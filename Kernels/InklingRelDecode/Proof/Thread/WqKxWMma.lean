-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WqKxWSync

@[expose] public section

/-!
# The key time of the MMA warp at synchronizing steps

`kstep_M`, site by site (`MStep`): two lanes' MMA states at one synchronizing site with one key
time (so one loop counter in the loop), whose counters at `bar0` are equal and which agree on the
successor of `bar0`, `qkElect` and `pvElect` (`WAgree`), have successors of one key time.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- The step of two lanes' MMA states at the site `s`. -/
def MStep (s : Mma.Site) : Prop :=
  ∀ {L : Launch} {g h : Nat} {e e' : Event} {i n tm : Nat} {pro : Nat → Value}
    {i' n' tm' : Nat} {pro' : Nat → Value} {t t' : Mma.D},
    kxM ⟨s, i, n, tm, pro⟩ = kxM ⟨s, i', n', tm', pro'⟩ → (s = .bar0 → i = i') →
    ((s = .bar0 → (Mma.start ⟨s, i, n, tm, pro⟩).site = (Mma.start ⟨s, i', n', tm', pro'⟩).site) ∧
      (s = .qkElect →
        (Mma.afterQk ⟨s, i, n, tm, pro⟩).site = (Mma.afterQk ⟨s, i', n', tm', pro'⟩).site) ∧
      (s = .pvElect →
        (Mma.iterNext ⟨s, i, n, tm, pro⟩).site = (Mma.iterNext ⟨s, i', n', tm', pro'⟩).site)) →
    Mma.next L g ⟨s, i, n, tm, pro⟩ e = some (some t) →
    Mma.next L h ⟨s, i', n', tm', pro'⟩ e' = some (some t') → kxM t = kxM t'

/-- The proof of `MStep` at one site. -/
macro "mstep_tac" : tactic => `(tactic| (
  intro L g h e e' i n tm pro i' n' tm' pro' t t' hx hb ha hn hn'
  (try simp only [start_site, afterQk_site, iterNext_site, forall_const, reduceCtorEq,
    false_implies, and_true, true_and, true_implies] at ha hb)
  (try simp only [kxM, mmaT, Bound.Mma.pos] at hx)
  (try (have hi : i = i' := hb; subst hi))
  (try (have hi : i = i' := by wt_omega
        subst hi))
  simp only [Mma.next] at hn hn'
  (repeat' split at hn)
  all_goals (repeat' split at hn')
  all_goals
    first
    | (simp only [reduceCtorEq, Option.some.injEq] at hn; done)
    | (simp only [reduceCtorEq, Option.some.injEq] at hn'; done)
    | (simp only [Option.some.injEq] at hn hn'
       subst hn hn'
       first
       | rfl
       | ((try simp only [kxM_afterQk, kxM_iterNext, kxM_start])
          (try simp only [kxM])
          (try simp only [mmaT_afterQk, mmaT_iterNext, mmaT_start])
          (try simp only [mmaT, Bound.Mma.pos])
          (try split_ifs at ha ⊢) <;> first | rfl | (simp_all; done) | wt_omega))))

theorem mstep_setMaxReg : MStep .setMaxReg := by mstep_tac
theorem mstep_bar0 : MStep .bar0 := by mstep_tac
theorem mstep_qkBar : MStep .qkBar := by mstep_tac
theorem mstep_qkShfl : MStep .qkShfl := by mstep_tac
theorem mstep_qkBar2 : MStep .qkBar2 := by mstep_tac
theorem mstep_qkElect : MStep .qkElect := by mstep_tac
theorem mstep_pvBar : MStep .pvBar := by mstep_tac
theorem mstep_pvShfl : MStep .pvShfl := by mstep_tac
theorem mstep_pvBar2 : MStep .pvBar2 := by mstep_tac
theorem mstep_pvElect : MStep .pvElect := by mstep_tac
theorem mstep_finBar : MStep .finBar := by mstep_tac
theorem mstep_finElect : MStep .finElect := by mstep_tac
theorem mstep_bar1 : MStep .bar1 := by mstep_tac

end
end PTX.Kernels.InklingRelDecode.Proof.Lk
