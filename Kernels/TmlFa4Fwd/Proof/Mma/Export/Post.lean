-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Machine
public import Kernels.TmlFa4Fwd.Proof.Mma.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Mma.Places
import Kernels.TmlFa4Fwd.Proof.Mma.Warp

@[expose] public section

/-! # After its last commit of a stage, the MMA lane issues nothing more

The sites after commit `cm (10 + st)` (`postSite st`: for stage 0 `ce 11` and `cm 11`, then the
late scheduler pass, the relinquish, `bar2`, the deallocation, the exit) are closed under the
role's `succ` (`post_next`), so every later state of the lane is such a state (`post_states`):
no MMA is issued and no commit of stage `st` is made after it (`after_commit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The sites after the last commit of stage `st`. -/
def postSite (st : Fin 2) : Mma.Site → Bool
  | .ce c | .cm c => st.val == 0 && c.val == 11
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .relinq l | .bar2 l | .dealloc l | .exit l => l
  | _ => false
theorem scanExit_post {st : Fin 2} {d : Mma.D} {gx cur : BitVec 64} :
    postSite st (Mma.scanExit p true d gx cur).site = true := by
  unfold Mma.scanExit; split <;> rfl

theorem loopHead_post {st : Fin 2} {d : Mma.D}
    {grp acc : BitVec 64} : postSite st (Mma.loopHead p L g true d grp acc).site = true := by
  unfold Mma.loopHead
  split
  · exact scanExit_post
  · split <;> rfl

theorem afterTotal_post {st : Fin 2} {k : Epilogue.Scan}
    (hk : k.late = true) {d : Mma.D} {x : BitVec 64} :
    postSite st (Mma.afterTotal p L g k d x).site = true := by
  cases k <;> simp only [Epilogue.Scan.late, Bool.false_eq_true] at hk <;> unfold Mma.afterTotal <;>
    dsimp only <;> split <;> first | exact scanExit_post | exact loopHead_post

theorem ceNext11_post {st : Fin 2} {d : Mma.D} :
    postSite st (Mma.ceNext p L g d 11).site = true := by
  simp only [Mma.ceNext, Mma.passStart]
  split <;> (repeat' split) <;> simp_all [postSite, Epilogue.Scan.late, Mma.scAt]

set_option maxHeartbeats 16000000 in
/-- The successor of a state after the last commit of stage `st` is after it. -/
theorem post_next {st : Fin 2} {d d' : Mma.D} {e : Event}
    (hp : postSite st d.site = true ∨ d.site = .cm ⟨10 + st.val, by omega⟩)
    (hn : Mma.succ p L g d e = some (some d')) : postSite st d'.site = true := by
  obtain ⟨s, v⟩ := d
  rcases hp with hp | hp
  · cases s <;> simp only [postSite, Bool.false_eq_true] at hp
    all_goals (try (rename_i k; cases k <;>
      simp only [Epilogue.Scan.late, Bool.false_eq_true] at hp))
    all_goals (try subst hp)
    all_goals simp only [Mma.succ, Mma.word32, Mma.afterTiles, Mma.passStart, Option.map] at hn
    all_goals (repeat' split at hn)
    all_goals first
      | (cases hn; done)
      | (cases hn; simp_all [postSite, Epilogue.Scan.late, Mma.afterTotal, Mma.scanExit,
          Mma.loopHead, Mma.ceNext]; done)
      | (cases hn; (repeat' split) <;> simp_all [postSite, Epilogue.Scan.late]; done)
      | (cases hn; exact afterTotal_post rfl)
      | (simp only [Bool.and_eq_true, beq_iff_eq] at hp
         obtain ⟨-, hv⟩ := hp
         subst hv
         cases hn
         exact ceNext11_post)
      | skip
  · simp only at hp
    subst hp
    simp only [Mma.succ] at hn
    cases hn
    fin_cases st
    · simp [Mma.ceNext, postSite]
    · exact ceNext11_post

/-- **Every state after the last commit of stage `st` is after it.** -/
theorem post_states {c : Nat} {st : Fin 2} {d0 : Mma.D} {n0 : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g c = some (some (Mma.minj p L g d0 n0)))
    (hs : d0.site = .cm ⟨10 + st.val, by omega⟩) :
    ∀ q, c < q → q ≤ (X.tr g).length → ∀ σ,
      Frame.stateAt (thread p L) X g q = some (some σ) →
      ∃ d n, σ = Mma.minj p L g d n ∧ postSite st d.site = true := by
  intro q
  induction q with
  | zero => intro h; omega
  | succ q ih =>
    intro hq hql σ' h'
    have heq : (X.tr g)[q]? = some ((X.tr g)[q]'(by omega)) := List.getElem?_eq_getElem _
    rw [Frame.stateAt_succ heq] at h'
    rcases hs' : Frame.stateAt (thread p L) X g q with _ | _ | σ
    · rw [hs'] at h'; cases h'
    · rw [hs'] at h'; cases h'
    rw [hs'] at h'
    obtain ⟨d, n, rfl, hpd⟩ : ∃ d n, σ = Mma.minj p L g d n ∧
        (postSite st d.site = true ∨ d.site = .cm ⟨10 + st.val, by omega⟩) := by
      rcases Nat.lt_or_ge c q with hcq | hcq
      · obtain ⟨d, n, h1, h2⟩ := ih hcq (by omega) σ hs'
        exact ⟨d, n, h1, .inl h2⟩
      · have : c = q := by omega
        subst this
        rw [hσ] at hs'
        cases hs'
        exact ⟨d0, n0, rfl, .inr hs⟩
    have hn : (thread p L g).next (Mma.minj p L g d n) ((X.tr g)[q]'(by omega)) =
        some (some σ') := h'
    rw [Mma.next_minj] at hn
    obtain ⟨o, ho1, ho⟩ := Option.map_eq_some_iff.mp hn
    cases o with
    | none => cases ho
    | some d' =>
      simp only [Option.map_some, Option.some.injEq] at ho
      exact ⟨d', _, ho.symm, post_next hpd ho1⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
