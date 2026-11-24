-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingArrival
public import Lemmas.Step.Released
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix

public section

/-! # Entry to a closing site leaves no outstanding blocking return -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingArrival

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem index_next_not_blocking {q d : Wg1Index.D} {e : Event}
    (hn : Wg1Index.next P L g q e = some (some d)) :
    e.kind.resume ≠ .blocking false := by
  intro hb
  cases hk : e.kind <;> simp only [hk, Kind.resume, reduceCtorEq,
    Resume.blocking.injEq, Bool.true_eq_false] at hb
  case' tc k => cases k <;> simp only [TcKind.resume, reduceCtorEq] at hb
  all_goals
    cases hs : q.site <;>
      simp only [Wg1Index.next, Wg1Index.nextSite, hs, hk, reduceCtorEq] at hn
  all_goals cases hn

/-- Entering any index state has already released the preceding event. -/
theorem index_released_of_tail {d : Wg1Index.D}
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.index d))) :
    PTX.Step.Released L X g := by
  apply PTX.Step.Released.of_get
  intro e he
  have hLen := PTX.len_of_get he
  have hTail : (X.tr g).length - 1 + 1 = (X.tr g).length := by
    change (X.tr g).length - 1 < (X.tr g).length at hLen
    omega
  obtain ⟨q, r, hq, hr, hn⟩ := FollowedPrefix.step_at hd hLen he
  rw [hTail, hd] at hr
  obtain rfl := Option.some.inj (Option.some.inj hr)
  change Machine.next P L g q e = some (some (.index d)) at hn
  cases q
  case index q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i d' hStep
      cases hn
      exact index_next_not_blocking hStep
    · split at hn <;> cases hn
    · cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp [Kind.resume]
  case prologue q =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i wg _
        split_ifs at hn
        · fin_cases wg <;> cases hn
        · cases hn
      · cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingArrival
