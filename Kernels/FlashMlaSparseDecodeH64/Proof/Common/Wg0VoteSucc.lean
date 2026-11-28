-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0Seg

@[expose] public section

/-! # The vote of warpgroup 0 is reached only from the row-maximum load

`succ_vote`: a step of the control machine lands on the vote site only from the load of the row
maxima (`mld`). Its event is a load, so a lane at the vote has not waited for a record. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

theorem getD_notVote (l : List Site) (d : Site) (k : Nat) (hl : ∀ s ∈ l, s ≠ .vote)
    (hd : d ≠ .vote) : l.getD k d ≠ .vote := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => simpa using hd
  | some s => simpa using hl s (List.mem_of_getElem? hk)

theorem nextChunk_notVote (c : Fin 4) (d : D) : (nextChunk c d).site ≠ .vote := by
  fin_cases c <;> simp [nextChunk]

/-- **Only the load of the row maxima leads to the vote.** -/
theorem succ_vote {d d' : D} {e : Event} (hb : scmp .ge .s (r2W L g) (pw P.b) = false)
    (h : succ P L g w d e = some (some d')) (ho : d'.site = .vote) : d.site = .mld := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [succ] at h
  all_goals try (obtain rfl := dataRd_eq h)
  all_goals try (obtain rfl | rfl := poll_eq h)
  all_goals try (obtain rfl := tcLoad_eq h)
  all_goals try (obtain ⟨x, rfl⟩ := ncWord_eq h)
  all_goals try (simp only [Option.some.injEq] at h; subst h)
  all_goals simp only [afterSmr, afterSink, afterA, loopEntry, finish, afterObar, nextChunk,
    afterEld, elemNext, afterOst, hb, Bool.false_eq_true, ite_false] at ho ⊢
  all_goals try (simp at ho ⊢; done)
  all_goals try (split_ifs at ho <;> simp at ho; done)
  all_goals try (split_ifs at ho <;> dsimp only at ho <;>
      exact absurd ho (getD_notVote _ _ _ (by simp) (by simp)))
  case sld =>
    rename_i arm k
    revert h
    fin_cases k <;> intro h <;> simp only at h <;> (obtain rfl := tcLoad_eq h) <;>
      simp at ho
  case pst =>
    exact absurd ho (getD_notVote _ _ _ (by simp) (by simp))
  case pld =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> (try dsimp only at ho) <;>
      first
      | exact absurd ho (getD_notVote _ _ _ (by simp) (by simp))
      | simp at ho
  case vote =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp at ho
  case rstw =>
    exact absurd ho (getD_notVote _ _ _ (by simp) (by simp))
  case arrS =>
    simp only [advance] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp at ho
  case oel =>
    obtain ⟨pc, kd⟩ := e
    cases kd <;> simp only [reduceCtorEq] at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
      first
      | exact absurd ho (nextChunk_notVote _ _)
      | simp at ho
  case otma =>
    exact absurd ho (getD_notVote _ _ _ (by simp) (by simp))
  case exit => cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
