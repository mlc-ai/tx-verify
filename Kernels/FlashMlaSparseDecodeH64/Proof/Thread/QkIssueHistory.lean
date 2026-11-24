-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GemmReuseEndpoints
import Lemmas.Flow.Final

public section

/-! # The sixteen QK issues tracked by a commit and their actual operands -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QkIssueHistory

open PTX PTX.Flow

private def phase : Wg1Mma.Site → Option Nat
  | .qkMma k => some k.val
  | .qkCommit => some 16
  | _ => none

variable {P : Params} {L : Launch}

set_option maxHeartbeats 1200000 in
private theorem role_predecessor {g n : Nat} {q d : Wg1Mma.D} {e : Event}
    (hn : Wg1Mma.next P L g q e = some (some d)) (hd : phase d.site = some (n + 1))
    : phase q.site = some n ∧ q.i = d.i := by
  cases hq : q.site <;> simp only [Wg1Mma.next, hq, Wg1Mma.nextSite] at hn
  case qkMma k =>
    have hk := k.isLt
    split at hn <;> cases hn
    all_goals simp only [phase, Option.some.injEq] at hd ⊢
    all_goals exact ⟨by omega, trivial⟩
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp only [hq, Wg1Mma.startSite, Wg1Mma.afterTopk] at hd
  all_goals try split_ifs at hd
  all_goals simp [phase] at hd

private theorem machine_predecessor {g n : Nat} {s : Machine.ThreadD} {d : Wg1Mma.D} {e : Event}
    (hn : Machine.next P L g s e = some (some (.mma d))) (hd : phase d.site = some (n + 1)) :
    ∃ q, s = .mma q ∧ phase q.site = some n ∧ q.i = d.i := by
  cases s
  case mma q =>
    simp only [Machine.next] at hn
    split at hn
    · rename_i q' hnext
      cases hn
      exact ⟨q, rfl, role_predecessor hnext hd⟩
    · split at hn <;> cases hn
    · split at hn <;> cases hn
  case head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn
    all_goals cases hn
    simp [phase] at hd
  case prologue st =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
        · cases hn
      · cases hn
    · cases hn
  all_goals
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

private theorem prior_phase {X : Execution} {g j n : Nat} {k : Fin 16} {d : Wg1Mma.D}
    (hbound : j ≤ (X.tr g).length)
    (hs : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)))
    (hphase : phase d.site = some (k.val + n)) :
    ∃ i q, i + n = j ∧ q.site = .qkMma k ∧ q.i = d.i ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) := by
  induction n generalizing j d with
  | zero =>
    have hsite : d.site = .qkMma k := by
      cases hd : d.site <;> simp [phase, hd] at hphase
      · exact congrArg Wg1Mma.Site.qkMma (Fin.ext hphase)
      · have := k.isLt
        omega
    exact ⟨j, d, rfl, hsite, rfl, hs⟩
  | succ n ih =>
    cases j with
    | zero => rw [Frame.stateAt_zero] at hs; cases hs
    | succ j =>
      have hj : j < (X.tr g).length := by omega
      have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hj
      rw [Frame.stateAt_succ (C := Machine.code P L) he] at hs
      cases hp : Frame.stateAt (Machine.code P L) X g j with
      | none => simp [hp] at hs
      | some σ =>
        cases σ with
        | none => simp [hp] at hs; cases hs
        | some s =>
          rw [hp, Option.bind_some] at hs
          obtain ⟨q, rfl, hq, hb⟩ := machine_predecessor hs hphase
          obtain ⟨i, t, hi, ht, hiBlock, hstate⟩ := ih hj.le hp hq
          exact ⟨i, t, by omega, ht, hiBlock.trans hb, hstate⟩

/-- The state for any of the sixteen QK issues before an actual commit of their block. -/
theorem qk_state_of_commit {X : Execution} {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d))) (hc : d.site = .qkCommit)
    (k : Fin 16) :
    ∃ i, i + (16 - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma k, d.i⟩)) := by
  have hk := k.isLt
  have hphase : phase d.site = some (k.val + (16 - k.val)) := by
    simp only [hc, phase, Option.some.injEq]
    omega
  obtain ⟨i, ⟨site, block⟩, hi, rfl, rfl, hstate⟩ :=
    prior_phase (PTX.len_of_get he).le hd hphase
  exact ⟨i, hi, hstate⟩

private theorem issue_of_earlier_state {mem0 : Mem0} {X : Execution} {g i j block : Nat}
    {k : Fin 16} {e : Event} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e) (hij : i < j)
    (hi : Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma k, block⟩))) :
    X.MmaIssue (g, i) Wg1Mma.tmemP (MmaDataTrace.qkOperands L g block k)
      (MmaDataTrace.qkAccum k) [0, 0, 0, 0] := by
  have hj := PTX.len_of_get he
  change j < (X.tr g).length at hj
  have hiLen : i < (X.tr g).length := by omega
  let ev := (X.tr g)[i]
  have hget : X.get (g, i) = some ev := List.getElem?_eq_getElem hiLen
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, ins, u, ha, _, hcode, hf⟩ := Frame.fired_site hs hX hget hi
  cases u with
  | none =>
    obtain ⟨_, hrun⟩ := hX.thr g hg
    have := PTX.Flow.Run.end_last hrun hget (fires_none_ends hf)
    omega
  | some u =>
    have hk := (MmaDataTrace.fires_qkMma hpre hg block k ha hcode hf).1
    obtain ⟨site, kind⟩ := ev
    change kind = _ at hk
    exact ⟨site, by rw [hget, hk]⟩

/-- An actual QK issue fixes every earlier issue of the same block by index. -/
theorem qk_issue_before {mem0 : Mem0} {X : Execution} {g j block : Nat} {e : Event} {last : Fin 16}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma ⟨.qkMma last, block⟩)))
    (k : Fin 16) (hk : k.val < last.val) :
    ∃ i, i + (last.val - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma k, block⟩)) ∧
      X.MmaIssue (g, i) Wg1Mma.tmemP (MmaDataTrace.qkOperands L g block k)
        (MmaDataTrace.qkAccum k) [0, 0, 0, 0] := by
  have hPhase : phase (.qkMma last) = some (k.val + (last.val - k.val)) := by
    simp only [phase, Option.some.injEq]
    omega
  obtain ⟨i, ⟨site, block'⟩, hi, hSite, hBlock, hState⟩ :=
    prior_phase (PTX.len_of_get he).le hd hPhase
  change site = _ at hSite
  change block' = block at hBlock
  subst site block'
  exact ⟨i, hi, hState, issue_of_earlier_state hpre hX hs he (by omega) hState⟩

/-- The indexed QK event before an actual commit issued that block's matching operands. -/
theorem qk_issue_of_commit {mem0 : Mem0} {X : Execution} {g j : Nat} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (he : X.get (g, j) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.mma d))) (hc : d.site = .qkCommit)
    (k : Fin 16) :
    ∃ i, i + (16 - k.val) = j ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma ⟨.qkMma k, d.i⟩)) ∧
      X.MmaIssue (g, i) Wg1Mma.tmemP (MmaDataTrace.qkOperands L g d.i k)
        (MmaDataTrace.qkAccum k) [0, 0, 0, 0] := by
  obtain ⟨i, hi, hState⟩ := qk_state_of_commit he hd hc k
  have := k.isLt
  exact ⟨i, hi, hState, issue_of_earlier_state hpre hX hs he (by omega) hState⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.QkIssueHistory
