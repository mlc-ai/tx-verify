-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Clc.ClcExecution
public import Core.Source.Decode
public import Mathlib.Tactic.NormNum

namespace PTX.Tests.ClcExecution
noncomputable section

private def L : Launch := { grid := 4, block := 32, clusterSize := ⟨2, by decide⟩, params :=
                            fun _ => none }
private theorem L_oneDim : L.OneDim := by simp [Launch.OneDim, L]
private theorem validTask_zero : Clc.ValidTask L 0 := by
  rw [Clc.validTask_oneDim L_oneDim]
  decide
private theorem validTask_one : Clc.ValidTask L 1 := by
  rw [Clc.validTask_oneDim L_oneDim]
  decide
private def spec : Clc.Spec := ⟨⟨.shared, 0, 32⟩, ⟨.shared, 0, 64⟩, true⟩
private def issue : Event := ⟨0, .clcIssue spec [0, 1]⟩
private def response : ClcResponse := Clc.responseOf L (0, 0) (some 1)
private def fx : Clc.Effects := { resolved := some response, written := {0}, notified := {0} }
private def launched : Clc.State := { Clc.initial with
  owner := Function.update Clc.initial.owner 0 (some .launched) }
private def state : Clc.State := {
  owner := Function.update launched.owner 1 (some (.canceled (Clc.requestId (0, 0))))
  response := Function.update launched.response (Clc.requestId (0, 0)) (some (some 1))
}
private def X : Execution := {
  tr := fun g => if g = 0 then [issue] else [], rf := fun _ _ => none,
  clc := fun i => if i = (0, 0) then fx else {}, clcState := state
}
private def env : Decode.Env := { classes := [⟨"r".toList, 2, 32⟩], labels := [], params := [] }

example : Decode.op env
    "clusterlaunchcontrol.try_cancel.async.shared::cta.mbarrier::complete_tx::bytes.\
      multicast::cluster::all.b128"
    [.address [.register "r0"], .address [.register "r1"]] =
    .ok (.clcTryCancel true 0 0 1 0) := rfl

-- The source instruction emits an issue and targets; it does not emit a response write.
private def t : TState := { regs := fun
  | 0 => .some (.bits 32 32)
  | 1 => .some (.bits 32 64)
  | _ => none }
example : clcTmpl L 0 t (.clcTryCancel true 0 0 1 0) =
    .clcIssue spec [0, 1] (next t) := rfl

-- Actual generic memory reads can name this asynchronous response write as their source.
example : X.MemWrites (.async (0, 0) (.write (.cta 0))) { loc := ⟨.shared, 0, 32⟩, size := 16 }
    (Value.clc response).toBytes := by
  exact ⟨spec, [0, 1], ⟨0, rfl⟩, by simp, by simp [Clc.ResponseWrite, X, fx, spec]⟩

-- Even the still-pending peer write participates in access/race checks.
example : X.Intent (.async (0, 0) (.write (.cta 1))) { loc := ⟨.shared, 1, 32⟩, size := 16 } true :=
  ⟨rfl, spec, [0, 1], ⟨0, rfl⟩, by simp, rfl⟩
example : ¬ X.AsyncPresent (0, 0) (.write (.cta 1)) := by
  simp [Execution.AsyncPresent, X, fx]

-- Notifications resolve to the correct target object and exactly sixteen bytes.
example : AsyncCopy.objectAction X X.async ⟨.shared, 0, 64⟩
    (.async (0, 0) (.notify (.cta 0))) = some (.completeTx 16) := by
  simp [AsyncCopy.objectAction, Execution.get, X, issue, spec, fx]
example : AsyncCopy.objectAction X X.async ⟨.shared, 1, 64⟩
    (.async (0, 0) (.notify (.cta 0))) = none := by
  simp [AsyncCopy.objectAction, Execution.get, X, issue, spec, fx]
example : AsyncCopy.objectAction X X.async ⟨.shared, 1, 64⟩
    (.async (0, 0) (.notify (.cta 1))) = none := by
  simp [AsyncCopy.objectAction, Execution.get, X, issue, spec, fx]

-- This deliberately incomplete arbitration state cannot pass Consistent.clc.
example : ¬ ClcOk L { X with clcState := Clc.initial } := by
  intro h
  have hs := h.2.2.2.2 ⟨(0, 0), spec, [0, 1], 0, rfl⟩ 0 (by decide)
    (by simp [X])
  simp [Clc.initial] at hs

private theorem only_issue {i : EvId} {s : Clc.Spec} {ts : List Nat}
    (hi : X.ClcIssue i s ts) : i = (0, 0) ∧ s = spec ∧ ts = [0, 1] := by
  obtain ⟨pc, h⟩ := hi
  rcases i with ⟨g, k⟩
  by_cases hg : g = 0
  · subst g
    cases k with
    | zero => simp [Execution.get, X, issue] at h; exact ⟨rfl, h.2.1.symm, h.2.2.symm⟩
    | succ k => simp [Execution.get, X] at h
  · simp [Execution.get, X, hg] at h

-- Positive execution-level witness: cluster 0 launched, and its request canceled cluster 1.
private theorem clc_ok : ClcOk L X := by
  have ar : Clc.ArbitrationOk L state := by
    exact .tail (.single (.launch Clc.initial 0 validTask_zero rfl))
      (.success launched (Clc.requestId (0, 0)) 1 validTask_one rfl rfl)
  refine ⟨ar, ?_, ?_, ?_, ?_⟩
  · intro request answer hr
    by_cases he : request = Clc.requestId (0, 0)
    · exact ⟨(0, 0), spec, [0, 1], he, 0, rfl⟩
    · simp [X, state, launched, Clc.initial, Function.update, he] at hr
  · intro i hi
    by_cases he : i = (0, 0)
    · subst i; exact ⟨spec, [0, 1], 0, rfl⟩
    · simp [X, he] at hi
  · intro i s ts hi
    obtain ⟨rfl, rfl, rfl⟩ := only_issue hi
    refine ⟨⟨ar, ?_, ?_, ?_⟩, by decide, ?_⟩
    · intro r hr
      have he : r = response := by simpa [X, fx] using hr.symm
      subst r
      exact ⟨some 1, by simp [X, state], rfl⟩
    · intro c hc
      have he : c = 0 := by simpa [X, fx] using hc
      subst c
      exact ⟨by simp only [Clc.Target, L, spec]; decide, rfl⟩
    · intro c hc; exact hc
    · intro c
      have hcgv : L.clusterGridValid := by decide
      have hco : L.clusterOfCta c = c / 2 := by
        rw [Launch.oneDim_clusterOfCta L_oneDim]
        rfl
      have hco0 : L.clusterOfCta 0 = 0 := by
        rw [Launch.oneDim_clusterOfCta L_oneDim]
        rfl
      have hth : 0 < L.threads := by decide
      have hg : L.grid = 4 := rfl
      simp only [Clc.Target, spec, hcgv, hco, hco0, hth, hg, true_and, ite_true, Nat.zero_div,
        List.mem_cons, List.not_mem_nil, or_false]
      omega
  · intro _ g hg ht
    by_cases he : g = 0
    · subst g
      have hco : L.clusterOfCta 0 = 0 := by decide
      simp [X, state, launched, hco]
    · simp [X, he] at ht

example : ∃ a bs, X.MemWrites (.async (0, 0) (.write (.cta 0))) a bs :=
  clc_ok.notification_has_write (by simp [X, fx])

-- A canceled task must trace back to a real request even before all replicas finish.
example : ∃ i s targets, Clc.requestId (0, 0) = Clc.requestId i ∧
    X.ClcIssue i s targets ∧ X.clcState.response (Clc.requestId i) = some (some 1) :=
  clc_ok.canceled_has_issue (task := 1) (by simp [X, state])

-- A request names the response mbarrier of each target CTA (`UsesMbar`), so an unallocated target
-- mbarrier is an unallocated access (ERR-UNALLOCATED-ACCESS), not a CLC-specific check.
example : Unalloc (fun _ => none) X := by
  have hm : X.UsesMbar (0, 0) ⟨.shared, 0, 64⟩ :=
    Execution.UsesMbar.of_clc (X := X) (e := (0, 0)) (s := spec) (targets := [0, 1]) (c := 0)
      ⟨0, rfl⟩ (by decide)
  refine Or.inr ⟨(0, 0), ⟨.shared, 0, 64⟩, ⟨.shared, 0, 64⟩, hm, ?_, rfl⟩
  simp only [Acc.Covers, Loc.InRange]
  decide

end
end PTX.Tests.ClcExecution
