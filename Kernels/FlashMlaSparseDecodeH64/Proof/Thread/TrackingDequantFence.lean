-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxLoopControl
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRawActualArrival
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Proxy fences precede actual raw-slot releases -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.EventFrame PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private theorem run_adjacent_events {t : TState} {es : List Event} {o : Option TState}
    {i : Nat} {e : Event}
    (hRun : Run kernel Assumptions.all L g t es o) (he : es[i + 1]? = some e) :
    ∃ previous s u v, es[i]? = some previous ∧
      EStep kernel Assumptions.all L g s previous (some u) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) u v ∧ v.pc = e.pc := by
  induction i generalizing t es with
  | zero =>
    cases hRun with
    | nil => cases he
    | last => cases he
    | @step _ s u first tail out _ hStep hRest =>
      change tail[0]? = some e at he
      cases hRest with
      | nil => cases he
      | step hLocal hChosen _ =>
        obtain rfl : _ = e := Option.some.inj he
        exact ⟨first, s, u, _, rfl, hStep, hLocal, (estep_source_pc hChosen).symm⟩
      | last hLocal hChosen =>
        obtain rfl : _ = e := Option.some.inj he
        exact ⟨first, s, u, _, rfl, hStep, hLocal, (estep_source_pc hChosen).symm⟩
  | succ i ih =>
    cases hRun with
    | nil => cases he
    | last => cases he
    | @step _ _ u _ tail _ _ _ hRest =>
      change tail[i + 1]? = some e at he
      exact ih hRest he

private theorem two_positions_before_barrier {t u : TState} {target : Nat} {ins : Instr}
    (hTarget : 2 ≤ target) (hBefore : kernel.code[target - 2]? = some ins)
    (hLocal : ins.op.isLocal = false) (hGuard : ins.guard = none)
    (hTargetEdge : kernel.branchTarget target = false)
    (hPrevEdge : kernel.branchTarget (target - 1) = false)
    (hEnd : u.pc = target)
    (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    t.pc = target ∨ t.pc = target - 1 := by
  cases hPath with
  | refl => exact .inl hEnd
  | @tail v z hPrior hStep =>
    have hNext := tau_step_before_non_target hStep (hEnd ▸ hTargetEdge)
    have hv : v.pc = target - 1 := by omega
    cases hPrior with
    | refl => exact .inr hv
    | @tail prev last hPrefix hLast =>
      have hNext' := tau_step_before_non_target hLast (hv ▸ hPrevEdge)
      have hp : prev.pc = target - 2 := by omega
      have hStop : Stops kernel Assumptions.all L g prev := by
        cases hf : prev.fault with
        | none =>
          exact ⟨_, out_event hf (hp ▸ hBefore) (by rw [hGuard]; rfl) hLocal⟩
        | some f => exact ⟨.ub f, by simp [out, hf]⟩
      exact (not_tau_of_stops hStop hLast).elim

private theorem previous_unit_arrival_event {target : Nat} {e : Event} {i base : Nat}
    {earlier middle : Instr}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, i) = some e)
    (hTag : e.pc = target) (hTarget : 2 ≤ target)
    (hCode : kernel.code[target]? = some
      ⟨none, .mbarArrive base 0 (.imm 0) (.imm 1) false true .cta none⟩)
    (hBefore : kernel.code[target - 2]? = some earlier)
    (hLocal : earlier.op.isLocal = false) (hGuard : earlier.guard = none)
    (hMiddle : kernel.code[target - 1]?  = some middle) (hMiddleLocal : middle.op.isLocal = true)
    (hTargetEdge : kernel.branchTarget target = false)
    (hPrevEdge : kernel.branchTarget (target - 1) = false) :
    ∃ j f, j + 1 = i ∧ X.get (g, j) = some f ∧ f.pc = target - 2 := by
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  have before {t u : TState} (hPc : u.pc = target)
      (hLocalPath : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
      t.pc = target ∨ t.pc = target - 1 :=
    two_positions_before_barrier hTarget hBefore hLocal hGuard hTargetEdge hPrevEdge hPc hLocalPath
  cases i with
  | zero =>
    have failAtFirst {u : TState} {v : Option TState}
        (hLocalPath : Relation.ReflTransGen (Tau kernel Assumptions.all L g) {} u)
        (hStep : EStep kernel Assumptions.all L g u e v) : False := by
      have hp := before ((estep_source_pc hStep).symm.trans hTag) hLocalPath
      change 0 = target ∨ 0 = target - 1 at hp
      omega
    have hGet : (X.tr g)[0]? = some e := he
    generalize hList : X.tr g = events at hRun
    rw [hList] at hGet
    cases hRun with
    | nil => cases hGet
    | step hTau hf _ =>
      obtain rfl : _ = e := Option.some.inj hGet
      exact (failAtFirst hTau hf).elim
    | last hTau hf =>
      obtain rfl : _ = e := Option.some.inj hGet
      exact (failAtFirst hTau hf).elim
  | succ j =>
    obtain ⟨f, s, u, v, hf, hStep, hLocalPath, hPc⟩ := run_adjacent_events hRun he
    have hp := before (hPc.trans hTag) hLocalPath
    have hSource := estep_source_pc hStep
    have hRet := (estep_return_pc hStep (fun _ _ _ h => local_frame h)).2
    have hPoss : s.pc = target ∨ s.pc = target - 1 ∨ s.pc = target - 2 := by omega
    rcases hPoss with h | h | h
    · obtain ⟨rfl, _⟩ := softmax_unit_arrival_return (h ▸ hCode) hStep
      change s.pc + 1 = target ∨ s.pc + 1 = target - 1 at hp
      omega
    · obtain ⟨ins, hIns, hNot, _⟩ := estep_event_source hStep
      rw [h, hMiddle] at hIns
      obtain rfl := Option.some.inj hIns
      rw [hMiddleLocal] at hNot
      cases hNot
    · exact ⟨j, f, rfl, hf, hSource.trans h⟩

/-- The last two events before any actual return to the raw producer are the proxy fence
and the dequantized-tile publication. -/
private theorem actual_fence_before_raw_return {i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, i) = some e)
    (hTag : e.pc = 3599) :
    ∃ j ready fence, j + 2 = i ∧ X.get (g, j + 1) = some ready ∧ ready.pc = 3597 ∧
      X.get (g, j) = some fence ∧ fence.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨k, ready, hk, hr, hReady⟩ := previous_unit_arrival_event hX he hTag (by decide)
    Flow.code_3599 Flow.code_3597 rfl rfl Flow.code_3598 rfl (by decide +kernel) (by decide +kernel)
  obtain ⟨j, fence, hj, hf, hFence⟩ := previous_unit_arrival_event hX hr hReady (by decide)
    Flow.code_3597 Flow.code_3595 rfl rfl Flow.code_3596 rfl (by decide +kernel) (by decide +kernel)
  refine ⟨j, ready, fence, by omega, hj ▸ hr, hReady, hf, ?_⟩
  have hNext : (X.tr g)[j + 1]? = some ready := hj ▸ hr
  obtain ⟨endState, hRun⟩ := hX.thr g (Frame.lt_of_get hX hf)
  obtain ⟨r, s, u, v, hGet, hStep, _, _⟩ := run_adjacent_events hRun hNext
  have hEq : r = fence := Option.some.inj (hGet.symm.trans hf)
  subst r
  obtain ⟨ins, hc, _, hFired⟩ := estep_event_source hStep
  have hPc := estep_source_pc hStep
  change fence.pc = 3595 at hFence
  rw [← hPc, hFence, Flow.code_3595] at hc
  obtain rfl := Option.some.inj hc
  exact congrArg Event.kind hFired.1

/-- The two events immediately preceding an actual raw release are the shared proxy fence
and a publication that cannot itself access ordinary memory. -/
theorem actual_raw_release_fence {i cta tx count : Nat} {e : Event}
    {slot : Fin 2} {scope : MbarScope} {rel : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hk : e.kind = .arrive (Protocol.RawRing.free L cta slot) tx count rel scope) :
    ∃ j mid fence, j + 2 = i ∧ X.get (g, j + 1) = some mid ∧ mid.acc = none ∧
      X.get (g, j) = some fence ∧ fence.kind = .fenceProxy (.async (some (.shared .cta))) none := by
  obtain ⟨_, _, _, _, _, _, hTag⟩ := actual_raw_free_arrive hpre hX hs he hk
  obtain ⟨j, mid, fence, hi, hm, hMid, hf, hKind⟩ := actual_fence_before_raw_return hX he hTag
  refine ⟨j, mid, fence, hi, hm, ?_, hf, hKind⟩
  have hAfter : (X.tr g)[(j + 1) + 1]? = some e := by rwa [show j + 1 + 1 = i by omega]
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  obtain ⟨r, t, u, v, hGet, hStep, _, _⟩ := run_adjacent_events hRun hAfter
  have hEq : r = mid := Option.some.inj (hGet.symm.trans hm)
  subst r
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source hStep
  have hPc := estep_source_pc hStep
  rw [← hPc, hMid, Flow.code_3597] at hc
  obtain rfl := Option.some.inj hc
  cases hAddr : mbarLoc L g t 2783 0 with
  | error f =>
    have hBad : Fires t.pc (.ub f) mid (some u) := by
      simpa only [eventTmpl, tmaTmpl, hAddr, widenMbarScope,
        show Assumptions.all.any (·.clusterScopeMbar t.pc) = false from rfl,
        Bool.false_eq_true, ↓reduceIte, bind, Except.bind, ofExec] using hFire
    cases hBad.2
  | ok m =>
    have hReady := RingEvents.fired_unit_arrive hAddr hFire
    obtain ⟨tag, kind⟩ := mid
    change kind = _ at hReady
    subst kind
    rfl

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
