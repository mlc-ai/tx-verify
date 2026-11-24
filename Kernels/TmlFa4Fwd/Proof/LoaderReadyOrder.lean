-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReadyArrival

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

private theorem runOfLoaderLocals {l : Launch} {g : Nat} {s t : TState}
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) :
    ∃ n, run kernel Assumptions.all l g n s = some t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hStep ih =>
    obtain ⟨n, hn⟩ := ih
    have hOne := tauStep_iff.mpr hStep
    exact ⟨n + 1, run_comp hn (by simp only [run, hOne, Option.bind_some])⟩

private theorem sliceEventMem {l : Launch} {g lower stop : Nat} {t : TState}
    {events : List Event} {visits : List Visit} {e : Event}
    (hw : Walk kernel Assumptions.all l g t events visits)
    (he : e ∈ loaderSliceEvents lower stop visits) : e ∈ events := by
  rw [hw.events]
  obtain ⟨v, hv, hIssue⟩ := List.mem_filterMap.mp he
  exact List.mem_filterMap.mpr ⟨v, List.takeWhile_subset _ hv, hIssue⟩

/-- In a finite prefix containing a later event of this slice, the loader poll
must have completed. The first successful acquire is preceded only by retries. -/
theorem pollBeforeSliceEvent {l : Launch} {g addr phase lower stop : Nat}
    (site : DrainWaitSite) (hCode : LoaderWaitCode site)
    (hRange : 174 ≤ site.pc ∧ site.pc + 3 < 1906)
    (hLower : lower ≤ site.pc) (hUpper : site.pc < stop)
    {F : List (Nat × Value)} (hFresh : ∀ pair ∈ F, pair.1 ≠ site.result)
    (hTemplate : ∀ s, At s site.pc F → out kernel Assumptions.all l g s =
      .ev (.wait ⟨.shared, g / l.block, addr⟩ phase
        (fun ok => next (setReg s site.result (.pred ok))) true .cta))
    {t : TState} {events : List Event} {visits : List Visit} {e : Event}
    (ht : At t site.pc F) (hw : Walk kernel Assumptions.all l g t events visits)
    (hLater : site.pc < e.pc) (hSeen : e ∈ loaderSliceEvents lower stop visits) :
    let ev := fun ok => (⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩ : Event)
    ∃ n u rest tail, events = List.replicate n (ev false) ++ (ev true :: rest) ∧
      At u (site.pc + 3) F ∧ Walk kernel Assumptions.all l g u rest tail ∧
      e ∈ loaderSliceEvents lower stop tail := by
  dsimp only
  induction events generalizing t visits with
  | nil => exact (List.not_mem_nil (sliceEventMem hw hSeen)).elim
  | cons first rest ih =>
    have hOut := hTemplate t ht
    cases hw with
    | tau hTau _ =>
      rw [Tau, hOut] at hTau
      cases hTau
    | last hStep =>
      obtain ⟨tmpl, hTmpl, hFire⟩ := hStep
      rw [hOut] at hTmpl
      obtain rfl := Out.ev.inj hTmpl
      obtain ⟨_, _, hNone⟩ := hFire
      cases hNone
    | @ev _ _ _ _ vs hStep hw =>
      obtain ⟨tmpl, hTmpl, hFire⟩ := hStep
      rw [hOut] at hTmpl
      obtain rfl := Out.ev.inj hTmpl
      obtain ⟨ok, rfl, hNext⟩ := hFire
      obtain rfl := Option.some.inj hNext
      have hTail : e ∈ loaderSliceEvents lower stop vs := by
        simpa only [loaderSliceEvents, visit, List.takeWhile_cons, hLower, hUpper, ht.1,
          decide_true, Bool.true_and, ↓reduceIte, List.filterMap_cons, List.mem_cons,
          show e ≠ ⟨site.pc, .wait ⟨.shared, g / l.block, addr⟩ phase ok true .cta⟩ from
            fun he => by have := congrArg Event.pc he; simp at this; omega,
          false_or] using hSeen
      have hAt : At (next (setReg t site.result (.pred ok))) (site.pc + 1)
          ((site.result, .pred ok) :: F) := ht.set hFresh
      obtain ⟨u, hLocal, hU⟩ := loaderAfterWait site hCode hRange ok hAt
      obtain ⟨steps, hRun⟩ := runOfLoaderLocals hLocal
      obtain ⟨tail, hWalk, _, hEvent⟩ := loaderEventAfterLocal hRun hw hTail
      cases ok
      · obtain ⟨n, v, suffix, vs, hEq, hAt, hWalk', hSeen'⟩ := ih hU hWalk hEvent
        exact ⟨n + 1, v, suffix, vs, by simp [hEq, ht.1, List.replicate_succ],
          hAt, hWalk', hSeen'⟩
      · exact ⟨0, u, rest, tail, by simp [ht.1], hU, hWalk, hEvent⟩

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g phase : Nat} (i : Fin 4)
    (stage : Fin 3) (hPhase : phase < 2) {s : TState} {events : List Event} {visits : List Visit}
    {loc : Loc} (hAt : At s ((recurringEmptyWait i).pc - 3) (recurringBarrierInput l i stage phase))
    (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hSeen : ⟨copyCommitPc (recurringPacketSite i) + 1, .asyncArrive loc true⟩ ∈
      loaderSliceEvents ((recurringEmptyWait i).pc - 3)
        (copyCommitPc (recurringPacketSite i) + 2) visits)
include hp i stage hPhase hAt hWalk hSeen

/-- Cut the actual walk immediately after a successful recurring empty acquire. -/
theorem recurringReadyArrivalCut :
    let empty := Prologue.initObject l (g / l.block) (emptySlot stage)
    let ready := Prologue.initObject l (g / l.block) (readySlot stage)
    let poll := fun ok => (⟨(recurringEmptyWait i).pc, .wait empty phase ok true .cta⟩ : Event)
    ∃ n u rest later, events = List.replicate n (poll false) ++ (poll true :: rest) ∧ loc = ready ∧
      At u ((recurringEmptyWait i).pc + 3) (recurringBarrierFacts l i stage phase) ∧
      Walk kernel Assumptions.all l g u rest later ∧
      ⟨copyCommitPc (recurringPacketSite i) + 1, .asyncArrive ready true⟩ ∈ rest := by
  obtain ⟨t, hLocal, ht⟩ := recurringBarrierPrep hp (g := g) i stage phase s hAt
  obtain ⟨tail, hW, _, hIssue⟩ := loaderEventAfterLocal hLocal hWalk hSeen
  have hRange : 174 ≤ (recurringEmptyWait i).pc ∧
      (recurringEmptyWait i).pc + 3 < 1906 := by fin_cases i <;> decide
  have hAddr : l.sharedBase + 8 * stage.val + 56 < 2 ^ 32 := by
    have := hp.shared.2.1
    have := stage.isLt
    omega
  have hAlign : (l.sharedBase + 8 * stage.val + 56) % 8 = 0 := by
    have := hp.shared.1
    omega
  have hFresh : ∀ pair ∈ recurringBarrierFacts l i stage phase,
      pair.1 ≠ (recurringEmptyWait i).result := by
    fin_cases i <;> simp [recurringBarrierFacts, recurringEmptyWait, recurringPacketSite,
      copyArrivalAddress]
  have hUpper : (recurringEmptyWait i).pc < copyCommitPc (recurringPacketSite i) + 1 := by
    fin_cases i <;> decide
  obtain ⟨n, u, rest, later, hEvents, hu, hw, hRecord⟩ :=
    pollBeforeSliceEvent (recurringEmptyWait i) (recurringEmptyWaitCode i)
      (stop := copyCommitPc (recurringPacketSite i) + 2)
      hRange (Nat.sub_le ..) (by omega) hFresh
      (fun _ state => loaderWaitTemplate _ (recurringEmptyWaitCode i) hRange
        hAddr hAlign hPhase state.1 state.2.2.2.1 state.2.2.2.2.1 state.2.2.2.2.2.1)
      ht hW hUpper hIssue
  have hScope : (recurringEmptyWait i).pc - 3 ≤ (recurringEmptyWait i).pc + 3 := by omega
  have hLoc := recurringReadyArrivalInSlice hp i stage hScope hu hw hRecord
  exact ⟨n, u, rest, later, by simpa only [emptySlot_address] using hEvents, hLoc, hu, hw,
    hLoc ▸ sliceEventMem hw hRecord⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
