-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaScanLaunchFrame
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.Alloc
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Allocation
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (dispatchWarp12 startupFacts)

private def beforeGroupBallotEvent : Op → Bool
  | .warp ⟨.shfl _, _, [some _], [_, _, _], some _⟩ => true
  | .mem a => a.kind == .load && !a.nc && a.ext == .same
  | .setMaxReg .. | .tcAlloc .. | .barSync .. | .barSyncN .. => true
  | _ => false

private theorem beforeGroupBallotCode :
    ((kernel.code.drop 1907).take (1982 - 1907)).all
      (fun i => i.op.isLocal || beforeGroupBallotEvent i.op) = true := by decide +kernel

private theorem barNotVote {l : Launch} {g pc : Nat} {s u : TState} {e : Event}
    {a : Opnd} {count : Option Opnd}
    (hf : Fires pc (barTmpl l g s a count .sync) e (some u)) : isFullWarpVote e = false := by
  unfold barTmpl at hf
  repeat' split at hf
  all_goals simp only [Fires] at hf
  all_goals first
    | exact False.elim (Option.some_ne_none _ hf.2)
    | (rw [hf.1]; rfl)

private theorem allocNotVote {l : Launch} {g pc base : Nat} {s u : TState} {e : Event}
    {group : CtaGroup} {off : Int} {nc : Opnd}
    (hf : Fires pc (eventTmpl Assumptions.all l g s (.tcAlloc group base off nc)) e (some u)) :
    isFullWarpVote e = false := by
  by_cases hSub : s.sub = 0
  · obtain ⟨d, n, rfl, _⟩ := fires_tcAlloc hSub hf
    rfl
  · simp only [eventTmpl, tcTmpl] at hf
    simp only [bind, Except.bind, pure, Except.pure, hSub, ite_false] at hf
    repeat' split at hf
    all_goals simp [ofExec, Fires] at hf
    all_goals first
      | contradiction
      | (obtain ⟨_, _, rfl, _⟩ := hf; rfl)

private theorem eventBeforeGroupBallot {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : 1907 ≤ s.pc) (hHi : s.pc < 1982)
    (he : EStep kernel Assumptions.all l g s e (some u)) : isFullWarpVote e = false := by
  obtain ⟨i, hCode, hLocal, hf⟩ := estep_event_source he
  have hAt : ((kernel.code.drop 1907).take (1982 - 1907))[s.pc - 1907]? = some i := by
    rwa [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
  have hKind := List.all_eq_true.mp beforeGroupBallotCode i (List.mem_of_getElem? hAt)
  simp only [hLocal, Bool.false_or] at hKind
  generalize hOp : i.op = op at hKind hf
  clear hOp hCode hAt hLo hHi hLocal he i
  cases op <;> simp only [beforeGroupBallotEvent, Bool.false_eq_true] at hKind
  case mem a =>
    have hm : a.kind = .load ∧ a.nc = false ∧ a.ext = .same := by
      simpa [beforeGroupBallotEvent, and_assoc] using hKind
    obtain ⟨_, _, rfl, _⟩ := fires_load hm.1 hm.2.1 hf hm.2.2
    rfl
  case warp w =>
    cases w with
    | mk kind ty dsts srcs mask =>
      split at hKind <;> try contradiction
      rename_i hShape
      rw [hShape] at hf
      obtain ⟨_, _, _, _, _, rfl, _⟩ := fires_shfl (p := none) hf
      rfl
  case barSync barrier aligned =>
    exact barNotVote (a := barrier) (count := none) hf
  case barSyncN barrier count aligned =>
    exact barNotVote (a := barrier) (count := some count) hf
  case setMaxReg inc n =>
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split at hf
    · obtain ⟨_, rfl, _⟩ := hf
      rfl
    · cases hf.2
  case tcAlloc => exact allocNotVote hf

private def voteBoundary : Fin 2 → Nat
  | 0 => 1907
  | 1 => 1982

private theorem voteBoundaryAudit : ∀ k : Fin 2,
    let floor := voteBoundary k
    (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true ∧
      Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
        | some seg => decide (floor ≤ seg.stop)
        | none => false) = true := by decide +kernel

private theorem voteFloorReach {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (k : Fin 2) (hTrace : TraceReach kernel Assumptions.all l g s events u)
    (hFloor : voteBoundary k ≤ s.pc) : voteBoundary k ≤ u.pc := by
  have ha := voteBoundaryAudit k
  induction hTrace with
  | refl => exact hFloor
  | tau hs _ ih =>
    exact ih (Thread.eventTailStepOfAudit ha.1 ha.2 hFloor (.inl ⟨rfl, hs⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit ha.1 ha.2 hFloor (.inr ⟨_, rfl, he⟩))

private theorem ballotFreeScanReach {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (hTrace : TraceReach kernel Assumptions.all l g s events u)
    (hLo : 1907 ≤ s.pc) (hHi : u.pc < 1982) : events.countP isFullWarpVote = 0 := by
  have ha := voteBoundaryAudit 0
  induction hTrace with
  | refl => rfl
  | tau hs _ ih =>
    exact ih (Thread.eventTailStepOfAudit ha.1 ha.2 hLo (.inl ⟨rfl, hs⟩)) hHi
  | @event t v u tail e he hRest ih =>
    have ht : t.pc < 1982 := by
      by_contra! hAfter
      exact Nat.not_le_of_lt hHi (voteFloorReach 1 (.event he hRest) hAfter)
    have hNo := eventBeforeGroupBallot hLo ht he
    have hv := Thread.eventTailStepOfAudit ha.1 ha.2 hLo (.inr ⟨_, rfl, he⟩)
    simpa [List.countP_cons, hNo] using ih hv hHi

private theorem commonStartupBallotCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hLen : 5 ≤ (X.tr g).length)
    (hFence : X.get (g, 3) = some ⟨172, .fenceMbarInit⟩)
    (hBar : X.get (g, 4) = some ⟨173, .bar 0 none .sync⟩) :
    ((X.tr g).take 5).countP isFullWarpVote = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  have hBound := (List.getElem?_eq_some_iff.mp hi).1
  rw [List.length_take, Nat.min_eq_left hLen] at hBound
  rw [List.getElem?_take_of_lt hBound] at hi
  change X.get (g, i) = some e at hi
  interval_cases i
  · rw [firstSharedValue hp hX g hg hi]
    intro h
    cases h
  · rw [secondWarpValue hp hX g hg hi]
    intro h
    cases h
  · rw [thirdWarpValue hp hX g hg hi]
    intro h
    cases h
  · rw [Option.some.inj (hi.symm.trans hFence)]
    intro h
    cases h
  · rw [Option.some.inj (hi.symm.trans hBar)]
    intro h
    cases h

/-- The first-group broadcast in the actual MMA lane precedes every full-mask ballot in
that lane. Its trace prefix has the ballot instance count needed by the group selector. -/
theorem firstGroupBroadcastBallotCount {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {e : Event} {u : TState} (he : X.get (g, j) = some e) (hSite : e.pc = 1980)
    (hu : u.pc = 1981)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take (j + 1)) (some u)) :
    ((X.tr g).take (j + 1)).countP isFullWarpVote = 0 := by
  have hWarp : 0 < warpIndex l g := by rw [hw]; decide
  obtain ⟨_, _, hIndex, _, _, _, hFence, hBar⟩ :=
    nonzeroCommonPrefixOfDemand hp hX hg hWarp he (.inl (by rw [hSite]; decide))
  have hLength : j + 1 ≤ (X.tr g).length := len_of_get he
  have hLen : 5 ≤ (X.tr g).length := by omega
  obtain ⟨t, _, ht, _, hBefore, _⟩ := nonzeroCommonPrefix hp hX hg hWarp hLen
  have hRole : (1062, b32 12) ∈ nonzeroBarrierFacts p l g := by
    simp [nonzeroBarrierFacts, hw]
  have hAt : At t 174 (startupFacts p l) := ht.mono ⟨holds_mem ht.2.2.2.2 hRole,
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]),
    holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts, abiFacts]), trivial⟩
  obtain ⟨s, hs, hStart⟩ := dispatchWarp12 hp hg hAt
  let events := (X.tr g).take (j + 1)
  let rest := events.drop 5
  have hSplit := List.take_append_drop 5 events
  change events.take 5 ++ rest = events at hSplit
  simp only [events, List.take_take, Nat.min_eq_left (show 5 ≤ j + 1 by omega)] at hSplit
  have hReach := hBefore.after_returned_prefix (hSplit.symm ▸ hPrefix)
  have hRest : rest ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp only [rest, events, List.length_drop, List.length_take, Nat.min_eq_left hLength]
    omega
  have hScan := hReach.after_local_nonempty (run_rtg hs) hRest
  have hNo := ballotFreeScanReach hScan.returning_reach (by rw [hStart.1])
    (by rw [hu]; decide)
  change ((X.tr g).take (j + 1)).countP isFullWarpVote = 0
  rw [← hSplit, List.countP_append, commonStartupBallotCount hp hX hg hLen hFence hBar, hNo]

end PTX.Kernels.TmlFa4Fwd.Thread.Allocation
