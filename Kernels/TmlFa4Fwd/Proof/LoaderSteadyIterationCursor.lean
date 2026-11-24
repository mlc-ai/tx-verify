-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRingPrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
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
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem steadyCounterWithFrame {l : Launch} {g iteration bound : Nat}
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < bound)
    {t : TState} {F : List (Nat × Value)}
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (ht : At t 1741 ([(7181, b32 iteration), (1091, b32 bound)] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 3 t = some u ∧
      At u (if iteration + 1 < bound then 1396 else 1744)
        ([(7181, b32 (iteration + 1)), (1091, b32 bound)] ++ F) := by
  obtain ⟨v, hv, hV⟩ := steadyRingCondition l g hTrip hIteration t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩)
  have hKeep : ((kernel.code.drop 1741).take 2).all
      (fun i => (1091 :: F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hi
    have hBound : ((kernel.code.drop 1741).take 2).all
        (fun i => !(writesRegs i.op).contains 1091) = true := by kernel_rfl
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hBound _ hi, List.all_eq_true.mp hTail _ hi⟩
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := 1091 :: F.map Prod.fst)
    (by decide) (by decide) ht.1 hKeep (by kernel_rfl) hv
  have hF := holdsSchedulerFrame ht.2.2.2.2.2.2 hvFrame
    (fun r hm => .tail 1091 (List.mem_map_of_mem hm))
  let takeBranch := decide (iteration + 1 < bound)
  have hAt : At v 1743 ((230, .pred takeBranch) ::
      [(7181, b32 (iteration + 1)), (1091, b32 bound)] ++ F) :=
    hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1,
      (hvFrame 1091 (by simp)).trans ht.2.2.2.2.2.1, hF⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1743 takeBranch hAt hAt.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu
  exact ⟨u, run_comp hvA huA, by simpa [takeBranch] using hU.mono hU.2.2.2.2.2⟩

set_option maxRecDepth 100000 in
/-- More than one steady round's shuffles in a prefix force the actual continuation
through the observed round's counter branch. The immutable frame survives. -/
theorem steadyObservedAdvance {l : Launch} {X : Execution} {g index iteration bound : Nat}
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < bound)
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hBody : ∀ n, ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1396 ([(7181, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hSafe : ∀ f, e.kind ≠ .ub f)
    (hLater : 1741 ≤ e.pc ∨ ((X.tr g).take index).countP Execution.isShfl + 64 <
      ((X.tr g).take j).countP Execution.isShfl) :
    ∃ pos ≤ j, ∃ u stop,
      At u (if iteration + 1 < bound then 1396 else 1744)
        ([(7181, b32 (iteration + 1)), (1091, b32 bound)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 64 := by
  have hWitness : ∃ k marker, k ≤ j ∧ X.get (g, k) = some marker ∧ index ≤ k ∧
      (1741 ≤ marker.pc ∨ (Execution.isShfl marker = true ∧
        ((X.tr g).take index).countP Execution.isShfl + 64 ≤
          ((X.tr g).take k).countP Execution.isShfl)) ∧ ∀ f, marker.kind ≠ .ub f := by
    rcases hLater with hPc | hCount
    · exact ⟨j, e, le_rfl, he, hBefore, .inl hPc, hSafe⟩
    obtain ⟨k, marker, hk, hMark, hShuffle, hNth⟩ := exists_nthEv (g := g)
      (p := Execution.isShfl) (Nat.succ_le_of_lt hCount)
    have hkFrom : index ≤ k := by
      by_contra! h
      have hMono := countP_take_mono Execution.isShfl (X.tr g) h.le
      rw [hNth] at hMono
      omega
    refine ⟨k, marker, hk.le, hMark, hkFrom, .inr ⟨hShuffle, hNth.ge⟩, ?_⟩
    intro f h
    obtain ⟨pc, kind⟩ := marker
    change kind = .ub f at h
    subst kind
    cases hShuffle
  obtain ⟨k, marker, hk, hMark, hkFrom, hDemand, hClean⟩ := hWitness
  have hCounted : (((kernel.code.drop 1396).take (1741 - 1396)).zipIdx 1396).all
      (fun (ins, pc) => LoaderRankedInstr 1741 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1741 1396 = 64 := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hBody hCounted hs hr hMark hkFrom
      (by rw [hCount]; exact hDemand) hClean
  obtain ⟨u, hu, huAt⟩ := steadyCounterWithFrame (l := l) (g := g)
    hTrip hIteration hTail ht
  let pos := index + front.length
  have hPos : pos ≤ j := htBefore.trans hk
  have hRun := htRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hPos)
  refine ⟨pos, hPos, u, stop, huAt, hRun, ?_⟩
  rw [htRank, hCount]

set_option maxRecDepth 100000 in
/-- Steady round boundaries can be replayed in any consistent prefix using the
actual shuffle ordinals, until the requested observed iteration is reached. -/
theorem steadyObservedIterations {l : Launch} {X : Execution} {g index iteration hops bound : Nat}
    (warp : Fin 2) (hTrip : bound < 2 ^ 31) (hIteration : iteration < bound)
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 1396 ([(7181, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hFeasible : iteration + hops < bound ∨ e.pc < 1744)
    (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : 1741 ≤ e.pc ∨ ((X.tr g).take index).countP Execution.isShfl + 64 * hops <
      ((X.tr g).take j).countP Execution.isShfl) :
    ∃ pos ≤ j, ∃ u stop, iteration + hops < bound ∧
      At u 1396 ([(7181, b32 (iteration + hops)), (1091, b32 bound)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 64 * hops := by
  induction hops generalizing index iteration s ending with
  | zero => exact ⟨index, hBefore, s, ending, hIteration, hs, hr, by simp⟩
  | succ hops ih =>
    obtain ⟨mid, hMidBefore, t, stop, ht, htRun, htRank⟩ :=
      steadyObservedAdvance hTrip hIteration hBody hTail hs hr he hBefore hSafe
        (hDemand.imp_right (fun h => by rw [Nat.mul_succ] at h; omega))
    have hContinues : iteration + 1 < bound := by
      rcases hFeasible with hBound | hSteady
      · omega
      by_contra! hEnds
      have ht' : At t 1744 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] := by
        have hAt := ht.mono (G := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
          ⟨holds_mem ht.2.2.2.2.2.2 hShared, holds_mem ht.2.2.2.2.2.2 hWarp, trivial⟩
        rw [ite_eq_right (show ¬ iteration + 1 < bound by omega)] at hAt
        exact hAt
      obtain ⟨vs, hw⟩ := Mma.walkFromRun htRun
      have hMem : e ∈ (X.tr g).drop mid := by
        apply List.mem_of_getElem? (i := j - mid)
        rw [List.getElem?_drop, Nat.add_sub_of_le hMidBefore]
        exact he
      have hFloor := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1744)
        (show 1744 ≤ t.pc ∧ t.pc ≤ 1901 by rw [ht'.1]; decide)
        (ringShapeOfAt ht') ht'.2.2.2.2 (fun _ => by kernel_rfl) hw e hMem
      omega
    have hAt : At t 1396 ([(7181, b32 (iteration + 1)), (1091, b32 bound)] ++ F) := by
      simpa [hContinues] using ht
    have hNext : 1741 ≤ e.pc ∨ ((X.tr g).take mid).countP Execution.isShfl + 64 * hops <
        ((X.tr g).take j).countP Execution.isShfl :=
      hDemand.imp_right (fun h => by rw [htRank]; rw [Nat.mul_succ] at h; omega)
    have hMode : iteration + 1 + hops < bound ∨ e.pc < 1744 :=
      hFeasible.imp_left (fun h => by omega)
    obtain ⟨pos, hPos, u, tail, hLoop, hu, huRun, huRank⟩ :=
      ih hContinues hAt htRun hMidBefore hMode hNext
    have hEq : iteration + 1 + hops = iteration + (hops + 1) := by omega
    rw [hEq] at hLoop hu
    refine ⟨pos, hPos, u, tail, hLoop, hu, huRun, ?_⟩
    rw [huRank, htRank, Nat.mul_succ]
    omega

section
variable {l : Launch} {X : Execution} {g index iteration bound : Nat} (warp : Fin 2)
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < bound) {s : TState} {ending : Option TState}
    {F : List (Nat × Value)} {ι : Type} (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (remaining : ι → Nat → Nat) (mark : ι → Event → Bool) (hZero : ∀ a, remaining a 1741 = 0)
    (hRankStep : ∀ {t u evt}, 1396 ≤ t.pc → t.pc < 1741 →
      WStep kernel Assumptions.all l g t evt u →
      ∀ a, remaining a t.pc = evt.toList.countP (mark a) + remaining a u.pc)
    (hs : At s 1396 ([(7181, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e)
include warp hTrip hIteration hShared hWarp hBody hTail remaining mark hZero hRankStep hs hr he

set_option maxRecDepth 100000 in
/-- Replay all projections through the same observed iterations or the exact exit. -/
theorem steadyProjectionsCheckpointOrExit (hBefore : index ≤ j) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ((1396 ≤ e.pc ∧ e.pc < 1741) ∧
      ∃ round, iteration ≤ round ∧ round < bound ∧
        (∀ a, ((X.tr g).take j).countP (mark a) + remaining a e.pc =
          ((X.tr g).take index).countP (mark a) + remaining a 1396 * (round-iteration+1)) ∧
        ∃ pos ≤ j, ∃ u stop, At u 1396 ([(7181, b32 round), (1091, b32 bound)] ++ F) ∧
          Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
          ∀ a, ((X.tr g).take pos).countP (mark a) =
            ((X.tr g).take index).countP (mark a) + remaining a 1396 * (round - iteration)) ∨
    (∃ pos ≤ j, ∃ u stop, At u 1744
        [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ∀ a, ((X.tr g).take pos).countP (mark a) =
        ((X.tr g).take index).countP (mark a) + remaining a 1396 * (bound-iteration)) := by
  generalize hf : bound - iteration = fuel
  induction fuel generalizing index iteration s ending with
  | zero => omega
  | succ fuel ih =>
    rcases prefixProjectionsCutOrEvent (by decide) hBody remaining mark hZero hRankStep
      hs hr he hBefore hSafe with
      ⟨hLo,hHi,hOrdinal⟩ | ⟨mid,hMid,t,stop,ht,htRun,htRank⟩
    · refine .inl ⟨⟨hLo,hHi⟩,iteration,le_rfl,hIteration,?_,index,hBefore,s,ending,hs,hr,?_⟩
      · intro a
        simpa using hOrdinal a
      · intro a
        simp
    obtain ⟨u,hu,hU⟩ := steadyCounterWithFrame (l := l) (g := g)
      hTrip hIteration hTail ht
    have huRun := htRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hMid)
    by_cases hNext : iteration + 1 < bound
    · rw [ite_eq_left hNext] at hU
      rcases ih hNext hU huRun hMid (by omega) with
        ⟨hSite,round,hRound,hLimit,hRank,pos,hPos,v,out,hV,hVRun,hStart⟩ |
      ⟨pos,hPos,v,out,hV,hVRun,hRank⟩
      · refine .inl ⟨hSite,round,by omega,hLimit,?_,pos,hPos,v,out,hV,hVRun,?_⟩
        · intro a
          rw [hRank a,htRank a,
            show round-iteration+1 = (round-(iteration+1)+1)+1 by omega]
          simp only [Nat.mul_add,Nat.mul_one]
          omega
        · intro a
          rw [hStart a, htRank a, show round - iteration = round - (iteration + 1) + 1 by omega]
          simp only [Nat.mul_add, Nat.mul_one]
          omega
      · refine .inr ⟨pos,hPos,v,out,hV,hVRun,?_⟩
        intro a
        rw [hRank a,htRank a,Nat.mul_succ]
        omega
    · rw [ite_eq_right hNext] at hU
      have huAt := hU.mono (G := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
        ⟨holds_mem hU.2.2.2.2.2.2 hShared, holds_mem hU.2.2.2.2.2.2 hWarp, trivial⟩
      refine .inr ⟨mid,hMid,u,stop,huAt,huRun,?_⟩
      intro a
      have hOne : fuel + 1 = 1 := by omega
      simpa only [hOne,Nat.mul_one] using htRank a

/-- Describe the selected traversal and its event ordinal, or replay to the exit. -/
theorem steadyProjectionsRoundOrExit (hBefore : index ≤ j) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ((1396 ≤ e.pc ∧ e.pc < 1741) ∧
      ∃ round, iteration ≤ round ∧ round < bound ∧
        ∀ a, ((X.tr g).take j).countP (mark a) + remaining a e.pc =
          ((X.tr g).take index).countP (mark a) + remaining a 1396 * (round-iteration+1)) ∨
    (∃ pos ≤ j, ∃ u stop, At u 1744
        [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ∀ a, ((X.tr g).take pos).countP (mark a) =
        ((X.tr g).take index).countP (mark a) + remaining a 1396 * (bound-iteration)) := by
  rcases steadyProjectionsCheckpointOrExit warp hTrip hIteration hShared hWarp hBody hTail
    remaining mark hZero hRankStep hs hr he hBefore hSafe with h | h
  · obtain ⟨hSite, round, hRound, hLimit, hRank, _⟩ := h
    exact .inl ⟨hSite, round, hRound, hLimit, hRank⟩
  · exact .inr h
end

variable {l : Launch} {X : Execution} {g index iteration bound : Nat} (warp : Fin 2)
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < bound) {s : TState} {ending : Option TState}
    {F : List (Nat × Value)} (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n
        ([7181, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
include warp hTrip hIteration hShared hWarp hBody hTail

set_option maxRecDepth 100000 in
/-- A conserved projection identifies the actual traversal containing a selected
event while preserving the counter and immutable frame. -/
theorem steadyProjectedRoundOfObservedEvent (remaining : Nat → Nat) (mark : Event → Bool)
    (hZero : remaining 1741 = 0)
    (hRankStep : ∀ {t u evt}, 1396 ≤ t.pc → t.pc < 1741 →
      WStep kernel Assumptions.all l g t evt u →
      remaining t.pc = evt.toList.countP mark + remaining u.pc)
    (hs : At s 1396 ([(7181, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j) (hSteady : e.pc < 1741)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ round, iteration ≤ round ∧ round < bound ∧
      ((X.tr g).take j).countP mark + remaining e.pc =
        ((X.tr g).take index).countP mark + remaining 1396 * (round - iteration) +
          remaining 1396 := by
  rcases steadyProjectionsRoundOrExit warp hTrip hIteration hShared hWarp hBody hTail
    (fun (_ : Unit) => remaining) (fun _ => mark) (fun _ => hZero)
    (fun hLo hHi hStep _ => hRankStep hLo hHi hStep) hs hr he hBefore hSafe with
    ⟨_,round,hRound,hLimit,hRank⟩ | ⟨pos,hPos,u,stop,hu,hRun,_⟩
  · exact ⟨round,hRound,hLimit,by simpa [Nat.mul_add,Nat.add_assoc] using hRank ()⟩
  · have hMem : e ∈ (X.tr g).drop pos := by
      apply List.mem_of_getElem? (i := j-pos)
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact he
    obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRun
    have hBound := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1744)
      (show 1744 ≤ u.pc ∧ u.pc ≤ 1901 by rw [hu.1]; decide)
      (ringShapeOfAt hu) hu.2.2.2.2 (fun _ => by kernel_rfl) hWalk e hMem
    omega

variable (hs : At s 1396 ([(7181, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j)
include hs hr he hBefore

/-- An observed event in the steady body determines its actual round and the
number of shuffles preceding its decoded position within that round. -/
theorem steadyCheckpointOfObservedEvent (hSteady : e.pc < 1741) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ round, iteration ≤ round ∧ round < bound ∧
      (((X.tr g).take j).countP Execution.isShfl + loaderShuffleTail 1741 e.pc =
        ((X.tr g).take index).countP Execution.isShfl + 64 * (round - iteration) + 64) ∧
      ∃ pos ≤ j, ∃ u stop, At u 1396 ([(7181, b32 round), (1091, b32 bound)] ++ F) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
        ((X.tr g).take pos).countP Execution.isShfl =
          ((X.tr g).take index).countP Execution.isShfl + 64 * (round - iteration) := by
  have hCounted : (((kernel.code.drop 1396).take (1741 - 1396)).zipIdx 1396).all
      (fun (ins, pc) => LoaderRankedInstr 1741 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1741 1396 = 64 := by kernel_rfl
  rcases steadyProjectionsCheckpointOrExit warp hTrip hIteration hShared hWarp hBody hTail
    (fun (_ : Unit) => loaderShuffleTail 1741) (fun _ => Execution.isShfl)
    (fun _ => by simp [loaderShuffleTail])
    (fun hLo hHi hStep _ => rankedLoaderStep (by decide) hCounted hLo hHi hStep)
    hs hr he hBefore hSafe with
    ⟨_, round, hRound, hLimit, hRank, pos, hPos, u, stop, hu, hRun, hStart⟩ |
    ⟨pos, hPos, u, stop, hu, hRun, _⟩
  · exact ⟨round, hRound, hLimit, by
      simpa [hCount, Nat.mul_add, Nat.add_assoc] using hRank (),
      pos, hPos, u, stop, hu, hRun, by simpa only [hCount] using hStart ()⟩
  · have hMem : e ∈ (X.tr g).drop pos := by
      apply List.mem_of_getElem? (i := j - pos)
      rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
      exact he
    obtain ⟨vs, hWalk⟩ := Mma.walkFromRun hRun
    have hBound := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1744)
      (show 1744 ≤ u.pc ∧ u.pc ≤ 1901 by rw [hu.1]; decide)
      (ringShapeOfAt hu) hu.2.2.2.2 (fun _ => by kernel_rfl) hWalk e hMem
    omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
