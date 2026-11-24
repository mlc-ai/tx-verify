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
import Kernels.TmlFa4Fwd.Flow.Code.Part021
import Lemmas.Flow.NthEv

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

set_option maxRecDepth 100000 in
private theorem warmCounterWithFrame {l : Launch} {g iteration bound : Nat}
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < min bound 9)
    {t : TState} {F : List (Nat × Value)}
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (ht : At t 1348 ([(7174, b32 iteration), (1091, b32 bound)] ++ F)) :
    ∃ u, run kernel Assumptions.all l g 5 t = some u ∧
      At u (if iteration + 1 < min bound 9 then 917 else 1353)
        ([(7174, b32 (iteration + 1)), (1091, b32 bound)] ++ F) := by
  obtain ⟨v, hv, hV⟩ := warmRingCondition l g hTrip hIteration t
    (ht.mono ⟨ht.2.2.2.2.1, ht.2.2.2.2.2.1, trivial⟩)
  have hKeep : ((kernel.code.drop 1348).take 4).all
      (fun i => (1091 :: F.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) =
      true := by
    apply List.all_eq_true.mpr
    intro ins hi
    have hBound : ((kernel.code.drop 1348).take 4).all
        (fun i => !(writesRegs i.op).contains 1091) = true := by kernel_rfl
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hBound _ hi, List.all_eq_true.mp hTail _ hi⟩
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := 1091 :: F.map Prod.fst)
    (by decide) (by decide) ht.1 hKeep (by kernel_rfl) hv
  have hF := holdsSchedulerFrame ht.2.2.2.2.2.2 hvFrame
    (fun r hm => .tail 1091 (List.mem_map_of_mem hm))
  let takeBranch := decide (iteration + 1 < min bound 9)
  have hAt : At v 1352 ((199, .pred takeBranch) ::
      [(7174, b32 (iteration + 1)), (1091, b32 bound)] ++ F) :=
    hV.mono ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.1,
      (hvFrame 1091 (by simp)).trans ht.2.2.2.2.2.1, hF⟩
  obtain ⟨u, hu, hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1352 takeBranch hAt hAt.2.2.2.2.1 (by simp)
  obtain ⟨huA, _⟩ := loaderLinear (regs := []) (by decide) (by decide) hAt.1 (by simp) rfl hu
  exact ⟨u, run_comp hvA huA, by simpa [takeBranch] using hU.mono hU.2.2.2.2.2⟩

set_option maxRecDepth 100000 in
/-- More than one warm round's shuffles in a prefix force the actual continuation
through the observed round's counter branch. The immutable frame survives. -/
theorem warmObservedAdvance {l : Launch} {X : Execution} {g index iteration bound : Nat}
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < min bound 9)
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hBody : ∀ n, ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hSafe : ∀ f, e.kind ≠ .ub f)
    (hLater : 1348 ≤ e.pc ∨ ((X.tr g).take index).countP Execution.isShfl + 64 <
      ((X.tr g).take j).countP Execution.isShfl) :
    ∃ pos ≤ j, ∃ u stop,
      At u (if iteration + 1 < min bound 9 then 917 else 1353)
        ([(7174, b32 (iteration + 1)), (1091, b32 bound)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 64 := by
  have hWitness : ∃ k marker, k ≤ j ∧ X.get (g, k) = some marker ∧ index ≤ k ∧
      (1348 ≤ marker.pc ∨ (Execution.isShfl marker = true ∧
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
  have hCounted : (((kernel.code.drop 917).take (1348 - 917)).zipIdx 917).all
      (fun (ins, pc) => LoaderRankedInstr 1348 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1348 917 = 64 := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hBody hCounted hs hr hMark hkFrom
      (by rw [hCount]; exact hDemand) hClean
  obtain ⟨u, hu, huAt⟩ := warmCounterWithFrame (l := l) (g := g)
    hTrip hIteration hTail ht
  let pos := index + front.length
  have hPos : pos ≤ j := htBefore.trans hk
  have hRun := htRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hPos)
  refine ⟨pos, hPos, u, stop, huAt, hRun, ?_⟩
  rw [htRank, hCount]

set_option maxRecDepth 100000 in
/-- Warm round boundaries can be replayed in any consistent prefix using the
actual shuffle ordinals, until the requested observed iteration is reached. -/
theorem warmObservedIterations {l : Launch} {X : Execution} {g index iteration hops bound : Nat}
    (warp : Fin 2) (hTrip : bound < 2 ^ 31) (hIteration : iteration < min bound 9)
    {s : TState} {ending : Option TState} {F : List (Nat × Value)}
    (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {j : Nat} {e : Event} (he : X.get (g, j) = some e) (hBefore : index ≤ j)
    (hFeasible : iteration + hops < min bound 9 ∨ e.pc < 1353)
    (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : 1348 ≤ e.pc ∨ ((X.tr g).take index).countP Execution.isShfl + 64 * hops <
      ((X.tr g).take j).countP Execution.isShfl) :
    ∃ pos ≤ j, ∃ u stop, iteration + hops < min bound 9 ∧
      At u 917 ([(7174, b32 (iteration + hops)), (1091, b32 bound)] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ((X.tr g).take pos).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl + 64 * hops := by
  induction hops generalizing index iteration s ending with
  | zero => exact ⟨index, hBefore, s, ending, hIteration, hs, hr, by simp⟩
  | succ hops ih =>
    obtain ⟨mid, hMidBefore, t, stop, ht, htRun, htRank⟩ :=
      warmObservedAdvance hTrip hIteration hBody hTail hs hr he hBefore hSafe
        (hDemand.imp_right (fun h => by rw [Nat.mul_succ] at h; omega))
    have hContinues : iteration + 1 < min bound 9 := by
      rcases hFeasible with hBound | hWarm
      · omega
      by_contra! hEnds
      have ht' : At t 1353 [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] := by
        have hAt := ht.mono (G := [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))])
          ⟨holds_mem ht.2.2.2.2.2.2 hShared, holds_mem ht.2.2.2.2.2.2 hWarp, trivial⟩
        rw [ite_eq_right (show ¬ iteration + 1 < min bound 9 by omega)] at hAt
        exact hAt
      obtain ⟨vs, hw⟩ := Mma.walkFromRun htRun
      have hMem : e ∈ (X.tr g).drop mid := by
        apply List.mem_of_getElem? (i := j - mid)
        rw [List.getElem?_drop, Nat.add_sub_of_le hMidBefore]
        exact he
      have hFloor := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1353)
        (show 1353 ≤ t.pc ∧ t.pc ≤ 1901 by rw [ht'.1]; decide)
        (ringShapeOfAt ht') ht'.2.2.2.2 (fun _ => by kernel_rfl) hw e hMem
      omega
    have hAt : At t 917 ([(7174, b32 (iteration + 1)), (1091, b32 bound)] ++ F) := by
      simpa [hContinues] using ht
    have hNext : 1348 ≤ e.pc ∨ ((X.tr g).take mid).countP Execution.isShfl + 64 * hops <
        ((X.tr g).take j).countP Execution.isShfl :=
      hDemand.imp_right (fun h => by rw [htRank]; rw [Nat.mul_succ] at h; omega)
    have hMode : iteration + 1 + hops < min bound 9 ∨ e.pc < 1353 :=
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
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < min bound 9) {s : TState}
    {ending : Option TState} {F : List (Nat × Value)} {ι : Type}
    (hShared : (2535, b32 l.sharedBase) ∈ F) (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (remaining : ι → Nat → Nat) (mark : ι → Event → Bool) (hZero : ∀ a, remaining a 1348 = 0)
    (hRankStep : ∀ {t u evt}, 917 ≤ t.pc → t.pc < 1348 →
      WStep kernel Assumptions.all l g t evt u →
      ∀ a, remaining a t.pc = evt.toList.countP (mark a) + remaining a u.pc)
    (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e)
include warp hTrip hIteration hShared hWarp hBody hTail remaining mark hZero hRankStep hs hr he

set_option maxRecDepth 100000 in
/-- Replay all projections through the same observed iterations or the exact exit. -/
theorem warmProjectionsCheckpointOrExit (hBefore : index ≤ j) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ((917 ≤ e.pc ∧ e.pc < 1348) ∧
      ∃ round, iteration ≤ round ∧ round < min bound 9 ∧
        (∀ a, ((X.tr g).take j).countP (mark a) + remaining a e.pc =
          ((X.tr g).take index).countP (mark a) + remaining a 917 * (round-iteration+1)) ∧
        ∃ pos ≤ j, ∃ u stop, At u 917 ([(7174, b32 round), (1091, b32 bound)] ++ F) ∧
          Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
          ∀ a, ((X.tr g).take pos).countP (mark a) =
            ((X.tr g).take index).countP (mark a) + remaining a 917 * (round - iteration)) ∨
    (∃ pos ≤ j, ∃ u stop, At u 1353
        [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ∀ a, ((X.tr g).take pos).countP (mark a) =
        ((X.tr g).take index).countP (mark a) + remaining a 917 * (min bound 9-iteration)) := by
  generalize hf : min bound 9 - iteration = fuel
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
    obtain ⟨u,hu,hU⟩ := warmCounterWithFrame (l := l) (g := g)
      hTrip hIteration hTail ht
    have huRun := htRun.after_local_nonempty (run_rtg hu) (traceAfterObservedEvent he hMid)
    by_cases hNext : iteration + 1 < min bound 9
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
theorem warmProjectionsRoundOrExit (hBefore : index ≤ j) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ((917 ≤ e.pc ∧ e.pc < 1348) ∧
      ∃ round, iteration ≤ round ∧ round < min bound 9 ∧
        ∀ a, ((X.tr g).take j).countP (mark a) + remaining a e.pc =
          ((X.tr g).take index).countP (mark a) + remaining a 917 * (round-iteration+1)) ∨
    (∃ pos ≤ j, ∃ u stop, At u 1353
        [(2535, b32 l.sharedBase), (1062, b32 (14 + warp.val))] ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
      ∀ a, ((X.tr g).take pos).countP (mark a) =
        ((X.tr g).take index).countP (mark a) + remaining a 917 * (min bound 9-iteration)) := by
  rcases warmProjectionsCheckpointOrExit warp hTrip hIteration hShared hWarp hBody hTail
    remaining mark hZero hRankStep hs hr he hBefore hSafe with h | h
  · obtain ⟨hSite, round, hRound, hLimit, hRank, _⟩ := h
    exact .inl ⟨hSite, round, hRound, hLimit, hRank⟩
  · exact .inr h
end

variable {l : Launch} {X : Execution} {g index iteration bound : Nat} (warp : Fin 2)
    (hTrip : bound < 2 ^ 31) (hIteration : iteration < min bound 9) {s : TState}
    {ending : Option TState} {F : List (Nat × Value)} (hShared : (2535, b32 l.sharedBase) ∈ F)
    (hWarp : (1062, b32 (14 + warp.val)) ∈ F)
    (hBody : ∀ n, ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n
        ([7174, 1091] ++ F.map Prod.fst) ins.op) = true)
    (hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
include warp hTrip hIteration hShared hWarp hBody hTail

set_option maxRecDepth 100000 in
/-- A conserved projection identifies the actual traversal containing a selected
event while preserving the counter and immutable frame. -/
theorem warmProjectedRoundOfObservedEvent (remaining : Nat → Nat) (mark : Event → Bool)
    (hZero : remaining 1348 = 0)
    (hRankStep : ∀ {t u evt}, 917 ≤ t.pc → t.pc < 1348 →
      WStep kernel Assumptions.all l g t evt u →
      remaining t.pc = evt.toList.countP mark + remaining u.pc)
    (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j) (hWarm : e.pc < 1348)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ round, iteration ≤ round ∧ round < min bound 9 ∧
      ((X.tr g).take j).countP mark + remaining e.pc =
        ((X.tr g).take index).countP mark + remaining 917 * (round - iteration) +
          remaining 917 := by
  rcases warmProjectionsRoundOrExit warp hTrip hIteration hShared hWarp hBody hTail
    (fun (_ : Unit) => remaining) (fun _ => mark) (fun _ => hZero)
    (fun hLo hHi hStep _ => hRankStep hLo hHi hStep) hs hr he hBefore hSafe with
    ⟨_,round,hRound,hLimit,hRank⟩ | ⟨pos,hPos,u,stop,hu,hRun,_⟩
  · exact ⟨round,hRound,hLimit,by simpa [Nat.mul_add,Nat.add_assoc] using hRank ()⟩
  · have hMem : e ∈ (X.tr g).drop pos := by
      apply List.mem_of_getElem? (i := j-pos)
      rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
      exact he
    obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRun
    have hBound := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1353)
      (show 1353 ≤ u.pc ∧ u.pc ≤ 1901 by rw [hu.1]; decide)
      (ringShapeOfAt hu) hu.2.2.2.2 (fun _ => by kernel_rfl) hWalk e hMem
    omega


/-- An observed event in the warm body determines its actual round and the
number of shuffles preceding its decoded position within that round. -/
theorem warmCheckpointOfObservedEvent
    (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j) (hWarm : e.pc < 1348)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ round, iteration ≤ round ∧ round < min bound 9 ∧
      (((X.tr g).take j).countP Execution.isShfl + loaderShuffleTail 1348 e.pc =
        ((X.tr g).take index).countP Execution.isShfl + 64 * (round - iteration) + 64) ∧
      ∃ pos ≤ j, ∃ u stop, At u 917 ([(7174, b32 round), (1091, b32 bound)] ++ F) ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop pos) stop ∧
        ((X.tr g).take pos).countP Execution.isShfl =
          ((X.tr g).take index).countP Execution.isShfl + 64 * (round - iteration) := by
  have hCounted : (((kernel.code.drop 917).take (1348 - 917)).zipIdx 917).all
      (fun (ins, pc) => LoaderRankedInstr 1348 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1348 917 = 64 := by kernel_rfl
  rcases warmProjectionsCheckpointOrExit warp hTrip hIteration hShared hWarp hBody hTail
    (fun (_ : Unit) => loaderShuffleTail 1348) (fun _ => Execution.isShfl)
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
    have hBound := Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1353)
      (show 1353 ≤ u.pc ∧ u.pc ≤ 1901 by rw [hu.1]; decide)
      (ringShapeOfAt hu) hu.2.2.2.2 (fun _ => by kernel_rfl) hWalk e hMem
    omega

/-- The current warm traversal number and the observed within-round shuffle ordinal. -/
theorem warmRoundOfObservedEvent (hs : At s 917 ([(7174, b32 iteration), (1091, b32 bound)] ++ F))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) {j : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hBefore : index ≤ j) (hWarm : e.pc < 1348)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ round, iteration ≤ round ∧ round < min bound 9 ∧
      ((X.tr g).take j).countP Execution.isShfl + loaderShuffleTail 1348 e.pc =
        ((X.tr g).take index).countP Execution.isShfl + 64 * (round - iteration) + 64 := by
  obtain ⟨round, hRound, hLimit, hRank, _⟩ :=
    warmCheckpointOfObservedEvent warp hTrip hIteration hShared hWarp hBody hTail
      hs hr he hBefore hWarm hSafe
  exact ⟨round, hRound, hLimit, hRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
