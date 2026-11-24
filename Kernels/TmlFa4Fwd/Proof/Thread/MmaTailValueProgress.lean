-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningTripFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningKeyReturn
import Kernels.TmlFa4Fwd.Proof.MmaPoll
import Kernels.TmlFa4Fwd.Flow.Code.Part039
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.ReturningPrefix
import Lemmas.Execution.EventFrameSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame Prologue Epilogue
open Thread.Mma (ReadyPoll)
open Thread.Mma.Observation (readyObject)

noncomputable section

/-- Live query return arguments and probability pointers on the single-visit path. -/
def tailValueCommitFrame (l : Launch) : List (Nat × Value) :=
  [(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),(2614,b32 (l.sharedBase+112)),
   (2615,b32 (l.sharedBase+104)),(2618,b32 (l.sharedBase+120)),(7207,b32 1),
   (7205,b32 0),(7206,b32 0),(7208,b32 0)]

/-- The tail V wait operands, with the first early-P wait operands retained. -/
def tailValueWaitFrame (l : Launch) : List (Nat × Value) :=
  [(2609,b32 (l.sharedBase+40))] ++ tailValueCommitFrame l ++
    [(1194,b32 (l.sharedBase+8))]

private def tailValueBranchFrame (l : Launch) : List (Nat × Value) :=
  [(1189,b32 1),(2535,b32 l.sharedBase),(2610,b32 (l.sharedBase+96)),
   (2614,b32 (l.sharedBase+112)),(2615,b32 (l.sharedBase+104)),(2618,b32 (l.sharedBase+120))]

private theorem tailValueTakeBranch {l : Launch} {g : Nat} (hWidth : l.sharedBase+120 < 2^32) :
    Seg kernel Assumptions.all l g 10 2275 [(1189,b32 1),(2535,b32 l.sharedBase)]
      2534 (tailValueCommitFrame l) := by
  have hOffsets : Seg kernel [] l g 4 2275 [(1189,b32 1),(2535,b32 l.sharedBase)]
      2279 (tailValueBranchFrame l) := by
    intro s hs
    have h₀ : l.sharedBase+96 < 2^32 := by omega
    have h₁ : l.sharedBase+104 < 2^32 := by omega
    have h₂ : l.sharedBase+112 < 2^32 := by omega
    dsimp [tailValueBranchFrame]
    have ha := Nat.mod_eq_of_lt h₀
    have hb := Nat.mod_eq_of_lt h₁
    have hc := Nat.mod_eq_of_lt h₂
    have hd := Nat.mod_eq_of_lt hWidth
    seg_fp hs using norm_bits [ha,hb,hc,hd]
  have hBranch : Seg kernel [] l g 6 2279 (tailValueBranchFrame l) 2534
      (tailValueCommitFrame l) := by
    intro s hs
    dsimp [tailValueBranchFrame,tailValueCommitFrame] at hs ⊢
    seg_fp hs using seg_close
  intro s hs
  obtain ⟨u,hr,hu⟩ := hOffsets s hs
  obtain ⟨v,ht,hv⟩ := hBranch u hu
  have hFirst := localRun (by decide : 1904 ≤ 2275) (by decide : 2275+4 ≤ 2768) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl) hr
  have hLater := localRun (by decide : 1904 ≤ 2279) (by decide : 2279+6 ≤ 2768) hu.1
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  exact ⟨v,run_comp hFirst hLater,hv⟩

private def queryReturnSite (stage : Fin 2) : Fin 12 := ⟨7+stage.val,by have := stage.isLt; omega⟩

private theorem tailQueryReturnCode (stage : Fin 2) :
    let site := electSite (commitElection (queryReturnSite stage))
    kernel.code[site.pc]? = some
      ⟨none,.warp ⟨.elect,none,[site.result,some site.pred],[],some (.imm (-1))⟩⟩ := by
  fin_cases stage
  · exact Flow.code_2534
  · exact Flow.code_2538

private theorem tailQueryReturnOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (stage : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (electSite (commitElection (queryReturnSite stage))).pc
      (fun _ => tailValueCommitFrame l) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g ((commitSite (queryReturnSite stage)).pc+1)
      (fun _ => tailValueCommitFrame l) shuffles votes ends) ∧
    ∃ issuer index, SameWarp l g issuer ∧ X.Commit (issuer,index)
      (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  let site := queryReturnSite stage
  have hSite : (commitSite site).base = 2535 := by fin_cases stage <;> rfl
  have hOff : (commitSite site).off = 16+8*stage.val := by fin_cases stage <;> rfl
  have hWidth : l.sharedBase+(commitSite site).off < 2^32 := by
    rw [hOff]
    have := hp.shared.2.1
    have := stage.isLt
    omega
  have hAlign : (l.sharedBase+(commitSite site).off)%8 = 0 := by
    rw [hOff]
    have := hp.shared.1
    omega
  obtain ⟨tail,issuer,index,hw,he⟩ := commitWarpFromFreshElection hp hMax hg site cur
    (fun lane hl j hj mask inst leader he => noEarlierMmaElection _ (tailQueryReturnCode stage)
      (by fin_cases stage <;> (set_option maxRecDepth 15000 in kernel_rfl))
      (by fin_cases stage <;> kernel_rfl) (cur.checkpoint lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hj he)
    (by fin_cases stage <;>
      simp [tailValueCommitFrame,site,queryReturnSite,commitElection,electSite])
    (by fin_cases stage <;>
      simp [tailValueCommitFrame,site,queryReturnSite,commitElection,electSite])
    (by fin_cases stage <;>
      simp [tailValueCommitFrame,site,queryReturnSite,commitElection,electSite])
    (by rw [hSite]; exact List.mem_cons_self) hWidth hAlign
  rw [hOff,← Nat.add_assoc] at he
  exact ⟨tail,issuer,index,hw,_,he⟩

private theorem tailValueWaitSetup {l : Launch} {g : Nat} (hWidth : l.sharedBase+40 < 2^32) :
    Seg kernel Assumptions.all l g 3 2542 (tailValueCommitFrame l)
      2545 (tailValueWaitFrame l) := by
  have hPlus : l.sharedBase+8 < 2^32 := by omega
  have hLocal : Seg kernel [] l g 3 2542 (tailValueCommitFrame l) 2545
      (tailValueWaitFrame l) := by
    intro s hs
    dsimp [tailValueCommitFrame,tailValueWaitFrame] at hs ⊢
    seg_fp hs using norm_bits [Nat.mod_eq_of_lt hPlus,Nat.mod_eq_of_lt hWidth]
  intro s hs
  obtain ⟨t,ht,hAt⟩ := hLocal s hs
  exact ⟨t,localRun (by decide) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl) ht,hAt⟩

/-- Recorded key release with the selected loop trip count at the next checkpoint. -/
abbrev OpeningKeyReturnedWithTrip (l : Launch) (X : Execution)
    (g n shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2275 (fun _ => [(1189,b32 n),(2535,b32 l.sharedBase)])
    shuffles votes ends

/-- The tail V acquire at the beginning of the final MMA body. -/
abbrev OpeningTailValueReached (l : Launch) (X : Execution)
    (g shuffles votes : Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 2545 (fun _ => tailValueWaitFrame l) shuffles votes ends

/-- A single-visit MMA warp follows the terminal path, returns both query buffers,
and reaches the first V acquire without needing the acquire as a premise. -/
theorem openingTailValueReachedOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningKeyReturnedWithTrip l X g 1 shuffles votes ends) :
    Nonempty (OpeningTailValueReached l X g shuffles votes ends) ∧
    ∀ stage : Fin 2, ∃ issuer index, SameWarp l g issuer ∧
      X.Commit (issuer,index) (commitSpec l issuer (l.sharedBase+16+8*stage.val)) := by
  have hWidth : l.sharedBase+120 < 2^32 := by have := hp.shared.2.1; omega
  obtain ⟨first⟩ := cur.advanceLocal (fun lane hl => by
    obtain ⟨u,hu,hU⟩ := tailValueTakeBranch hWidth _ (cur.checkpoint lane hl)
    exact ⟨u,run_rtg hu,hU⟩)
  obtain ⟨⟨second⟩,h₀⟩ := tailQueryReturnOfMaximal hp hMax hg 0 first
  obtain ⟨⟨tail⟩,h₁⟩ := tailQueryReturnOfMaximal hp hMax hg 1 second
  refine ⟨tail.advanceLocal (fun lane hl => ?_),fun stage => ?_⟩
  · obtain ⟨u,hu,hU⟩ := tailValueWaitSetup (by omega : l.sharedBase+40 < 2^32) _
      (tail.checkpoint lane hl)
    exact ⟨u,run_rtg hu,hU⟩
  · fin_cases stage
    · exact h₀
    · exact h₁

/-- When the ready phase is one, a maximal lane in the tail records the first V acquire. -/
theorem openingTailValueWaitOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : OpeningTailValueReached l X g shuffles votes ends)
    (hReady : let log := X.objects (readyObject l g 1)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 1) :
    ∀ lane < 32, ∃ j, ReadyPoll l X (warpLane l g lane) j 1 0 true .cta := by
  intro lane hl
  have hBlock : l.block%32=0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWidth : l.sharedBase+40 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+40)%8 = 0 := by have := hp.shared.1; omega
  have hHeld : ∀ pair ∈ tailValueWaitFrame l, pair.1 ≠ (waitSite 9).result := by
    simp [tailValueWaitFrame,tailValueCommitFrame,waitSite]
  have hParity : ((waitSite 9).phase,b32 0) ∈ tailValueWaitFrame l := by
    simp [tailValueWaitFrame,tailValueCommitFrame,waitSite]
  obtain ⟨n,_,_,he,_,_,_,_⟩ := waitOfMaximal hMax hSame.1.2.1 9 hWidth hAlign (by decide)
    hHeld List.mem_cons_self hParity (fun _ _ _ => by
      obtain ⟨s,hs,hPhase⟩ := hReady
      have hEq : (warpLane l g lane)/l.block = g/l.block := hSame.1.2.2.symm
      change let log := X.objects ⟨.shared,(warpLane l g lane)/l.block,l.sharedBase+40⟩
        ∃ r, MBarrier.stateBefore log log.length = some r ∧ r.phase%2 ≠ 0%2
      rw [hEq]
      exact ⟨s,hs,by rw [hPhase]; decide⟩)
    (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl) (cur.checkpoint lane hl)
    (cur.recorded lane hl) (cur.continuation lane hl) (cur.localSteps lane hl)
  exact ⟨cur.pos lane+n,_,he,rfl⟩

private theorem tailFloorCode : ∀ floor ∈ [2285,2534],
    (kernel.code.drop floor).all (fun ins => Thread.staysPastEvent floor ins.op) = true := by
  intro floor hf
  rcases (by simpa using hf : floor = 2285 ∨ floor = 2534) with rfl | rfl <;>
    (set_option maxRecDepth 100000 in kernel_rfl)

private theorem tailFloorSegments : ∀ floor ∈ [2285,2534],
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
  intro floor hf
  rcases (by simpa using hf : floor = 2285 ∨ floor = 2534) with rfl | rfl <;> kernel_rfl

private theorem eventReachesFloor {l : Launch} {g floor : Nat} {t u : TState}
    {es : List Event} (hf : floor ∈ [2285,2534])
    (reach : TraceReach kernel Assumptions.all l g t es u)
    (contains : ∃ e ∈ es, floor ≤ e.pc) : floor ≤ u.pc := by
  have keep {a b : TState} {e : Option Event}
      (h : WStep kernel Assumptions.all l g a e b) (ha : floor ≤ a.pc) : floor ≤ b.pc :=
    Thread.eventTailStepOfAudit (tailFloorCode floor hf) (tailFloorSegments floor hf) ha h
  have hFloor {a b : TState} {events : List Event}
      (path : TraceReach kernel Assumptions.all l g a events b)
      (ha : floor ≤ a.pc) : floor ≤ b.pc := by
    induction path with
    | refl => exact ha
    | tau hu _ ih => exact ih (keep (.inl ⟨rfl,hu⟩) ha)
    | event he _ ih => exact ih (keep (.inr ⟨_,rfl,he⟩) ha)
  induction reach with
  | refl => simp at contains
  | tau _ _ ih => exact ih contains
  | event he rest ih =>
    obtain ⟨e,hMem,hPc⟩ := contains
    rcases List.mem_cons.mp hMem with rfl | heMem
    · exact hFloor rest (keep (.inr ⟨_,rfl,he⟩) ((estep_source_pc he).symm ▸ hPc))
    · exact ih ⟨e,heMem,hPc⟩

/-- The actual one-visit branch excludes every steady-loop event from this lane's trace,
including prefixes which end at any later wait. -/
theorem noSteadyEventOfSingleVisitOpening {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g shuffles votes lane : Nat} (hl : lane < 32)
    {ends : Nat → Option TState} (cur : OpeningKeyReturnedWithTrip l X g 1 shuffles votes ends)
    {j : Nat} {e : Event} (he : X.get (warpLane l g lane,j) = some e)
    (hLo : 2285 ≤ e.pc) (hHi : e.pc < 2534) : False := by
  let thread := warpLane l g lane
  change (X.tr thread)[j]? = some e at he
  by_cases hj : j < cur.pos lane
  · have hGet : ((X.tr thread).take (cur.pos lane))[j]? = some e := by
      rw [List.getElem?_take_of_lt hj]
      exact he
    have hpast := (cur.recorded lane hl).returning_reach
    have hPath := hpast.append (TraceReach.of_local (cur.localSteps lane hl))
    rw [List.append_nil] at hPath
    have hEnd := eventReachesFloor (by decide : 2285 ∈ [2285,2534]) hPath
      ⟨e,List.mem_of_getElem? hGet,hLo⟩
    have hPc := (cur.checkpoint lane hl).1
    omega
  · have hAfter : cur.pos lane ≤ j := Nat.le_of_not_gt hj
    have hGet : ((X.tr thread).drop (cur.pos lane))[j-cur.pos lane]? = some e := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hAfter]
      exact he
    have hNonempty : (X.tr thread).drop (cur.pos lane) ≠ [] := by
      intro h
      rw [h] at hGet
      simp at hGet
    have hWidth : l.sharedBase+120 < 2^32 := by have := hp.shared.2.1; omega
    obtain ⟨u,hr,hu⟩ := tailValueTakeBranch (g := thread) hWidth _ (cur.checkpoint lane hl)
    have hSuffix := (cur.continuation lane hl).after_local_nonempty
      ((cur.localSteps lane hl).trans (run_rtg hr)) hNonempty
    obtain ⟨_,hw⟩ := walkFromRun hSuffix
    have hAfter := Thread.eventTailEvents (tailFloorCode 2534 (by decide))
      (tailFloorSegments 2534 (by decide)) hw hu.1.ge e (List.mem_of_getElem? hGet)
    omega

end
end PTX.Kernels.TmlFa4Fwd.Mma
