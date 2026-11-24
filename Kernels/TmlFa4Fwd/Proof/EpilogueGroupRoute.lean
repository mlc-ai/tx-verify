-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueBatchChoice
public import Kernels.TmlFa4Fwd.Proof.SchedulerCursor
public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPassEntry
public import Kernels.TmlFa4Fwd.Proof.EpilogueDrainFinish

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

section
variable {l : Launch} {X : Execution} {g pc pc' shuffles votes : Nat}
    {F G : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F shuffles votes ends)
    (hStep : ∀ lane < 32, ∃ u,
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane)) (cur.state lane) u ∧
        At u pc' (G lane))
include cur hStep

end

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pc shuffles votes dst : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g pc F shuffles votes ends) (mode : ShflMode) (a : Nat → Value)
    (b c : Nat → Nat) (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst)
    (hOut : ∀ lane < 32,
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) =
        .ev (.shfl mode (a lane) (b lane) (c lane)
          (fun v _ => next (setReg (cur.state lane) dst v))))
include hp hX hg cur mode a b c hFresh hOut

end

/-- The stable registers used by the group search, tile selection and output phases. -/
def groupSchedulerFrame (p : Params) (lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (268, .pred (!decide (laneHasRequest lane p.batch))) :: (7138, b32 p.heads) :: F

/-- Scheduler group-loop state before advancing to the next group. -/
def groupSearchFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  let limit := tilePrefix p (min p.batch (first + 31)) * p.heads
  [(1203, b32 (cta + 1)), (7223, b32 first), (7218, b32 limit),
    (7228, b32 p.batch), (1201, b32 lane), (1072, b32 cta)] ++ groupSchedulerFrame p lane F

/-- The verified lane contributions and prefix words needed by the selection ballot. -/
def groupChoiceFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
    (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
    (7138, b32 p.heads), (1072, b32 cta), (7223, b32 first),
    (7220, b32 (groupLaneTiles p first lane))] ++ groupSchedulerFrame p lane F

private theorem coreSchedulerOut {l : Launch} {g : Nat} {s : TState}
    (hLo : 2820 ≤ s.pc) (hHi : s.pc < 2959) :
    out kernel Assumptions.all l g s = out kernel [] l g s :=
  epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

private theorem firstCutoffBranch {p : Params} {l : Launch} {g cta lane : Nat}
    {F : List (Nat × Value)} {t : TState} (ht : At t 2820 (firstGroupFacts p cta lane F)) :
    let cutoff := tilePrefix p (min p.batch 31) * p.heads
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u (if cta < cutoff then 2878 else 2821) (firstGroupFacts p cta lane F) := by
  dsimp only
  let cutoff := tilePrefix p (min p.batch 31) * p.heads
  have hPred : t.regs 277 = some (.pred (decide (cta < cutoff))) := ht.2.2.2.2.2.1
  obtain ⟨u, hRun, hu⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2820 _ ht hPred (by simp)
  have hRunA := schedulerLocalTransport (A := Assumptions.all) (lo := 2820) (len := 1)
    rfl (fun hlo hhi => coreSchedulerOut hlo (by omega)) hRun (by rw [ht.1]) (by rw [ht.1])
  exact ⟨u, hRunA, by simpa only [decide_eq_true_eq] using hu⟩

private theorem firstFallbackWrites :
    ((kernel.code.drop 2821).take 3).all
      (fun ins => (7228 :: schedulerFrameRegs).all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstFallbackStraight :
    ((kernel.code.drop 2821).take 2).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

section
variable {p : Params} {l : Launch} {X : Execution} {g cta shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : FirstGroupCutoff p l Assumptions.all X g cta F shuffles votes ends)
    (hSkip : tilePrefix p (min p.batch 31) * p.heads ≤ cta) (hCta : cta < 2 ^ 31)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
include cur hSkip hCta hF

/-- The first cutoff's fallthrough starts the bounded reload loop. -/
theorem FirstGroupCutoff.enterSearchPreserving (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    ∃ result : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta 0 lane (F lane))
      shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  let cutoff := tilePrefix p (min p.batch 31) * p.heads
  have hLocal (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
        (cur.before lane) u ∧
        At u 2824 (groupSearchFacts p cta 0 lane (F lane)) := by
    by_cases hl : lane < 32
    · let thread := warpLane l g lane
      let frame := [(7228, b32 p.batch), (1201, b32 lane), (1072, b32 cta)] ++
        groupSchedulerFrame p lane (F lane)
      have hKeep : ∀ pair ∈ frame, pair.1 ∈ 7228 :: schedulerFrameRegs := by
        intro pair hm
        simp only [frame, groupSchedulerFrame, List.cons_append, List.nil_append,
          List.mem_cons] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | hm
        all_goals first
          | exact List.mem_cons_of_mem _ (hF lane hl pair hm)
          | simp [schedulerFrameRegs]
      obtain ⟨v, hv, hV⟩ := firstCutoffBranch (l := l) (g := thread) (cur.checkpoint lane hl)
      have htt : At v 2821 (firstGroupFacts p cta lane (F lane)) := by
        simpa only [ite_eq_right (Nat.not_lt_of_ge hSkip)] using hV
      have hs := htt.2.2.2.2
      have hAt : At v 2821 [(1072, b32 cta), (7224, b32 cutoff)] := htt.mono
        ⟨holds_mem hs (by simp [firstGroupFacts, firstPassFacts, hCtaFact lane hl]), hs.1, trivial⟩
      obtain ⟨u, hRun, hU⟩ := enterGroupSearch l thread (by omega) v hAt
      have hInit : Holds v.regs frame := by
        refine ⟨holds_mem hs (by simp [firstGroupFacts, firstPassFacts]),
          holds_mem hs (by simp [firstGroupFacts, firstPassFacts]),
          holds_mem hs (by simp [firstGroupFacts, firstPassFacts, hCtaFact lane hl]), ?_⟩
        have hTail := hs.2.2.2.2.2
        exact ⟨hTail.2.2.1, hTail.2.1, hTail.2.2.2.2.2⟩
      have hFrame := holdsSchedulerFrame hInit
        (fun _ hr => schedulerLocalFrame firstFallbackWrites firstFallbackStraight hRun
          (by rw [hAt.1]) (by rw [hAt.1]) hr) hKeep
      have hRunA := schedulerLocalTransport (A := Assumptions.all) (lo := 2821) (len := 3)
        firstFallbackStraight (fun hlo hhi => coreSchedulerOut (by omega) (by omega))
        hRun (by rw [hAt.1]) (by rw [hAt.1])
      refine ⟨u, fun _ => ⟨(cur.localSteps lane hl).trans (run_rtg (run_comp hv hRunA)), ?_⟩⟩
      have h := hU.2.2.2.2
      exact hU.mono ⟨h.1, h.2.1, h.2.2.1, hFrame⟩
    · exact ⟨cur.branch lane, fun h => False.elim (hl h)⟩
  choose u hu using hLocal
  exact ⟨⟨cur.pos, cur.before, u, cur.ordinals, cur.continuation, fun lane hl => (hu lane hl).1,
    fun lane hl => (hu lane hl).2⟩, rfl, rfl⟩

/-- The first cutoff's fallthrough starts the bounded reload loop. -/
theorem FirstGroupCutoff.enterSearchAt (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    ∃ result : SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta 0 lane (F lane))
      shuffles votes ends, result.pos = cur.pos := by
  obtain ⟨next, hPos, _⟩ := cur.enterSearchPreserving hSkip hCta hF hCtaFact
  exact ⟨next,hPos⟩
end

/-- The first cutoff's fallthrough starts the bounded reload loop. -/
theorem FirstGroupCutoff.enterSearch {p : Params} {l : Launch} {X : Execution}
    {g cta shuffles votes : Nat} {F : Nat → List (Nat × Value)}
    (cur : FirstGroupCutoff p l Assumptions.all X g cta F shuffles votes)
    (hSkip : tilePrefix p (min p.batch 31) * p.heads ≤ cta) (hCta : cta < 2 ^ 31)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    Nonempty (SchedulerWarpAt l X g 2824 (fun lane => groupSearchFacts p cta 0 lane (F lane))
      shuffles votes) := by
  obtain ⟨result, _⟩ := cur.enterSearchAt hSkip hCta hF hCtaFact
  exact ⟨result⟩

private theorem availabilityStraight :
    ((kernel.code.drop 2878).take 4).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The group test can inspect the live batch count before entering selection. -/
def groupAvailableFacts (p : Params) (cta first lane : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  (7228, b32 p.batch) :: groupChoiceFacts p cta first lane F

variable {p : Params} {l : Launch} {m : Mem0}

/-- The active group passes the availability check and exposes the actual ballot checkpoint. -/
theorem SchedulerWarpAt.enterBatchSelectionPreserving {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2878 (fun lane => groupAvailableFacts p cta first lane (F lane))
      shuffles votes ends) (hActive : first < p.batch)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    ∃ result : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  apply cur.advanceLocalPreserving
  intro lane hl
  let frame := groupAvailableFacts p cta first lane (F lane)
  have ht := cur.checkpoint lane hl
  have hKeep : ∀ pair ∈ frame, pair.1 ∈ groupAvailabilityRegs := by
    intro pair hm
    simp only [frame, groupAvailableFacts, groupChoiceFacts, groupSchedulerFrame, List.cons_append,
      List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hm
    all_goals first
      | exact List.mem_append.mpr (.inr (hF lane hl pair hm))
      | simp [groupAvailabilityRegs, schedulerFrameRegs]
  obtain ⟨u, hu, hU⟩ := groupAvailabilityFramed l (warpLane l g lane)
    (lt_trans hActive hp.shape.2.1) hp.shape.2.1 hKeep
    (by simp [frame, groupAvailableFacts, groupChoiceFacts]) (by simp [frame, groupAvailableFacts])
    ht
  have hRun := schedulerLocalTransport (A := Assumptions.all) (lo := 2878) (len := 5)
    availabilityStraight (fun hlo hhi => coreSchedulerOut (by omega) (by omega))
    hu (by rw [ht.1]) (by rw [ht.1])
  refine ⟨u, run_rtg hRun, ?_⟩
  simpa only [ite_eq_right (Nat.not_le_of_gt hActive)] using (hU.mono hU.2.2.2.2.2.2)

/-- Follow the local selection while preserving every recorded lane boundary. -/
theorem SchedulerWarpAt.enterBatchSelectionAt {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2878 (fun lane => groupAvailableFacts p cta first lane (F lane))
      shuffles votes ends) (hActive : first < p.batch)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    ∃ result : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes ends, result.pos = cur.pos := by
  obtain ⟨result,hPos,_⟩ := SchedulerWarpAt.enterBatchSelectionPreserving hp cur hActive hF
  exact ⟨result,hPos⟩

/-- The active group passes the availability check and exposes the actual ballot checkpoint. -/
theorem SchedulerWarpAt.enterBatchSelection {X : Execution} (hp : Pre p l m)
    {g cta first shuffles votes : Nat} {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2878 (fun lane => groupAvailableFacts p cta first lane (F lane))
      shuffles votes) (hActive : first < p.batch)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs) :
    Nonempty (SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta first lane (F lane))
      shuffles votes) := by
  obtain ⟨result, _⟩ := cur.enterBatchSelectionAt hp hActive hF
  exact ⟨result⟩

/-- The first cutoff's taken branch arrives at the ballot with verified group-zero operands. -/
theorem FirstGroupCutoff.enterSelectionPreserving {X : Execution} (hp : Pre p l m)
    {g cta shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : FirstGroupCutoff p l Assumptions.all X g cta F shuffles votes ends)
    (hFound : cta < tilePrefix p (min p.batch 31) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    ∃ result : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta 0 lane (F lane))
      shuffles votes ends,
      result.pos = cur.pos ∧ result.before = cur.before := by
  have hLocal (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
        (cur.before lane) u ∧
        At u 2883 (groupChoiceFacts p cta 0 lane (F lane)) := by
    by_cases hl : lane < 32
    · let thread := warpLane l g lane
      let frame := (7228, b32 p.batch) :: groupChoiceFacts p cta 0 lane (F lane)
      have hKeep : ∀ pair ∈ frame, pair.1 ∈ groupAvailabilityRegs := by
        intro pair hm
        simp only [frame, groupChoiceFacts, groupSchedulerFrame, List.cons_append, List.nil_append,
          List.mem_cons] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hm
        all_goals first
          | exact List.mem_append.mpr (.inr (hF lane hl pair hm))
          | simp [groupAvailabilityRegs, schedulerFrameRegs]
      obtain ⟨v, hv, hV⟩ := firstCutoffBranch (l := l) (g := thread) (cur.checkpoint lane hl)
      have hAt : At v 2878 (firstGroupFacts p cta lane (F lane)) := by
        simpa only [ite_eq_left hFound] using hV
      have hs := hAt.2.2.2.2
      have hFrame : At v 2878 frame := by
        refine hAt.mono ⟨holds_mem hs (by simp [firstGroupFacts, firstPassFacts]),
          hs.2.2.2.1, hs.2.2.2.2.1, hs.1,
          holds_mem hs (by simp [firstGroupFacts, firstPassFacts]),
          holds_mem hs (by simp [firstGroupFacts, firstPassFacts, hCtaFact lane hl]),
          hs.2.2.1, holds_mem hs (by simp [firstGroupFacts, firstPassFacts]), ?_⟩
        have ht := hs.2.2.2.2.2
        exact ⟨ht.2.2.1, ht.2.1, ht.2.2.2.2.2⟩
      obtain ⟨u, hRun, hU⟩ := groupAvailabilityFramed l thread (first := 0) (batch := p.batch)
        (by decide) hp.shape.2.1
        hKeep (by simp [frame, groupChoiceFacts]) (by simp [frame]) hFrame
      have hRunA := schedulerLocalTransport (A := Assumptions.all) (lo := 2878) (len := 5)
        availabilityStraight (fun hlo hhi => coreSchedulerOut (by omega) (by omega))
        hRun (by rw [hFrame.1]) (by rw [hFrame.1])
      have hBranch : ¬p.batch ≤ 0 := by have := hp.shape.1; omega
      refine ⟨u, fun _ => ⟨(cur.localSteps lane hl).trans (run_rtg (run_comp hv hRunA)), ?_⟩⟩
      simpa only [ite_eq_right hBranch] using hU.mono hU.2.2.2.2.2.2
    · exact ⟨cur.branch lane, fun h => False.elim (hl h)⟩
  choose u hu using hLocal
  exact ⟨⟨cur.pos, cur.before, u, cur.ordinals, cur.continuation, fun lane hl => (hu lane hl).1,
    fun lane hl => (hu lane hl).2⟩, rfl, rfl⟩

/-- Follow the local selection while preserving every recorded lane boundary. -/
theorem FirstGroupCutoff.enterSelectionAt {X : Execution} (hp : Pre p l m)
    {g cta shuffles votes : Nat} {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : FirstGroupCutoff p l Assumptions.all X g cta F shuffles votes ends)
    (hFound : cta < tilePrefix p (min p.batch 31) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    ∃ result : SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta 0 lane (F lane))
      shuffles votes ends, result.pos = cur.pos := by
  obtain ⟨result,hPos,_⟩ := FirstGroupCutoff.enterSelectionPreserving hp cur hFound hF hCtaFact
  exact ⟨result,hPos⟩

/-- The first cutoff's taken branch arrives at the ballot with verified group-zero operands. -/
theorem FirstGroupCutoff.enterSelection {X : Execution} (hp : Pre p l m)
    {g cta shuffles votes : Nat} {F : Nat → List (Nat × Value)}
    (cur : FirstGroupCutoff p l Assumptions.all X g cta F shuffles votes)
    (hFound : cta < tilePrefix p (min p.batch 31) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    Nonempty (SchedulerWarpAt l X g 2883 (fun lane => groupChoiceFacts p cta 0 lane (F lane))
      shuffles votes) := by
  obtain ⟨result, _⟩ := cur.enterSelectionAt hp hFound hF hCtaFact
  exact ⟨result⟩

/-- The exhausted scheduler still has the batch sentinel and the original warp rank. -/
def exhaustedScheduleFacts (p : Params) : List (Nat × Value) :=
  [(7223, b32 p.batch), (7228, b32 p.batch), (1062, b32 13)]

private theorem noTileStraight :
    ((kernel.code.drop 2947).take 1).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- Exhausting the scheduler reaches the common exit via local instructions. -/
theorem SchedulerWarpAt.exitWithoutTileLocal {X : Execution} (hp : Pre p l m)
    {g shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p) shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    ∃ v, Relation.ReflTransGen (Tau kernel Assumptions.all l (warpLane l g lane))
        (cur.before lane) v ∧
      v.pc = 3099 ∧ v.fault = none ∧ v.regs 1062 = some (b32 13) := by
  let thread := warpLane l g lane
  have ht := cur.checkpoint lane hl
  have hKeep : ∀ pair ∈ exhaustedScheduleFacts p, pair.1 ∈ groupAvailabilityRegs := by
    intro pair hm
    simp only [exhaustedScheduleFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [groupAvailabilityRegs, schedulerFrameRegs]
  obtain ⟨u, hu, hU⟩ := groupAvailabilityFramed l thread hp.shape.2.1 hp.shape.2.1 hKeep
    (by simp [exhaustedScheduleFacts]) (by simp [exhaustedScheduleFacts]) ht
  have huA := schedulerLocalTransport (A := Assumptions.all) (lo := 2878) (len := 5)
    availabilityStraight (fun hlo hhi => coreSchedulerOut (by omega) (by omega))
    hu (by rw [ht.1]) (by rw [ht.1])
  have hpU : u.pc = 2947 := by simpa only [Nat.le_refl, ↓reduceIte] using hU.1
  let v := { next (setReg u 306 (.pred true)) with pc := 3099 }
  have hv : run kernel [] l thread 2 u = some v :=
    selectedBranch l thread u false hpU hU.2.2.2.1 hU.2.2.2.2.1
  have hvA := schedulerLocalTransport (A := Assumptions.all) (lo := 2947) (len := 2)
    noTileStraight (fun hlo hhi => coreSchedulerOut (by omega) (by omega))
    hv (by rw [hpU]) (by rw [hpU])
  have hWarp : v.regs 1062 = some (b32 13) := by
    simpa [v, next, setReg] using hU.2.2.2.2.2.2.2.1
  exact ⟨v, (cur.localSteps lane hl).trans (run_rtg (run_comp huA hvA)),
    rfl, hU.2.2.2.1, hWarp⟩

/-- If the scheduler has exhausted all requests, its actual remaining suffix is the common exit. -/
theorem SchedulerWarpAt.exitWithoutTile {X : Execution} (hp : Pre p l m) {g shuffles votes : Nat}
    (cur : SchedulerWarpAt l X g 2878 (fun _ => exhaustedScheduleFacts p) shuffles votes) :
    ∀ lane < 32, (X.tr (warpLane l g lane)).drop (cur.pos lane) = [⟨9205, .exit⟩] := by
  intro lane hl
  obtain ⟨v, hLocal, hPc, hFault, hWarp⟩ := cur.exitWithoutTileLocal hp lane hl
  exact drainExitTrace hPc hFault hWarp ((cur.continuation lane hl).after_local hLocal)

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
