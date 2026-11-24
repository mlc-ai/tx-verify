-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueFirstPass
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Shared facts kept during the initial inclusive scan. -/
def firstPassFacts (p : Params) (lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  [(7220, b32 (groupLaneTiles p 0 lane)), (7138, b32 p.heads),
    (268, .pred (!decide (laneHasRequest lane p.batch))), (1201, b32 lane),
    (7228, b32 p.batch)] ++ F

/-- The register holding the partial sum, including the inclusive result after the fifth round. -/
def firstPassScanReg (round : Nat) : Nat :=
  if h : round < 5 then firstScanSrc ⟨round, h⟩ else 7221

/-- A terminated warp continuation at a first-pass scan checkpoint. The thread state immediately
after its last event reaches the next shuffle through the decoded local steps. -/
structure FirstPassScan (p : Params) (l : Launch) (A : List Assumption) (X : Execution)
    (g : Nat) (F : Nat → List (Nat × Value)) (round shuffles votes : Nat)
    (ends : Nat → Option TState := fun _ => none) where
  pos : Nat → Nat
  before : Nat → TState
  scan : Nat → TState
  ordinals : WarpOrdinals l X g pos shuffles votes
  continuation : ∀ lane < 32, Run kernel A l (warpLane l g lane) (before lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane)
  localSteps : ∀ lane < 32,
    Relation.ReflTransGen (Tau kernel A l (warpLane l g lane)) (before lane) (scan lane)
  checkpoint : ∀ lane < 32, At (scan lane) (2796 + 4 * round)
    ((firstPassScanReg round, b32 (prefixWindow (groupLaneTiles p 0) (2 ^ round) lane)) ::
      firstPassFacts p lane (F lane))

private theorem firstPassFacts_frame {p : Params} {lane : Nat} {F : List (Nat × Value)}
    (hF : ∀ pair ∈ F, pair.1 ∈ firstPassRegs) :
    ∀ pair ∈ firstPassFacts p lane F, pair.1 ∈ firstPassFrameRegs := by
  intro pair hm
  simp only [firstPassFacts, List.cons_append, List.nil_append, List.mem_cons] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | hm
  all_goals first
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hF pair hm)))
    | simp [firstPassFrameRegs, firstPassRegs, schedulerFrameRegs]

/-- The per-lane scheduler counts enter the same initial up-shuffle instance. -/
theorem firstPassStartAt {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} {X : Execution} {g shuffles votes : Nat} (hg : g < l.threads)
    {F : Nat → List (Nat × Value)} {pos : Nat → Nat} {initial : Nat → TState}
    {ends : Nat → Option TState}
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hRun : ∀ lane < 32, Run kernel A l (warpLane l g lane) (initial lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane))
    (hInput : ∀ lane < 32, At (initial lane) 2778
      ([(1201, b32 lane), (7228, b32 p.batch), (7217, b32 (firstPassOffset p lane)),
        (2308, b32 (firstPassOffset p (if lane < 31 then lane + 1 else lane)))] ++ F lane)) :
    ∃ cur : FirstPassScan p l A X g F 0 shuffles votes ends, cur.pos = pos := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLocal (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel A l (warpLane l g lane)) (initial lane) u ∧
        At u 2796 ((7220, b32 (groupLaneTiles p 0 lane)) :: firstPassFacts p lane (F lane)) := by
    by_cases hl : lane < 32
    · let thread := warpLane l g lane
      have hLane : laneOf l thread = lane := (Step.sameWarp_lane hBlock hg hl).2
      let extra := [(1201, b32 lane), (7228, b32 p.batch)] ++ F lane
      have hMember : ∀ pair ∈ extra, pair.1 ∈ firstPassRegs := by
        intro pair hm
        simp only [extra, List.cons_append, List.nil_append, List.mem_cons] at hm
        rcases hm with rfl | rfl | hm
        · simp [firstPassRegs, schedulerFrameRegs]
        · simp [firstPassRegs]
        · exact hF lane hl pair hm
      have ht := hInput lane hl
      have hIn : At (initial lane) 2778 ([(1201, b32 lane), (7228, b32 p.batch),
          (7217, b32 (firstPassOffset p lane)),
          (2308, b32 (firstPassOffset p (if lane < 31 then lane + 1 else lane)))] ++ extra) := by
        have hs := ht.2.2.2.2
        exact ht.mono ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.1, hs.2.1, hs.2.2.2.2⟩
      obtain ⟨u, hu, hs⟩ := firstPassPrelude hp thread
        (fun hlo hhi => hModel thread hlo (by omega)) hMember (by simpa only [hLane] using hIn)
      have hOut : At u 2796
          ((7220, b32 (groupLaneTiles p 0 lane)) :: firstPassFacts p lane (F lane)) := by
        rw [firstPassFacts]
        have h := (show At u 2796 _ from hs)
        rw [hLane] at h
        exact h.mono ⟨h.2.2.2.2.1, h.2.2.2.2⟩
      exact ⟨u, fun _ => ⟨run_rtg hu, hOut⟩⟩
    · exact ⟨initial lane, fun hh => False.elim (hl hh)⟩
  choose u hu using hLocal
  refine ⟨⟨pos, initial, u, hOrd, hRun, fun lane hl => (hu lane hl).1, ?_⟩, rfl⟩
  intro lane hl
  simpa [firstPassScanReg, firstScanSrc, prefixWindow_one] using (hu lane hl).2

/-- The per-lane scheduler counts enter the same initial up-shuffle instance. -/
theorem firstPassStart {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} {X : Execution} {g shuffles votes : Nat} (hg : g < l.threads)
    {F : Nat → List (Nat × Value)} {pos : Nat → Nat} {initial : Nat → TState}
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hRun : ∀ lane < 32, Run kernel A l (warpLane l g lane) (initial lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none)
    (hInput : ∀ lane < 32, At (initial lane) 2778
      ([(1201, b32 lane), (7228, b32 p.batch), (7217, b32 (firstPassOffset p lane)),
        (2308, b32 (firstPassOffset p (if lane < 31 then lane + 1 else lane)))] ++ F lane)) :
    Nonempty (FirstPassScan p l A X g F 0 shuffles votes) := by
  obtain ⟨cur, _⟩ := firstPassStartAt hp hg hModel hF hOrd hRun hInput
  exact ⟨cur⟩

private theorem firstScanDst_disjoint (round : Fin 5) :
    firstScanDst round ≠ firstScanSrc round ∧ firstScanDst round ∉ firstPassFrameRegs := by
  fin_cases round <;> decide

private theorem firstScanResult_next (round : Fin 5) :
    firstScanResult round = firstPassScanReg (round.val + 1) := by
  fin_cases round <;> rfl

/-- Each warp-wide round consumes the actual observed shuffle in every lane and keeps the
continuations aligned at their next positions. -/
theorem FirstPassScan.advanceTo {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} {X : Execution} (hX : Consistent l kernel A m X)
    {g round shuffles votes : Nat} (hg : g < l.threads) (hRound : round < 5)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : FirstPassScan p l A X g F round shuffles votes ends)
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨
      WarpFollowsEvent l X g cur.pos src index target)
    (hPc : firstScanPc ⟨round, hRound⟩ < target.pc) :
    ∃ next : FirstPassScan p l A X g F (round + 1) (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let stage : Fin 5 := ⟨round, hRound⟩
  let part := prefixWindow (groupLaneTiles p 0) (2 ^ round)
  let thread := warpLane l g
  let pc := firstScanPc stage
  let shift := 2 ^ round
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (thread lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  have hAt (lane : Nat) (hl : lane < 32) : At (cur.scan lane) pc
      ((firstScanSrc stage, b32 (part lane)) :: firstPassFacts p lane (F lane)) := by
    change At (cur.scan lane) (2796 + 4 * round)
      ((firstScanSrc ⟨round, hRound⟩, b32 (part lane)) :: firstPassFacts p lane (F lane))
    simpa only [firstPassScanReg, dite_eq_left hRound] using cur.checkpoint lane hl
  let after := fun (lane : Nat) (recv : Value) =>
    next (setReg (cur.scan lane) (firstScanDst stage) recv)
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel A l (thread lane) (cur.before lane) (cur.scan lane)
        (.shfl .up (b32 (part lane)) shift 0 (fun value _ => after lane value)) := by
    have hs := hAt lane hl
    have hOut := firstScanTemplate hp (thread lane) (cur.scan lane) stage (part lane)
      hs.1 hs.2.2.2.1 hs.2.2.2.2.1
    have hEq := hModel (thread lane) (s := cur.scan lane)
      (by rw [hs.1]; change _ ≤ 2796 + 4 * round; omega)
      (by rw [hs.1]; change 2796 + 4 * round < _; omega)
    exact ⟨cur.localSteps lane hl, hEq.trans hOut⟩
  have hSuffix : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | hw
    · intro lane hl hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · exact hw.shuffleSuffix hX cur.ordinals hBlock hg (hNext src hw.lane)
        (cur.continuation src hw.lane)
  have hObserve (lane : Nat) : ∃ recv ok, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨pc, .shfl .up (b32 (part lane)) shift 0 recv ok⟩ ∧
        Run kernel A l (thread lane) (after lane recv)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨recv, ok, he, _, hRest⟩ := (hNext lane hl).shuffle_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.shfl lane hl)
      exact ⟨recv, ok, fun _ => ⟨by rw [(hAt lane hl).1] at he; exact he, hRest⟩⟩
    · exact ⟨b32 0, false, fun hh => False.elim (hl hh)⟩
  choose recv ok witness using hObserve
  have hWhat := fun lane hl => (witness lane hl).1
  have hOrd := (cur.ordinals.shuffle (fun _ => pc) .up (fun lane => b32 (part lane))
    recv (fun _ => shift) (fun _ => 0) ok hWhat).2
  have hValue := cur.ordinals.shuffle_value hX hBlock hg (fun _ => pc) .up
    (fun lane => b32 (part lane)) recv (fun _ => shift) (fun _ => 0) ok hWhat
  have hLocal (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel A l (thread lane)) (after lane (recv lane)) u ∧
        At u (2796 + 4 * (round + 1))
          ((firstPassScanReg (round + 1),
            b32 (prefixWindow (groupLaneTiles p 0) (2 ^ (round + 1)) lane)) ::
            firstPassFacts p lane (F lane)) := by
    by_cases hl : lane < 32
    · have hDisj : ∀ pair ∈
          (firstScanSrc stage, b32 (part lane)) :: firstPassFacts p lane (F lane),
          pair.1 ≠ firstScanDst stage := by
        intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact (firstScanDst_disjoint stage).1.symm
        · intro eq
          exact (firstScanDst_disjoint stage).2 (eq ▸ firstPassFacts_frame (hF lane hl) pair hm)
      have hs := (hAt lane hl).set (v := recv lane) hDisj
      let q := (shflSource .up lane shift 0).1
      have hRecv : recv lane = b32 (part q) := (hValue lane hl).1
      have hFacts : At (after lane (recv lane)) (firstScanPc stage + 1)
          ([(1201, b32 lane), (firstScanSrc stage, b32 (part lane)),
            (firstScanDst stage, b32 (part q))] ++ firstPassFacts p lane (F lane)) :=
        hs.mono ⟨holds_mem hs.2.2.2.2 (by simp [firstPassFacts]), hs.2.2.2.2.2.1,
          hRecv ▸ hs.2.2.2.2.1, hs.2.2.2.2.2.2⟩
      obtain ⟨u, hu, hU⟩ := firstPassFold hp (thread lane) stage
        (fun hlo hhi => hModel (thread lane)
          (by simp [firstScanPc, stage] at hlo; omega)
          (by simp [firstScanPc, stage] at hhi; omega))
        (firstPassFacts_frame (hF lane hl)) (by simpa only [hLane lane hl] using hFacts)
      have hpEq : firstScanPc stage + 4 = 2796 + 4 * (round + 1) := by
        simp [firstScanPc, stage, Nat.mul_add, Nat.add_assoc]
      have hwEq : 2 * 2 ^ stage.val = 2 ^ (round + 1) := by
        simpa only [stage, Nat.pow_succ] using Nat.mul_comm 2 (2 ^ round)
      have hFact : At u (2796 + 4 * (round + 1))
          ((firstPassScanReg (round + 1),
            b32 (prefixWindow (groupLaneTiles p 0) (2 ^ (round + 1)) lane)) ::
            firstPassFacts p lane (F lane)) := by
        simpa only [hpEq, firstScanResult_next, hwEq, hLane lane hl] using hU
      exact ⟨u, fun _ => ⟨run_rtg hu, hFact⟩⟩
    · exact ⟨after lane (recv lane), fun hh => False.elim (hl hh)⟩
  choose final hFinal using hLocal
  refine ⟨⟨fun lane => cur.pos lane + 1, fun lane => after lane (recv lane), final, hOrd,
    fun lane hl => (witness lane hl).2, fun lane hl => (hFinal lane hl).1,
    fun lane hl => (hFinal lane hl).2⟩, ?_⟩
  exact fun h => h.afterShuffle hX hBlock hg hPc .up
    (fun lane => b32 (part lane)) recv (fun _ => shift) (fun _ => 0) ok hWhat

/-- Each warp-wide round consumes the actual observed shuffle in every lane and keeps the
terminated continuations aligned at their next positions. -/
theorem FirstPassScan.advance {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} {X : Execution} (hX : Consistent l kernel A m X)
    {g round shuffles votes : Nat} (hg : g < l.threads) (hRound : round < 5)
    {F : Nat → List (Nat × Value)} (cur : FirstPassScan p l A X g F round shuffles votes)
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs) :
    Nonempty (FirstPassScan p l A X g F (round + 1) (shuffles + 1) votes) := by
  obtain ⟨next, _⟩ := cur.advanceTo hp hX hg hRound hModel hF
    (src := 0) (index := 0) (target := ⟨2820, .exit⟩) (.inl (fun _ _ => rfl))
    (by change 2796 + 4 * round < 2820; omega)
  exact ⟨next⟩

/-- The five decoded rounds reach the inclusive-prefix checkpoint. -/
theorem FirstPassScan.complete {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {A : List Assumption} {X : Execution} (hX : Consistent l kernel A m X)
    {g shuffles votes : Nat} (hg : g < l.threads)
    {F : Nat → List (Nat × Value)} (cur : FirstPassScan p l A X g F 0 shuffles votes)
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs) :
    Nonempty (FirstPassScan p l A X g F 5 (shuffles + 5) votes) := by
  obtain ⟨s1⟩ := cur.advance hp hX hg (by decide) hModel hF
  obtain ⟨s2⟩ := s1.advance hp hX hg (by decide) hModel hF
  obtain ⟨s3⟩ := s2.advance hp hX hg (by decide) hModel hF
  obtain ⟨s4⟩ := s3.advance hp hX hg (by decide) hModel hF
  exact s4.advance hp hX hg (by decide) hModel hF

/-- Registers after the lane-31 broadcast and before the initial group-search branch. -/
def firstGroupFacts (p : Params) (cta lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  let limit := tilePrefix p (min p.batch 31) * p.heads
  [(7224, b32 limit), (277, .pred (decide (cta < limit))), (7223, b32 0),
    (7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p 0 j)),
    (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p 0 j))] ++ firstPassFacts p lane F

/-- The first scan's actual lane continuations at its uniform CTA cutoff. -/
structure FirstGroupCutoff (p : Params) (l : Launch) (A : List Assumption) (X : Execution)
    (g cta : Nat) (F : Nat → List (Nat × Value)) (shuffles votes : Nat)
    (ends : Nat → Option TState := fun _ => none) where
  pos : Nat → Nat
  before : Nat → TState
  branch : Nat → TState
  ordinals : WarpOrdinals l X g pos shuffles votes
  continuation : ∀ lane < 32, Run kernel A l (warpLane l g lane) (before lane)
    ((X.tr (warpLane l g lane)).drop (pos lane)) (ends lane)
  localSteps : ∀ lane < 32,
    Relation.ReflTransGen (Tau kernel A l (warpLane l g lane)) (before lane) (branch lane)
  checkpoint : ∀ lane < 32, At (branch lane) 2820 (firstGroupFacts p cta lane (F lane))

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {g cta shuffles votes : Nat} (hg : g < l.threads)
    (hCta : cta < 2 ^ 31) {F : Nat → List (Nat × Value)}
include hp hX hg hCta

/-- The actual indexed broadcast of lane 31 advances the warp to the group-search branch. -/
theorem FirstPassScan.groupCutoffTo {ends : Nat → Option TState}
    (cur : FirstPassScan p l A X g F 5 shuffles votes ends)
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) {src index : Nat} {target : Event}
    (hProgress : (∀ lane < 32, ends lane = none) ∨ WarpFollowsEvent l X g cur.pos src index target)
    (hPc : 2816 < target.pc) :
    ∃ next : FirstGroupCutoff p l A X g cta F (shuffles + 1) votes ends,
      WarpFollowsEvent l X g cur.pos src index target →
        WarpFollowsEvent l X g next.pos src index target := by
  let thread := warpLane l g
  let part := fun lane => ∑ j ∈ Finset.range (lane + 1), groupLaneTiles p 0 j
  let count := part 31
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAt (lane : Nat) (hl : lane < 32) :
      At (cur.scan lane) 2816 ((7221, b32 (part lane)) :: firstPassFacts p lane (F lane)) := by
    have hu := cur.checkpoint lane hl
    change At (cur.scan lane) 2816 ((7221, b32 (prefixWindow (groupLaneTiles p 0) 32 lane)) ::
      firstPassFacts p lane (F lane)) at hu
    simpa only [part, prefixWindow_warp _ hl] using hu
  let after := fun (lane : Nat) (recv : Value) => next (setReg (cur.scan lane) 7222 recv)
  have hNext (lane : Nat) (hl : lane < 32) :
      Next kernel A l (thread lane) (cur.before lane) (cur.scan lane)
        (.shfl .idx (b32 (part lane)) 31 31 (fun value _ => after lane value)) := by
    have ht := hAt lane hl
    have hOut := firstGroupTotalTemplate hp (thread lane) (cur.scan lane) (part lane)
      ht.1 ht.2.2.2.1 ht.2.2.2.2.1
    have hEq := hModel (thread lane) (s := cur.scan lane)
      (by rw [ht.1]; decide) (by rw [ht.1]; decide)
    exact ⟨cur.localSteps lane hl, hEq.trans hOut⟩
  have hSuffix : ∀ lane < 32, (X.tr (thread lane)).drop (cur.pos lane) ≠ [] := by
    rcases hProgress with he | hw
    · intro lane hl hNil
      have hr := cur.continuation lane hl
      rw [hNil, he lane hl] at hr
      cases hr
    · exact hw.shuffleSuffix hX cur.ordinals hBlock hg (hNext src hw.lane)
        (cur.continuation src hw.lane)
  have hObserve (lane : Nat) : ∃ recv ok, lane < 32 →
      X.get (thread lane, cur.pos lane) = some ⟨2816, .shfl .idx (b32 (part lane)) 31 31 recv ok⟩ ∧
        Run kernel A l (thread lane) (after lane recv)
          ((X.tr (thread lane)).drop (cur.pos lane + 1)) (ends lane) := by
    by_cases hl : lane < 32
    · obtain ⟨recv, ok, he, _, hRest⟩ := (hNext lane hl).shuffle_at_nonempty
        (cur.continuation lane hl) (hSuffix lane hl) (cur.ordinals.shfl lane hl)
      exact ⟨recv, ok, fun _ => ⟨by rw [(hAt lane hl).1] at he; exact he, hRest⟩⟩
    · exact ⟨b32 0, false, fun hh => False.elim (hl hh)⟩
  choose recv ok witness using hObserve
  have hEvent := fun lane hl => (witness lane hl).1
  have hOrd := (cur.ordinals.shuffle (fun _ => 2816) .idx (fun lane => b32 (part lane))
    recv (fun _ => 31) (fun _ => 31) ok hEvent).2
  have hValue := cur.ordinals.shuffle_value hX hBlock hg (fun _ => 2816) .idx
    (fun lane => b32 (part lane)) recv (fun _ => 31) (fun _ => 31) ok hEvent
  have hLocal (lane : Nat) : ∃ u, lane < 32 →
      Relation.ReflTransGen (Tau kernel A l (thread lane)) (after lane (recv lane)) u ∧
        At u 2820 (firstGroupFacts p cta lane (F lane)) := by
    by_cases hl : lane < 32
    · let frame := (7222, b32 count) :: (7221, b32 (part lane)) :: firstPassFacts p lane (F lane)
      have hFrame : ∀ pair ∈ frame, pair.1 ∈ firstPassLimitRegs := by
        intro pair hm
        simp only [frame, List.mem_cons] at hm
        rcases hm with rfl | rfl | hm
        · simp [firstPassLimitRegs]
        · simp [firstPassLimitRegs]
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (firstPassFacts_frame
            (hF lane hl) pair hm))
      have hFresh : ∀ pair ∈ (7221, b32 (part lane)) :: firstPassFacts p lane (F lane),
          pair.1 ≠ 7222 := by
        intro pair hm
        rcases List.mem_cons.mp hm with rfl | hm
        · change (7221 : Nat) ≠ 7222
          decide
        · intro eq
          have hh : 7222 ∈ firstPassFrameRegs := eq ▸ firstPassFacts_frame (hF lane hl) pair hm
          exact (of_decide_eq_true (by decide : decide (7222 ∉ firstPassFrameRegs) = true)) hh
      have hv := (hValue lane hl).1
      rw [shflSource_idx lane (by decide : 31 < 32)] at hv
      have hState : At (after lane (recv lane)) 2817 frame := by
        have ht := (hAt lane hl).set (v := recv lane) hFresh
        simpa only [hv] using ht
      have ht : At (after lane (recv lane)) 2817
          ([(7222, b32 count), (7138, b32 p.heads), (1072, b32 cta)] ++ frame) :=
        hState.mono ⟨hState.2.2.2.2.1, holds_mem hState.2.2.2.2 (by simp [frame, firstPassFacts]),
          holds_mem hState.2.2.2.2 (by simp [frame, firstPassFacts, hCtaFact lane hl]),
          hState.2.2.2.2⟩
      obtain ⟨u, hu, hU⟩ := firstPassLimit hp (thread lane) hCta
        (fun hlo hhi => hModel (thread lane) (by omega) hhi) hFrame ht
      exact ⟨u, fun _ => ⟨run_rtg hu, hU⟩⟩
    · exact ⟨after lane (recv lane), fun hh => False.elim (hl hh)⟩
  choose final hFinal using hLocal
  refine ⟨⟨fun lane => cur.pos lane + 1, fun lane => after lane (recv lane), final, hOrd,
    fun lane hl => (witness lane hl).2, fun lane hl => (hFinal lane hl).1,
    fun lane hl => (hFinal lane hl).2⟩, ?_⟩
  exact fun h => h.afterShuffle hX hBlock hg hPc .idx
    (fun lane => b32 (part lane)) recv (fun _ => 31) (fun _ => 31) ok hEvent

/-- The actual indexed broadcast of lane 31 advances the warp to the group-search branch. -/
theorem FirstPassScan.groupCutoff (cur : FirstPassScan p l A X g F 5 shuffles votes)
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane) :
    Nonempty (FirstGroupCutoff p l A X g cta F (shuffles + 1) votes) := by
  obtain ⟨next, _⟩ := cur.groupCutoffTo hp hX hg hCta hModel hF hCtaFact
    (src := 0) (index := 0) (target := ⟨2820, .exit⟩) (.inl (fun _ _ => rfl)) (by decide)
  exact ⟨next⟩

/-- The startup continuation, five up-shuffles and total broadcast reach the first group cutoff. -/
theorem firstPassThroughCutoff {pos : Nat → Nat} {initial : Nat → TState}
    (hModel : ∀ (thread : Nat) {s : TState}, 2778 ≤ s.pc → s.pc < 2820 →
      out kernel A l thread s = out kernel [] l thread s)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ firstPassRegs)
    (hCtaFact : ∀ lane < 32, (1072, b32 cta) ∈ F lane)
    (hOrd : WarpOrdinals l X g pos shuffles votes)
    (hRun : ∀ lane < 32, Run kernel A l (warpLane l g lane) (initial lane)
      ((X.tr (warpLane l g lane)).drop (pos lane)) none)
    (hInput : ∀ lane < 32, At (initial lane) 2778
      ([(1201, b32 lane), (7228, b32 p.batch), (7217, b32 (firstPassOffset p lane)),
        (2308, b32 (firstPassOffset p (if lane < 31 then lane + 1 else lane)))] ++ F lane)) :
    Nonempty (FirstGroupCutoff p l A X g cta F (shuffles + 6) votes) := by
  obtain ⟨s0⟩ := firstPassStart hp hg hModel hF hOrd hRun hInput
  obtain ⟨s5⟩ := s0.complete hp hX hg hModel hF
  exact s5.groupCutoff hp hX hg hCta hModel hF hCtaFact

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
