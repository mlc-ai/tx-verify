-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueGroupTileTrace
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuQReadBytes
public import Kernels.TmlFa4Fwd.Proof.EpilogueWriteback
public import Lemmas.Flow.WriteSpace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The writeback operands and the registers used again by the drain scan. -/
def outputReadyFacts (p : Params) (l : Launch) (batch head tile lane : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  writebackEntry p l batch head tile ++
    ([(307, .pred (decide (p.batch < lane))), (1201, b32 lane), (7506, b64 p.cuQBase),
      (268, .pred (!decide (laneHasRequest lane p.batch))),
      (7147, b32 p.batch), (7138, b32 p.heads)] ++ F)

/-- Global access of a selected request endpoint. -/
def endpointAccess (p : Params) (row : Nat) : Acc :=
  { loc := globalLoc (p.cuQBase + 4 * row), size := 4 }

/-- The observed read of a selected request endpoint. -/
def endpointEvent (p : Params) (batch : Nat) (endpoint : Fin 2) : Event :=
  ⟨2953 + endpoint.val, .rd (endpointAccess p (batch + endpoint.val))
    ((b32 (p.qOffset (batch + endpoint.val))).toBytes.map some)⟩

private theorem readyModel {l : Launch} {g : Nat} {t : TState}
    (hLo : 2899 ≤ t.pc) (hHi : t.pc ≤ 2958) :
    out kernel Assumptions.all l g t = out kernel [] l g t :=
  epilogue_out_all_eq_nil (.inl ⟨by omega, by omega⟩)

private theorem readApproachStraight :
    ((kernel.code.drop 2949).take 3).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem readySetupStraight :
    ((kernel.code.drop 2955).take 2).all (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The suffix contains an issued tensor store. -/
def ContainsTensorStore (es : List Event) : Prop :=
  ∃ (pc a : Nat) (d : TensorStore.Spec), (⟨pc, .tensorStore a d⟩ : Event) ∈ es

variable {p : Params}

theorem replayEndpoint {l : Launch} {X : Execution} {g batch pos : Nat} {o : Option TState}
    (endpoint : Fin 2) (hReads : CuQWordReadsFromLaunchOnThread p X g (batch + endpoint.val))
    {before t u : TState} (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (he : EStep kernel [] l g t (endpointEvent p batch endpoint) (some u))
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop pos) o)
    (hDemand : o = none ∨ (X.tr g).drop pos ≠ []) :
    t.pc = 2953 + endpoint.val ∧ X.get (g, pos) = some (endpointEvent p batch endpoint) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o ∧
      ∀ pc a (d : TensorStore.Spec), (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop pos →
        (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop (pos + 1) := by
  let a := endpointAccess p (batch + endpoint.val)
  let bs := (b32 (p.qOffset (batch + endpoint.val))).toBytes.map some
  obtain ⟨tm, hOut, hf⟩ := he
  change Fires t.pc tm ⟨2953 + endpoint.val, .rd a bs⟩ (some u) at hf
  obtain ⟨k, rfl⟩ := fires_read_tmpl hf
  obtain ⟨observed, -, hEv, hU⟩ := hf
  have hPc : t.pc = 2953 + endpoint.val := (congrArg Event.pc hEv).symm
  have hBytes : observed = bs := by
    exact (Kind.rd.inj (congrArg Event.kind hEv)).2.symm
  subst observed
  obtain rfl := Option.some.inj hU
  have hNext : Next kernel Assumptions.all l g before t (.read a k) :=
    ⟨hLocal, (readyModel (by rw [hPc]; omega) (by rw [hPc]; omega)).trans hOut⟩
  cases hList : (X.tr g).drop pos with
  | nil =>
    rw [hList] at hRun hDemand
    rcases hDemand with rfl | hNonempty
    · cases hRun
    · exact (hNonempty rfl).elim
  | cons e es =>
    have hRest : (X.tr g).drop (pos + 1) = es := by
      rw [← List.drop_drop, hList]
      rfl
    rw [hList] at hRun
    obtain ⟨v, hf', hRun'⟩ := hNext.continuing_event (by
      rintro ⟨obs, _, _, hNone⟩
      cases hNone) hRun
    have hx : X.get (g, pos) = some e := by
      change (X.tr g)[pos]? = some e
      rw [show (X.tr g)[pos]? = ((X.tr g).drop pos)[0]? by simp, hList]
      rfl
    obtain ⟨obs, -, rfl, hState⟩ := hf'
    obtain rfl := Option.some.inj hState
    rw [hPc] at hx
    have hVal : obs = bs := hReads pos obs ⟨_, hx⟩
    subst obs
    refine ⟨hPc, hx, hRest.symm ▸ hRun', ?_⟩
    intro pc addr d hm
    rw [hRest]
    rcases List.mem_cons.mp hm with heq | hIn
    · cases heq
    · exact hIn

/-- The selected coordinates fix both endpoint reads before any writeback event. -/
theorem selectedEndpointPath {l : Launch} {m : Mem0} (hp : Pre p l m) {g cta first batch lane : Nat}
    {before t : TState} {F : List (Nat × Value)} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hl : lane < 32) (hLane : laneOf l g = lane) (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs)
    (hStartup : schedulerStartupFrame p l g ⊆ F)
    (hAt : At t 2899 (tileCoordinateFacts p cta first batch lane F))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t) :
    ∃ u v w z,
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) before u ∧
      EStep kernel [] l g u (endpointEvent p batch 0) (some v) ∧
      EStep kernel [] l g v (endpointEvent p batch 1) (some w) ∧ w.pc = 2955 ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) w z ∧
      At z 2958 (outputReadyFacts p l batch (assignedCoordinates p batch cta).2
        (assignedCoordinates p batch cta).1 lane F) := by
  let frame := groupSchedulerFrame p lane F
  have hFrame : ∀ pair ∈ frame, pair.1 ∈ schedulerFrameRegs := by
    intro pair hm
    simp only [frame, groupSchedulerFrame, List.mem_cons] at hm
    rcases hm with rfl | rfl | hm
    · exact of_decide_eq_true rfl
    · exact of_decide_eq_true rfl
    · exact hF pair hm
  have hLaneFact : (1201, b32 lane) ∈ frame := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply hStartup
    simp [schedulerStartupFrame, hLane]
  have hCuQFact : (7502, b64 p.cuQBase) ∈ frame := by
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply hStartup
    simp [schedulerStartupFrame]
  have hPrefix : tilePrefix p first * p.heads + selectedGroupPrefix p first batch =
      tilePrefix p batch * p.heads :=
    precedingGroupWork p hFirst hBatch hGroup
  obtain ⟨u, v, w, z, hLocal, hRead₀, hRead₁, hw, hSetup, hZ⟩ :=
    selectedCoordinatesToReady hp g hBatch hPrefix hLo hHi hl hFrame hLaneFact hCuQFact hAt
  obtain ⟨s, hCoordinates, hs⟩ :=
    computeSelectedTileFramed hp g hBatch hPrefix hLo hHi hFrame t hAt
  have hApproach : run kernel [] l g 4 s = some u := by
    rw [show 54 = 50 + 4 by decide, run_add, hCoordinates, Option.bind_some] at hLocal
    exact hLocal
  have hCoord : run kernel Assumptions.all l g 50 t = some s :=
    coordinateRunTransport (fun hlo hhi => readyModel hlo (by omega)) hCoordinates hAt.1
  have hPre : run kernel Assumptions.all l g 4 s = some u :=
    schedulerLocalTransport (lo := 2949) (len := 4) readApproachStraight
      (fun hlo hhi => readyModel (by omega) (by omega)) hApproach
      (by rw [hs.1]) (by rw [hs.1])
  have hStep₀ := hSteps.trans (run_rtg (run_comp hCoord hPre))
  have hSetup' : run kernel Assumptions.all l g 3 w = some z :=
    schedulerLocalTransport (lo := 2955) (len := 3) readySetupStraight
      (fun hlo hhi => readyModel (by omega) (by omega)) hSetup
      (by rw [hw]) (by rw [hw])
  have hReg := hZ.2.2.2.2
  have hExtra : Holds z.regs frame := hReg.2.2.2.2.2.2.2.2
  have hSaved : Holds z.regs F := hExtra.2.2
  have hInput (pair : Nat × Value) (h : pair ∈ schedulerStartupFrame p l g) :
      z.regs pair.1 = some pair.2 := holds_mem hSaved (hStartup h)
  have hWriteback : Holds z.regs (writebackEntry p l batch (assignedCoordinates p batch cta).2
      (assignedCoordinates p batch cta).1) := by
    exact ⟨hInput (2535, b32 l.sharedBase) (by simp [schedulerStartupFrame]),
      hInput (1178, b32 (l.sharedBase + 68608)) (by simp [schedulerStartupFrame]),
      hInput (2390, b32 (l.sharedBase + 208)) (by simp [schedulerStartupFrame]),
      hInput (6497, b32 (l.sharedBase + 224)) (by simp [schedulerStartupFrame]), hReg.1,
      hInput (7290, .ptr 64 false (.param (param 10)) 0) (by simp [schedulerStartupFrame]),
      hReg.2.1, hReg.2.2.1, hReg.2.2.2.2.2.2.1, trivial⟩
  have hReady : At z 2958 (outputReadyFacts p l batch (assignedCoordinates p batch cta).2
      (assignedCoordinates p batch cta).1 lane F) := by
    apply hZ.mono
    exact (holds_append ..).mpr ⟨hWriteback, hReg.2.2.2.1, holds_mem hExtra hLaneFact,
      hInput (7506, b64 p.cuQBase) (by simp [schedulerStartupFrame]), hExtra.1, hReg.2.2.2.2.1,
      hExtra.2.1, hSaved⟩
  exact ⟨u, v, w, z, hStep₀, hRead₀, hRead₁, hw, run_rtg hSetup', hReady⟩

private theorem readyDemand {o : Option TState} {es : List Event}
    (h : o = none ∨ ContainsTensorStore es) : o = none ∨ es ≠ [] :=
  h.imp_right (fun ⟨_, _, _, hm⟩ eq => by simp [eq] at hm)

/-- A selected lane can enter writeback on a terminated trace or on a prefix already
containing an output issue. The two scalar reads leave every tensor store in the suffix. -/
theorem enterReadyLaneOnThread {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first batch pos lane : Nat} {o : Option TState} {before t : TState}
    {F : List (Nat × Value)} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) (hl : lane < 32) (hLane : laneOf l g = lane)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) (hStartup : schedulerStartupFrame p l g ⊆ F)
    (hReads : ∀ endpoint : Fin 2, CuQWordReadsFromLaunchOnThread p X g (batch + endpoint.val))
    (hAt : At t 2899 (tileCoordinateFacts p cta first batch lane F))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop pos) o)
    (hDemand : o = none ∨ ContainsTensorStore ((X.tr g).drop pos)) :
    ∃ after ready,
      X.get (g, pos) = some (endpointEvent p batch 0) ∧
      X.get (g, pos + 1) = some (endpointEvent p batch 1) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos + 2)) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after ready ∧
      At ready 2958 (outputReadyFacts p l batch (assignedCoordinates p batch cta).2
        (assignedCoordinates p batch cta).1 lane F) ∧
      ∀ pc a (d : TensorStore.Spec), (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop pos →
        (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop (pos + 2) := by
  obtain ⟨u, v, w, z, hStep₀, hRead₀, hRead₁, _, hSetup, hReady⟩ :=
    selectedEndpointPath hp hFirst hGroup hBatch hLo hHi hl hLane hF hStartup hAt hSteps
  obtain ⟨_, hGet₀, hRun₁, hStore₀⟩ :=
    replayEndpoint 0 (hReads 0) hStep₀ hRead₀ hRun (readyDemand hDemand)
  have hDemand' : o = none ∨ ContainsTensorStore ((X.tr g).drop (pos + 1)) :=
    hDemand.imp_right (fun ⟨pc, a, d, hm⟩ => ⟨pc, a, d, hStore₀ pc a d hm⟩)
  obtain ⟨_, hGet₁, hRun₂, hStore₁⟩ :=
    replayEndpoint 1 (hReads 1) .refl hRead₁ hRun₁ (readyDemand hDemand')
  refine ⟨w, z, hGet₀, hGet₁, ?_, hSetup, hReady, ?_⟩
  · simpa only [Nat.add_assoc] using hRun₂
  · intro pc a d hm
    simpa only [Nat.add_assoc] using hStore₁ pc a d (hStore₀ pc a d hm)

/-- Apply the scoped proof when every CuQ read agrees with the launch. -/
theorem enterReadyLane {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g cta first batch pos lane : Nat} {o : Option TState} {before t : TState}
    {F : List (Nat × Value)} (hFirst : first ≤ batch) (hGroup : batch < first + 31)
    (hBatch : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch + 1) * p.heads) (hl : lane < 32) (hLane : laneOf l g = lane)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) (hStartup : schedulerStartupFrame p l g ⊆ F)
    (hReads : ∀ endpoint : Fin 2, CuQWordReadsFromLaunch p X (batch + endpoint.val))
    (hAt : At t 2899 (tileCoordinateFacts p cta first batch lane F))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before t)
    (hRun : Run kernel Assumptions.all l g before ((X.tr g).drop pos) o)
    (hDemand : o = none ∨ ContainsTensorStore ((X.tr g).drop pos)) :
    ∃ after ready,
      X.get (g, pos) = some (endpointEvent p batch 0) ∧
      X.get (g, pos + 1) = some (endpointEvent p batch 1) ∧
      Run kernel Assumptions.all l g after ((X.tr g).drop (pos + 2)) o ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) after ready ∧
      At ready 2958 (outputReadyFacts p l batch (assignedCoordinates p batch cta).2
        (assignedCoordinates p batch cta).1 lane F) ∧
      ∀ pc a (d : TensorStore.Spec), (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop pos →
        (⟨pc, .tensorStore a d⟩ : Event) ∈ (X.tr g).drop (pos + 2) :=
  enterReadyLaneOnThread hp hFirst hGroup hBatch hLo hHi hl hLane hF hStartup
    (fun endpoint => (hReads endpoint).onThread g) hAt hSteps hRun hDemand

/-- The two chosen cuQ loads are actual events in every lane. At their common successor,
the selected tile's writeback operands and the unchanged warp ordinals are available. -/
theorem SchedulerWarpAt.enterWriteback {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g cta first batch shuffles votes : Nat}
    (hg : g < l.threads) {F : Nat → List (Nat × Value)}
    (cur : SchedulerWarpAt l X g 2899
      (fun lane => tileCoordinateFacts p cta first batch lane (F lane)) shuffles votes)
    (hFirst : first ≤ batch) (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ cta) (hHi : cta < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ∈ schedulerFrameRegs)
    (hStartup : ∀ lane < 32, schedulerStartupFrame p l (warpLane l g lane) ⊆ F lane)
    (hProtected : ∀ endpoint : Fin 2, ∀ k < 4, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers ((globalLoc (p.cuQBase + 4 * (batch + endpoint.val))).at k)) :
    let coords := assignedCoordinates p batch cta
    ∃ ready : SchedulerWarpAt l X g 2958
        (fun lane => outputReadyFacts p l batch coords.2 coords.1 lane (F lane)) shuffles votes,
      ∀ lane < 32, ready.pos lane = cur.pos lane + 2 := by
  dsimp only
  let thread := warpLane l g
  let coords := assignedCoordinates p batch cta
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLanes (lane : Nat) (hl : lane < 32) :
      ∃ after ready,
        X.get (thread lane, cur.pos lane) = some (endpointEvent p batch 0) ∧
        X.get (thread lane, cur.pos lane + 1) = some (endpointEvent p batch 1) ∧
        Run kernel Assumptions.all l (thread lane) after
          ((X.tr (thread lane)).drop (cur.pos lane + 2)) none ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) after ready ∧
        At ready 2958 (outputReadyFacts p l batch coords.2 coords.1 lane (F lane)) := by
    obtain ⟨after, ready, h₀, h₁, hr, ht, hAt, _⟩ :=
      enterReadyLane hp hFirst hGroup hBatch hLo hHi hl (Step.sameWarp_lane hBlock hg hl).2
        (hF lane hl) (hStartup lane hl)
        (fun endpoint => cuQWordReadsFromLaunchOfProtected hp hX
          (by have := endpoint.isLt; omega) (hProtected endpoint))
        (cur.checkpoint lane hl)
        (cur.localSteps lane hl) (cur.continuation lane hl) (.inl rfl)
    exact ⟨after, ready, h₀, h₁, hr, ht, hAt⟩
  let _ : Nonempty TState := ⟨cur.state 0⟩
  choose! after ready hGet₀ hGet₁ hRun hLocal hAt using hLanes
  let reads := [endpointEvent p batch 0, endpointEvent p batch 1]
  have hPrefix (lane : Nat) (hl : lane < 32) :
      (X.tr (thread lane)).drop (cur.pos lane) =
        reads ++ (X.tr (thread lane)).drop (cur.pos lane + 2) := by
    have h₀ := List.getElem?_eq_some_iff.mp (hGet₀ lane hl)
    have h₁ := List.getElem?_eq_some_iff.mp (hGet₁ lane hl)
    rw [List.drop_eq_getElem_cons h₀.1, h₀.2, List.drop_eq_getElem_cons h₁.1, h₁.2]
    rfl
  have hCounts := cur.ordinals.advance (fun _ => reads)
    (fun lane hl => ⟨_, hPrefix lane hl⟩) (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨⟨fun lane => cur.pos lane + 2, after, ready, hCounts, hRun, hLocal, hAt⟩, fun _ _ => rfl⟩

/-- The writeback transition needs only the issue operands of the ready state. -/
theorem outputReady_writebackAt {l : Launch} {batch head tile lane : Nat} {t : TState}
    {F : List (Nat × Value)} (h : At t 2958 (outputReadyFacts p l batch head tile lane F)) :
    At t 2958 (writebackEntry p l batch head tile) :=
  h.mono ((holds_append ..).mp h.2.2.2.2).1

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
