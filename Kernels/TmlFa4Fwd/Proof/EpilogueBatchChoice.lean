-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.EpilogueSelectionPath
public import Lemmas.Flow.Determinism

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Batch scan and startup registers which the availability check leaves live. -/
def groupAvailabilityRegs : List Nat := [7222, 7221, 7224, 7223, 7220, 7228] ++ schedulerFrameRegs

private theorem availabilityRegsCode :
    ((kernel.code.drop 2878).take 5).all
      (fun ins => groupAvailabilityRegs.all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem availabilityStraightCode :
    ((kernel.code.drop 2878).take 4).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The availability check reaches the ballot or the exhausted branch and preserves the scan. -/
theorem groupAvailabilityFramed (l : Launch) (g : Nat) {first batch : Nat}
    {t : TState} {F : List (Nat × Value)}
    (hFirst : first < 2 ^ 31) (hBatch : batch < 2 ^ 31)
    (hF : ∀ pair ∈ F, pair.1 ∈ groupAvailabilityRegs)
    (hStart : (7223, b32 first) ∈ F) (hCount : (7228, b32 batch) ∈ F)
    (ht : At t 2878 F) :
    ∃ u, run kernel [] l g 5 t = some u ∧
      At u (if batch ≤ first then 2947 else 2883) ((782, .pred false) :: F) := by
  obtain ⟨u, hRun, hu⟩ := groupAvailability l g hFirst hBatch t
    (ht.mono ⟨holds_mem ht.2.2.2.2 hStart, holds_mem ht.2.2.2.2 hCount, trivial⟩)
  have hKeep := holdsSchedulerFrame ht.2.2.2.2
    (fun _ hr => schedulerLocalFrame availabilityRegsCode availabilityStraightCode hRun
      (by rw [ht.1]) (by rw [ht.1]) hr) hF
  exact ⟨u, hRun, hu.mono ⟨hu.2.2.2.2.1, hKeep⟩⟩

/-- An exhausted scan exits warp 13 directly from the scheduler. -/
theorem noAssignedRequest (l : Launch) (g : Nat) {first batch : Nat} {t : TState}
    (hFirst : first < 2 ^ 31) (hBatch : batch < 2 ^ 31) (hEnd : batch ≤ first)
    (ht : At t 2878 [(7223, b32 first), (7228, b32 batch), (1062, b32 13)]) :
    Run kernel [] l g t [⟨Flow.exit_0, .exit⟩] none := by
  obtain ⟨u, hRun, hu⟩ := groupAvailabilityFramed l g hFirst hBatch
    (by
      intro pair hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> simp [groupAvailabilityRegs, schedulerFrameRegs])
    (by simp) (by simp) ht
  have hPc : u.pc = 2947 := by simpa only [ite_eq_left hEnd] using hu.1
  let v := { next (setReg u 306 (.pred true)) with pc := 3099 }
  have hv : run kernel [] l g 2 u = some v :=
    selectedBranch l g u false hPc hu.2.2.2.1 hu.2.2.2.2.1
  have hWarp : v.regs 1062 = some (.bits 32 13) := by
    simpa [v, next, setReg, b32] using hu.2.2.2.2.2.2.2.1
  obtain ⟨w, hFinish, hExit, hOut⟩ := finishScheduler l g v rfl hu.2.2.2.1 hWarp
  exact .last (run_rtg (run_comp (run_comp hRun hv) hFinish)) ⟨.exit, hOut, by rw [hExit], rfl⟩

/-- Untouched group and startup operands before the batch ballot. -/
def ballotRegs : List Nat := [7223, 7220, 7221] ++ schedulerFrameRegs

/-- The ballot's continuation also carries the group's starting work index. -/
def popcountRegs : List Nat := 1207 :: ballotRegs

private theorem ballotRegsCode :
    ((kernel.code.drop 2883).take 4).all
      (fun ins => ballotRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem ballotStraightCode :
    ((kernel.code.drop 2883).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem popcountRegsCode :
    ((kernel.code.drop 2888).take 4).all
      (fun ins => popcountRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem popcountStraightCode :
    ((kernel.code.drop 2888).take 3).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

variable {p : Params}

/-- The group comparison is replayed under the actual scheduler assumptions and its live facts
are available at the ballot instruction. -/
theorem prepareGroupVote {l : Launch} {m : Mem0} (hp : Pre p l m) {A : List Assumption} (g : Nat)
    {first batch item : Nat} {t : TState} {F : List (Nat × Value)} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ item) (hHi : item < tilePrefix p (batch + 1) * p.heads)
    (hModel : ∀ {s : TState}, 2883 ≤ s.pc → s.pc < 2887 → out kernel A l g s = out kernel [] l g s)
    (hF : ∀ pair ∈ F, pair.1 ∈ ballotRegs) :
    let lane := laneOf l g
    At t 2883 ([(7222, b32 (∑ j ∈ Finset.range 32, groupLaneTiles p first j)),
      (7221, b32 (∑ j ∈ Finset.range (lane + 1), groupLaneTiles p first j)),
      (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
      (7138, b32 p.heads), (1072, b32 item)] ++ F) →
    ∃ u, run kernel A l g 4 t = some u ∧
      At u 2887 ([(1207, b32 (tilePrefix p first * p.heads)),
        (293, .pred (decide (first + lane < batch)))] ++ F) := by
  dsimp only
  intro ht
  obtain ⟨hArgs, hFrame⟩ := (holds_append ..).mp ht.2.2.2.2
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨u, hRun, hu⟩ := selectedGroupBallot hp g hFirst hGroup hBatch hl hLo hHi t (ht.mono hArgs)
  have hLoPc : 2883 ≤ t.pc := ht.1.ge
  have hHiPc : t.pc + 4 ≤ 2883 + 4 := by rw [ht.1]
  have hKeep := holdsSchedulerFrame hFrame
    (fun _ hr => schedulerLocalFrame ballotRegsCode ballotStraightCode hRun hLoPc hHiPc hr) hF
  have hActual := schedulerLocalTransport (A := A) (lo := 2883) (len := 4)
    ballotStraightCode hModel hRun hLoPc hHiPc
  exact ⟨u, hActual, hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2, hKeep⟩)⟩

/-- The ballot's actual word drives the popcount and leaves the selection's frame live. -/
theorem finishGroupVote {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel A m X) {g i ordinal first batch : Nat} {t : TState}
    {F : List (Nat × Value)} {word : BitVec 32} {hit : Bool} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hModel : ∀ {s : TState}, 2888 ≤ s.pc → s.pc < 2892 → out kernel A l g s = out kernel [] l g s)
    (hF : ∀ pair ∈ F, pair.1 ∈ popcountRegs) (hFirstFact : (7223, b32 first) ∈ F)
    (ht : At t 2887 ((293, .pred hit) :: F))
    (he : X.get (g, i) = some ⟨2887, .vote (2 ^ 32 - 1) hit word⟩)
    (hOrdinal : X.MaskK voteClass (g, i) (2 ^ 32 - 1) ordinal)
    (hPeers : ∀ j < 32, ∃ k val,
      let e := (g - laneOf l g + j, k)
      X.get e = some ⟨2887, .vote (2 ^ 32 - 1) (decide (first + j < batch)) val⟩ ∧
        X.MaskK voteClass e (2 ^ 32 - 1) ordinal) :
    let u := next (setReg t 2352 (b32 word.toNat))
    ∃ v, run kernel A l g 4 u = some v ∧
      At v 2892 ([(1208, b32 (batch - first)), (7228, b32 batch),
        (294, .pred (decide (batch = first))), (7225, b32 0)] ++ F) := by
  dsimp only
  let u := next (setReg t 2352 (b32 word.toNat))
  have ht' : At t 2887 [(293, .pred hit), (7223, b32 first)] :=
    ht.mono ⟨ht.2.2.2.2.1, holds_mem ht.2.2.2.2.2 hFirstFact, trivial⟩
  obtain ⟨v, _, hRun, hv⟩ :=
    selectedGroupPopcountObserved hp hX t hit word hFirst hGroup hBatch ht' he hOrdinal hPeers
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 2352 := by
    intro pair hm eq
    have hBad : 2352 ∈ popcountRegs := eq ▸ hF pair hm
    exact (of_decide_eq_true (by decide : decide (2352 ∉ popcountRegs) = true)) hBad
  have hu : At u 2888 ((2352, b32 word.toNat) :: F) := (ht.mono ht.2.2.2.2.2).set hFresh
  have hLoPc : 2888 ≤ u.pc := hu.1.ge
  have hHiPc : u.pc + 4 ≤ 2888 + 4 := by rw [hu.1]
  have hKeep := holdsSchedulerFrame hu.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame popcountRegsCode popcountStraightCode hRun hLoPc hHiPc hr) hF
  have hActual := schedulerLocalTransport (A := A) (lo := 2888) (len := 4)
    popcountStraightCode hModel hRun hLoPc hHiPc
  exact ⟨v, hActual, hv.mono ((holds_append ..).mpr ⟨hv.2.2.2.2, hKeep⟩)⟩

/-- The ballot and indexed exchanges recover all inputs of the decoded tile calculation. -/
theorem chooseBatch {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) {g i ballotOrdinal first batch item : Nat} {t : TState}
    {F : List (Nat × Value)} {word : BitVec 32} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ item) (hHi : item < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) :
    let n := batch - first
    let lane := laneOf l g
    let count := groupLaneTiles p first
    let part := fun j => ∑ k ∈ Finset.range (j + 1), count k
    let start := tilePrefix p first * p.heads
    let prev := (∑ j ∈ Finset.range n, count j) * p.heads
    let voteEv := ⟨2887, .vote (2 ^ 32 - 1) (decide (first + lane < batch)) word⟩
    At t 2883 ([(7222, b32 (∑ j ∈ Finset.range 32, count j)), (7221, b32 (part lane)),
      (7224, b32 (tilePrefix p (min p.batch (first + 31)) * p.heads)),
      (7138, b32 p.heads), (1072, b32 item), (7223, b32 first), (7220, b32 (count lane))] ++ F) →
    X.get (g, i) = some voteEv →
    X.MaskK voteClass (g, i) (2 ^ 32 - 1) ballotOrdinal →
    (∀ j < 32, ∃ k val,
      X.get (g - lane + j, k) = some ⟨2887, .vote (2 ^ 32 - 1) (decide (first + j < batch)) val⟩ ∧
        X.MaskK voteClass (g - lane + j, k) (2 ^ 32 - 1) ballotOrdinal) →
    (first < batch → IndexedSchedulerShuffle X l g 2894 (n - 1)
      (b32 (part lane)) (b32 (part (n - 1)))) →
    (finish : IndexedSchedulerShuffle X l g 2898 n (b32 (count lane)) (b32 (count n))) →
    ∃ events u, Run kernel [] l g t (voteEv :: events) (some u) ∧
      At u 2899 ([(1207, b32 start), (7225, b32 prev), (1072, b32 item),
        (2355, b32 (requestTiles p batch)), (7138, b32 p.heads), (7155, b32 800),
        (7146, b32 p.batch), (7228, b32 batch)] ++ F) ∧
      events.getLast? = X.get (g, finish.eventIndex) := by
  dsimp only
  intro hAt hEvent hOrdinal hPeers hPrevious finish
  let n := batch - first
  let lane := laneOf l g
  let count := groupLaneTiles p first
  let part := fun j => ∑ k ∈ Finset.range (j + 1), count k
  let start := tilePrefix p first * p.heads
  let carrier := [(7221, b32 (part lane)), (7138, b32 p.heads), (1072, b32 item),
    (7223, b32 first), (7220, b32 (count lane))] ++ F
  let carry := (1207, b32 start) :: carrier
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hCarrier : ∀ pair ∈ carrier, pair.1 ∈ ballotRegs := by
    intro pair hm
    simp only [carrier, List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | hm
    all_goals first
      | exact List.mem_append.mpr (.inr (hF pair hm))
      | simp [ballotRegs, schedulerFrameRegs]
  have hCarry : ∀ pair ∈ carry, pair.1 ∈ popcountRegs := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [popcountRegs]
    · exact List.mem_cons_of_mem _ (hCarrier pair hm)
  obtain ⟨v, hLocal, hv⟩ := selectedGroupBallot hp g hFirst hGroup hBatch hLane hLo hHi t
    (hAt.mono ⟨hAt.2.2.2.2.1, hAt.2.2.2.2.2.1, hAt.2.2.2.2.2.2.1,
      hAt.2.2.2.2.2.2.2.1, hAt.2.2.2.2.2.2.2.2.1, trivial⟩)
  have hInitial : Holds t.regs carrier := by
    have h := hAt.2.2.2.2
    exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  have hPreserve := holdsSchedulerFrame hInitial
    (fun _ hr => schedulerLocalFrame ballotRegsCode ballotStraightCode hLocal
      (by rw [hAt.1]) (by rw [hAt.1]) hr) hCarrier
  have hAtBallot : At v 2887 [(293, .pred (decide (first + lane < batch))), (7223, b32 first)] :=
    hv.mono ⟨hv.2.2.2.2.2.1, holds_mem hPreserve (by simp [carrier]), trivial⟩
  obtain ⟨w, hVote, hPop, hw⟩ := selectedGroupPopcountObserved hp hX v _ word
    hFirst hGroup hBatch hAtBallot hEvent hOrdinal hPeers
  let v' := next (setReg v 2352 (b32 word.toNat))
  have hCarryV : At v 2887 carry := hv.mono ⟨hv.2.2.2.2.1, hPreserve⟩
  have hUntouched : ∀ pair ∈ carry, pair.1 ≠ 2352 := by
    intro pair hm
    have hReg := hCarry pair hm
    simp only [popcountRegs, ballotRegs, schedulerFrameRegs, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hReg
    omega
  have hAfterVote : At v' 2888 ((2352, b32 word.toNat) :: carry) := hCarryV.set hUntouched
  have hFinalCarry := holdsSchedulerFrame hAfterVote.2.2.2.2.2
    (fun _ hr => schedulerLocalFrame popcountRegsCode popcountStraightCode hPop
      (by rw [hAfterVote.1]) (by rw [hAfterVote.1]) hr) hCarry
  let regs := [(1207, b32 start), (1072, b32 item), (7138, b32 p.heads), (7228, b32 batch)] ++ F
  have hRegs : Holds w.regs regs := by
    refine ⟨hFinalCarry.1, holds_mem hFinalCarry (by simp [carry, carrier]),
      holds_mem hFinalCarry (by simp [carry, carrier]), hw.2.2.2.2.2.1, ?_⟩
    exact hFinalCarry.2.2.2.2.2.2
  have hReady : At w 2892 ([(294, .pred (decide (batch = first))), (7225, b32 0),
      (1208, b32 n), (7220, b32 (count lane)), (7221, b32 (part lane))] ++ regs) :=
    hw.mono ⟨hw.2.2.2.2.2.2.1, hw.2.2.2.2.2.2.2.1, hw.2.2.2.2.1,
      holds_mem hFinalCarry (by simp [carry, carrier]),
      holds_mem hFinalCarry (by simp [carry, carrier]), hRegs⟩
  have hFresh : ∀ pair ∈ regs, pair.1 ≠ 2353 ∧ pair.1 ≠ 2354 ∧ pair.1 ≠ 7225 ∧
      pair.1 ≠ 7146 ∧ pair.1 ≠ 7155 ∧ pair.1 ≠ 2355 := by
    intro pair hm
    simp only [regs, List.cons_append, List.nil_append, List.mem_cons] at hm
    rcases hm with rfl | rfl | rfl | rfl | hm <;> first
      | exact of_decide_eq_true rfl
      | have hReg := hF pair hm
        simp only [schedulerFrameRegs, List.mem_cons, List.not_mem_nil, or_false] at hReg
        omega
  obtain ⟨events, u, hTail, hu, hLast⟩ :=
    selectedRequestPath hp hX hFirst hGroup hBatch hFresh (by simp [regs])
      hReady hPrevious finish
  have hTail' : Run kernel [] l g v' events (some u) := by
    cases events with
    | nil => rw [finish.event] at hLast; cases hLast
    | cons event events =>
      cases hTail with
      | step hs he hr => exact .step ((run_rtg hPop).trans hs) he hr
  refine ⟨events, u, .step (run_rtg hLocal) hVote hTail', hu.mono ?_, hLast⟩
  have h := hu.2.2.2.2
  exact ⟨h.2.2.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.1, h.2.2.2.2.2.2.1,
    h.2.2.1, h.2.1, h.2.2.2.2.2.2.2⟩

/-- Continue a selected batch trace through the decoded coordinate arithmetic and exact
cuQ endpoint reads, placing the thread at the first output poll. -/
theorem chosenBatchToReady {l : Launch} {m : Mem0} (hp : Pre p l m) {g first batch item : Nat}
    {t s : TState} {events : List Event} {F : List (Nat × Value)} (hFirst : first ≤ batch)
    (hGroup : batch < first + 31) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ item) (hHi : item < tilePrefix p (batch + 1) * p.heads)
    (hF : ∀ pair ∈ F, pair.1 ∈ schedulerFrameRegs) (hLane : (1201, b32 (laneOf l g)) ∈ F)
    (hCuQ : (7502, b64 p.cuQBase) ∈ F) (hTrace : Run kernel [] l g t events (some s)) :
    let start := tilePrefix p first * p.heads
    let prev := (∑ j ∈ Finset.range (batch - first), groupLaneTiles p first j) * p.heads
    let pos := assignedCoordinates p batch item
    let e0 := ⟨2953, .rd { loc := globalLoc (p.cuQBase + 4 * batch), size := 4 }
      ((b32 (p.qOffset batch)).toBytes.map some)⟩
    let e1 := ⟨2954, .rd { loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4 }
      ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩
    At s 2899 ([(1207, b32 start), (7225, b32 prev), (1072, b32 item),
      (2355, b32 (requestTiles p batch)), (7138, b32 p.heads), (7155, b32 800),
      (7146, b32 p.batch), (7228, b32 batch)] ++ F) →
    ∃ u v, Run kernel [] l g t (events ++ [e0, e1]) (some u) ∧
      run kernel [] l g 3 u = some v ∧
      At v 2958 ([(7229, b32 0), (2395, b32 (2 ^ 30 - p.qLength batch + 256 * pos.1)),
        (2393, b32 (p.qOffset (batch + 1))), (307, .pred (decide (p.batch < laneOf l g))),
        (7147, b32 p.batch), (7228, b32 batch), (7227, b32 pos.2),
        (7226, b32 (2 ^ 30 + 256 * pos.1))] ++ F) := by
  dsimp only
  intro hs
  have hi : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨a, b, c, d, hLocal, hRead0, hRead1, _, hEnd, hd⟩ :=
    selectedCoordinatesToReady hp g hBatch (precedingGroupWork p hFirst hBatch hGroup) hLo hHi
      hi hF hLane hCuQ hs
  have h0 := hTrace.snoc (run_rtg hLocal) hRead0
  have h1 := h0.snoc Relation.ReflTransGen.refl hRead1
  exact ⟨c, d, by simpa only [List.append_assoc, List.singleton_append] using h1, hEnd, hd⟩

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
