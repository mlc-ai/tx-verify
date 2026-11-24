-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.EpilogueGroup
public import Kernels.TmlFa4Fwd.Proof.SchedulerScanObservations
public import Lemmas.Flow.WarpScan

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Startup registers carried through the first pass, before the gate and head count are set. -/
def firstPassRegs : List Nat :=
  7228 :: schedulerFrameRegs.filter (fun r => r != 268 && r != 7138)

/-- cuQ lanes beyond the batch sentinel have the prologue's initialized zero. -/
def firstPassOffset (p : Params) (lane : Nat) : Nat :=
  if lane ≤ p.batch then p.qOffset lane else 0

variable {p : Params} {l : Launch} {m : Mem0}

theorem firstPassOffset_bound (hp : Pre p l m) (lane : Nat) : firstPassOffset p lane < 2 ^ 30 := by
  have hTotal := hp.shape.2.2.2.2.2
  by_cases h : lane ≤ p.batch
  · rw [firstPassOffset, ite_eq_left h]
    have := hp.qOffset_le_total h
    omega
  · simp [firstPassOffset, h]

private theorem firstGateWrites :
    ((kernel.code.drop 2778).take 6).all
      (fun ins => firstPassRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstGateStraight :
    ((kernel.code.drop 2778).take 5).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstCountWrites :
    ((kernel.code.drop 2785).take 11).all
      (fun ins => (268 :: firstPassRegs).all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstCountStraight :
    ((kernel.code.drop 2785).take 10).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstBranchStraight :
    ((kernel.code.drop 2784).take (1 - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true := rfl

/-- The entry count, request predicate and head parameter reach the first up-shuffle.
The result runs under any model that agrees with Core at these decoded PCs. -/
theorem firstPassPrelude (hp : Pre p l m) {A : List Assumption} (g : Nat) {t : TState}
    {F : List (Nat × Value)}
    (hModel : ∀ {s : TState}, 2778 ≤ s.pc → s.pc < 2796 → out kernel A l g s = out kernel [] l g s)
    (hF : ∀ pair ∈ F, pair.1 ∈ firstPassRegs) :
    let lane := laneOf l g
    let begin := firstPassOffset p lane
    let finish := firstPassOffset p (if lane < 31 then lane + 1 else lane)
    let eligible := laneHasRequest lane p.batch
    At t 2778 ([(1201, b32 lane), (7228, b32 p.batch), (7217, b32 begin),
      (2308, b32 finish)] ++ F) →
    ∃ u, run kernel A l g (if eligible then 18 else 8) t = some u ∧
      At u 2796 ([(7220, b32 (groupLaneTiles p 0 lane)), (7138, b32 p.heads),
        (268, .pred (!decide eligible))] ++ F) := by
  dsimp only
  intro ht
  let lane := laneOf l g
  let begin := firstPassOffset p lane
  let finish := firstPassOffset p (if lane < 31 then lane + 1 else lane)
  let eligible := laneHasRequest lane p.batch
  let pred : Nat × Value := (268, .pred (!decide eligible))
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hBatch := hp.shape.2.1
  have hBegin := firstPassOffset_bound hp lane
  have hFinish := firstPassOffset_bound hp (if lane < 31 then lane + 1 else lane)
  have hMono : eligible → begin ≤ finish := by
    rintro ⟨hb, hs⟩
    simpa [begin, finish, firstPassOffset, hb.le, hs, show lane + 1 ≤ p.batch by omega] using
      (hp.lengths lane hb).1
  have hLength : finish - begin < 2 ^ 30 := lt_of_le_of_lt (Nat.sub_le ..) hFinish
  have hCount :
      (if eligible then (finish - begin + 255) / 256 else 0) = groupLaneTiles p 0 lane := by
    by_cases h : eligible
    · obtain ⟨hb, hs⟩ := h
      simp [groupLaneTiles, eligible, hb, hs, requestTiles, Params.qLength, begin, finish,
        firstPassOffset, hb.le, show lane + 1 ≤ p.batch by omega]
    · have hn : ¬ (lane < 31 ∧ lane < p.batch) := fun hh => h ⟨hh.2, hh.1⟩
      simp [groupLaneTiles, h, hn]
  obtain ⟨hInput, hFrame⟩ := (holds_append ..).mp ht.2.2.2.2
  let params := [(1201, b32 lane), (7228, b32 p.batch), (7217, b32 begin), (2308, b32 finish)]
  have hInputAt : At t 2778 params := ht.mono hInput
  obtain ⟨gate, hGate, hg⟩ := firstTileGate l g hLane hBatch (by omega) (by omega) t hInputAt
  have hGateKeep := holdsSchedulerFrame hFrame
    (fun _ hr => schedulerLocalFrame firstGateWrites firstGateStraight hGate
      (by rw [ht.1]) (by rw [ht.1]) hr) hF
  have hPred : At gate 2784 (pred :: F) := hg.mono ⟨hg.2.2.2.2.2.2.1, hGateKeep⟩
  obtain ⟨entry, hEntry, he⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2784 _ hPred hPred.2.2.2.2.1 (by simp)
  obtain ⟨count, hCountRun, hc⟩ :=
    firstLaneTiles l g hLane hBatch (by omega) (by omega) hMono hLength t hInputAt
  have hc' : At count 2795 [(7220, b32 (groupLaneTiles p 0 lane))] := hCount ▸ hc
  obtain ⟨u, hHead, hu⟩ := firstScanHeadCount hp g _ count hc'
  have hGateA := schedulerLocalTransport (A := A) (lo := 2778) (len := 6) firstGateStraight
    (fun hlo hhi => hModel hlo (by omega)) hGate (by rw [ht.1]) (by rw [ht.1])
  have hEntryA := schedulerLocalTransport (A := A) (lo := 2784) (len := 1) firstBranchStraight
    (fun hlo hhi => hModel (by omega) (by omega)) hEntry (by rw [hPred.1]) (by rw [hPred.1])
  have hFrameEntry : ∀ pair ∈ pred :: F, pair.1 ∈ 268 :: firstPassRegs := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [pred]
    · exact List.mem_cons_of_mem _ (hF pair hm)
  have hPrefix := run_comp hGate hEntry
  have hPrefixA := run_comp hGateA hEntryA
  have complete {n : Nat} (hr : run kernel [] l g n entry = some u)
      (hLo : 2785 ≤ entry.pc) (hHi : entry.pc + n ≤ 2796) :
      run kernel A l g n entry = some u ∧
        At u 2796 ([(7220, b32 (groupLaneTiles p 0 lane)), (7138, b32 p.heads),
          (268, .pred (!decide eligible))] ++ F) := by
    have hKeep := holdsSchedulerFrame he.2.2.2.2
      (fun _ hr' => schedulerLocalFrame firstCountWrites firstCountStraight hr hLo hHi hr')
      hFrameEntry
    have hRunA := schedulerLocalTransport (A := A) (lo := 2785) (len := 11) firstCountStraight
      (fun hlo hhi => hModel (by omega) hhi) hr hLo hHi
    exact ⟨hRunA, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.1, hKeep⟩⟩
  by_cases h : eligible
  · have hpEntry : entry.pc = 2785 := by simpa [eligible, h] using he.1
    have hr : run kernel [] l g 10 entry = some count := by
      rw [show (if eligible then 17 else 7) = 7 + 10 by simp [h], run_add, hPrefix,
        Option.bind_some] at hCountRun
      exact hCountRun
    obtain ⟨hLocal, hAt⟩ := complete (run_comp hr hHead) (by rw [hpEntry]) (by rw [hpEntry])
    refine ⟨u, ?_, hAt⟩
    change run kernel A l g (if eligible then 18 else 8) t = some u
    simpa only [h, ↓reduceIte] using run_comp hPrefixA hLocal
  · have hpEntry : entry.pc = 2795 := by simpa [eligible, h] using he.1
    have hSame : count = entry := Option.some.inj ((by
      simpa [eligible, h] using hCountRun : run kernel [] l g 7 t = some count).symm.trans hPrefix)
    subst count
    obtain ⟨hLocal, hAt⟩ := complete hHead (by rw [hpEntry]; decide) (by rw [hpEntry])
    refine ⟨u, ?_, hAt⟩
    change run kernel A l g (if eligible then 18 else 8) t = some u
    simpa only [h, ↓reduceIte] using run_comp hPrefixA hLocal

/-- The inputs shared by all rounds and by the first group-bound test. -/
def firstPassFrameRegs : List Nat := 7220 :: 7138 :: 268 :: firstPassRegs

private theorem firstPassRoundWrites (stage : Fin 5) :
    ((kernel.code.drop (firstScanPc stage + 1)).take 3).all
      (fun ins => firstPassFrameRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    fin_cases stage <;> kernel_rfl

private theorem firstPassRoundStraight (stage : Fin 5) :
    ((kernel.code.drop (firstScanPc stage + 1)).take 2).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    fin_cases stage <;> kernel_rfl

/-- The local part of an actual up-shuffle round doubles the verified prefix window. -/
theorem firstPassFold (hp : Pre p l m) {A : List Assumption} (g : Nat) (stage : Fin 5) {t : TState}
    {F : List (Nat × Value)}
    (hModel : ∀ {s : TState}, firstScanPc stage + 1 ≤ s.pc → s.pc < firstScanPc stage + 4 →
      out kernel A l g s = out kernel [] l g s) (hF : ∀ pair ∈ F, pair.1 ∈ firstPassFrameRegs) :
    let lane := laneOf l g
    let source := (shflSource .up lane (2 ^ stage.val) 0).1
    let part := prefixWindow (groupLaneTiles p 0) (2 ^ stage.val)
    At t (firstScanPc stage + 1) ([(1201, b32 lane),
      (firstScanSrc stage, b32 (part lane)), (firstScanDst stage, b32 (part source))] ++ F) →
    ∃ u, run kernel A l g 3 t = some u ∧ At u (firstScanPc stage + 4)
      ((firstScanResult stage, b32 (prefixWindow (groupLaneTiles p 0) (2 * 2 ^ stage.val) lane)) ::
        F) := by
  dsimp only
  intro ht
  have hl : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨hArgs, hFrame⟩ := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u, hRun, hu⟩ := firstScanFold stage l g (groupLaneTiles p 0) hl
    (groupPrefixOperands_fit hp (Nat.zero_le p.batch) hl stage) t (ht.mono hArgs)
  have hLo : firstScanPc stage + 1 ≤ t.pc := ht.1.ge
  have hHi : t.pc + 3 ≤ firstScanPc stage + 1 + 3 := by rw [ht.1]
  have hKeep := holdsSchedulerFrame hFrame
    (fun _ hr => schedulerLocalFrame (firstPassRoundWrites stage) (firstPassRoundStraight stage)
      hRun hLo hHi hr) hF
  have hRunA := schedulerLocalTransport (A := A)
    (lo := firstScanPc stage + 1) (len := 3) (firstPassRoundStraight stage)
    (fun hlo hhi => hModel hlo (by omega)) hRun hLo hHi
  exact ⟨u, hRunA, hu.mono ⟨hu.2.2.2.2.1, hKeep⟩⟩

/-- The per-lane and warp-total prefix words are live across the cutoff check. -/
def firstPassLimitRegs : List Nat := 7221 :: 7222 :: firstPassFrameRegs

private theorem firstPassLimitWrites :
    ((kernel.code.drop 2817).take 3).all
      (fun ins => firstPassLimitRegs.all (fun r => !(writesRegs ins.op).contains r)) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

private theorem firstPassLimitStraight :
    ((kernel.code.drop 2817).take 2).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The lane-31 scan total establishes exactly the first CTA cutoff. -/
theorem firstPassLimit (hp : Pre p l m) {A : List Assumption} (g : Nat) {cta : Nat} {t : TState}
    {F : List (Nat × Value)} (hCta : cta < 2 ^ 31)
    (hModel : ∀ {s : TState}, 2817 ≤ s.pc → s.pc < 2820 → out kernel A l g s = out kernel [] l g s)
    (hF : ∀ pair ∈ F, pair.1 ∈ firstPassLimitRegs) :
    let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p 0 lane
    let limit := tilePrefix p (min p.batch 31) * p.heads
    At t 2817 ([(7222, b32 count), (7138, b32 p.heads), (1072, b32 cta)] ++ F) →
    ∃ u, run kernel A l g 3 t = some u ∧ At u 2820
      ([(7224, b32 limit), (277, .pred (decide (cta < limit))), (7223, b32 0)] ++ F) := by
  dsimp only
  intro ht
  let count := ∑ lane ∈ Finset.range 32, groupLaneTiles p 0 lane
  have hGroup : count = tilePrefix p (min p.batch 31) := by
    simpa [tilePrefix] using groupTiles_eq p (Nat.zero_le p.batch) (by decide : 32 ≤ 32)
  have hCut := hp.prefixWork_signed (Nat.min_le_left p.batch 31)
  have hWork : count * p.heads < 2 ^ 31 := by rw [hGroup]; exact hCut
  have hPos : 0 < p.heads := by
    unfold Params.heads
    have := hp.shape.2.2.1
    omega
  have hCount := lt_of_le_of_lt (Nat.le_mul_of_pos_right count hPos) hWork
  obtain ⟨hArgs, hFrame⟩ := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨u, hRun, hu⟩ := firstGroupLimit l g hCount hp.heads_signed hCta hWork t
    (ht.mono hArgs)
  have hKeep := holdsSchedulerFrame hFrame
    (fun _ hr => schedulerLocalFrame firstPassLimitWrites firstPassLimitStraight hRun
      (by rw [ht.1]) (by rw [ht.1]) hr) hF
  have hRunA := schedulerLocalTransport (A := A) (lo := 2817) (len := 3)
    firstPassLimitStraight hModel hRun (by rw [ht.1]) (by rw [ht.1])
  refine ⟨u, hRunA, hu.mono ?_⟩
  apply (holds_append ..).mpr
  refine ⟨?_, hKeep⟩
  simpa only [hGroup] using hu.2.2.2.2

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
