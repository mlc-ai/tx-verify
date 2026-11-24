-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseFootprint
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.Assumption Epilogue Mma

noncomputable section

/-- The final readout for a valid correction row agrees with the producer's last softmax visit.
Only stage zero uses a nonzero predicate carried from the normalization code. -/
def LseStatisticsAt (p : Params) (batch head row : Nat) (stage : Fin 2) (t : TState) : Prop :=
  ∃ (blocks : Nat) (ref : Nat → Option ℝ) (sums : Nat → ℝ) (maximum : ℝ),
    SoftmaxSumRun p batch head row blocks ref sums ∧ 0 < blocks ∧
    p.keyCount batch row ≤ 128 * blocks ∧
    t.regs (statsReg stage .sum) = some (fl (sums (blocks - 1))) ∧
    t.regs (statsReg stage .maximum) = some (fl maximum) ∧
    t.regs 7134 = some (b32 p.scaleLog2Bits) ∧
    abiFloat p.scaleLog2Bits * maximum = (ref (blocks - 1)).getD 0 ∧
    (stage = 0 → t.regs (lsePredReg stage) = some (.pred true))

private theorem lseScale {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    valFloat .f32 (b32 p.scaleLog2Bits) = .ok (abiFloat p.scaleLog2Bits) := by
  obtain ⟨x, _, h, _, _⟩ := hp.scales
  have hBound := (hp.values (12, p.scaleLog2Bits) (by simp [Params.scalarWords])).1
  rw [abiFloat, h]
  exact valFloat_b32 (by change p.scaleLog2Bits < 2 ^ 32 at hBound; omega) h

private theorem lseNumericFrame {F : List (Nat × Value)} (stage : Fin 2)
    (h : (F.map Prod.fst).all (fun r => decide
      (r ≠ lseLogReg stage ∧ r ≠ lseFmaReg stage ∧ r ≠ lseMulReg stage ∧ r ≠ lseOutReg stage)) =
      true) :
    ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage := fun _ hm =>
  of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))

private theorem lseComputed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head row : Nat} {t : TState} {F : List (Nat × Value)} (stage : Fin 2)
    (hb : batch < p.batch) (hr : row < p.qLength batch) (ht : At t (lsePc stage) F)
    (hStats : LseStatisticsAt p batch head row stage t)
    (hPred : t.regs (lsePredReg stage) = some (.pred true))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ lseLogReg stage ∧ rv.1 ≠ lseFmaReg stage ∧
      rv.1 ≠ lseMulReg stage ∧ rv.1 ≠ lseOutReg stage) :
    ∃ u, At u (lsePc stage + 4) ((lseOutReg stage, fl (lse p batch head row)) :: F) ∧
      run kernel Assumptions.all l g 4 t = some u := by
  obtain ⟨blocks, ref, sums, maximum, hSoft, hBlocks, hCover, hSum, hMax, hScale,
    hReference, _⟩ := hStats
  have hKey := hp.keyCount_pos hb hr
  have hPositive := hSoft.final_sum_pos hBlocks hKey hCover
  have hValue := hSoft.final_lse hBlocks hKey hCover
  obtain ⟨u, hu, hRun⟩ := finalLseLocal (l := l) (g := g) stage ht hSum hMax hScale hPred
    rfl rfl (lseScale hp) hPositive hFresh
  rw [hReference, hValue] at hu
  exact ⟨u, hu, hRun⟩

/-- The value of the selected store is determined by the known four-byte source at its guard. -/
private theorem lseReadoutAtGuard {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch head tile pc : Nat} {a : Acc} {bytes : List Byte} {v : Value}
    {s : TState} {F : List (Nat × Value)} {es : List Event} {vs : List Visit}
    (stage : Fin 2) (hb : batch < p.batch) (hh : head < p.heads)
    (hStage : pc = lseGuardPc stage + 1)
    (ht : At s (lseGuardPc stage) F)
    (hTest : s.regs (lseTailPred stage) = some
      (.pred (decide (p.qLength batch ≤ stageRow tile stage + rowOf l g))))
    (hBase : (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) ∈ F)
    (hVal : (lseOutReg stage, v) ∈ F) (hWidth : v.bytes = 4)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : ⟨pc, .wr a bytes⟩ ∈ es) :
    bytes = v.toBytes := by
  obtain ⟨u, es', _, hu, hWalk, hBranch, _⟩ :=
    traceLseStoreBranch hp stage hb hh hTest hBase ht (fun _ _ => terminalNotWrite) hw he
  have hAfter : (⟨pc, .wr a bytes⟩ : Event) ∉ es' := by
    apply noEarlierLseAfterStage (lo := lseGuardPc stage + 2)
    · fin_cases stage <;> decide
    · omega
    · exact hu.1.ge
    · rw [hu.2.1]
      decide
    · exact hWalk
  rcases hBranch with ⟨_, rfl⟩ | ⟨_, written, hEvents, hValue⟩
  · exact (hAfter he).elim
  rw [hEvents, List.mem_cons] at he
  have hEq := he.resolve_right hAfter
  obtain ⟨_, _, hBytes⟩ := by simpa only [Event.mk.injEq, Kind.wr.injEq] using hEq
  exact hBytes.trans (hValue v hVal hWidth)

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch head tile pc : Nat}
    {s : TState} {a : Acc} {bytes : List Byte} {es : List Event} {vs : List Visit}
    (hb : batch < p.batch) (hh : head < p.heads) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9057 (lseFootprintEntryFacts p l g batch head tile)) (hPc : pc = 9073 ∨ pc = 9082)
    (hw : Walk kernel Assumptions.all l g s es vs)
include hp hb hh hTile hs hPc hw

/-- Recover the actual stage's numerical readout, with no predicate about padded-stage sums.
The callback relates the chosen stage's observed window to its final softmax statistics. -/
theorem correctionLseValueFromReadyForValidRow (he : ⟨pc, .wr a bytes⟩ ∈ es)
    (hStats : ∀ (stage : Fin 2) t consumed rest tail, pc = lseGuardPc stage + 1 →
      stageRow tile stage + rowOf l g < p.qLength batch →
      t.pc = (if stage = 0 then 9061 else 9074) → es = consumed ++ rest →
      TraceReach kernel Assumptions.all l g s consumed t →
      Walk kernel Assumptions.all l g t rest tail → ⟨pc, .wr a bytes⟩ ∈ rest →
      LseStatisticsAt p batch head (stageRow tile stage + rowOf l g) stage t) :
    ∃ stage : Fin 2, pc = lseGuardPc stage + 1 ∧
      stageRow tile stage + rowOf l g < p.qLength batch ∧
      a.loc = p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head ∧
      a.size = 4 ∧ bytes = (fl (lse p batch head (stageRow tile stage + rowOf l g))).toBytes := by
  obtain ⟨stage, hStage, hr, hAddr, hSize⟩ :=
    correctionLseFootprintFromReady hp hb hh hTile hs hPc hw he
  refine ⟨stage, hStage, hr, hAddr, hSize, ?_⟩
  fin_cases stage
  · obtain ⟨t, tvs, ht, hW, hPath⟩ := lseFirstStartFromWalk hp hb hh hTile hs hw he
    have hStats0 := hStats 0 t [] es tvs hStage hr ht.1 rfl hPath hW he
    have hPred : t.regs (lsePredReg 0) = some (.pred true) := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hZero⟩ := hStats0
      exact hZero rfl
    let value := fl (lse p batch head (stageRow tile 0 + rowOf l g))
    obtain ⟨u, hu, hRun⟩ := lseComputed hp 0 hb hr ht hStats0 hPred (lseNumericFrame 0 rfl)
    obtain ⟨v, hGuard, hTest, hv, hSaved⟩ := lseFirstGuardRun hp hb hTile (hu.mono hu.2.2.2.2.2)
    rcases advanceWalkLocals (run_comp hRun hGuard) hW with hNil | ⟨_, _, _, hV⟩
    · simp [hNil] at he
    have hv' := hv.mono (G := (1655, value) :: _) ⟨hSaved.trans hu.2.2.2.2.1, hv.2.2.2.2⟩
    exact lseReadoutAtGuard hp 0 hb hh hStage hv' hTest (by simp) List.mem_cons_self rfl hV he
  obtain ⟨v, _, hTest0, hv, hV, hPath⟩ :=
    lseFirstGuardFromWalk hp hb hh hTile hs (fun _ _ => terminalNotWrite) hw he
  obtain ⟨t, rest, tail, ht, hW, hBranch, consumed, hConsumed, hReach⟩ :=
    traceLseStoreBranch hp 0 hb hh hTest0 (by simp) hv (fun _ _ => terminalNotWrite) hV he
  have hRest : ⟨pc, .wr a bytes⟩ ∈ rest ∧ rest ⊆ es := by
    rcases hBranch with ⟨_, rfl⟩ | ⟨_, written, hEvents, _⟩
    · exact ⟨he, fun _ h => h⟩
    · rw [hEvents, List.mem_cons] at he
      refine ⟨he.resolve_left ?_, fun _ h => hEvents.symm ▸ List.mem_cons_of_mem _ h⟩
      intro hEq
      have h0 := congrArg Event.pc hEq
      change pc = 9073 at h0
      change pc = 9082 at hStage
      omega
  have hStats1 :=
    hStats 1 t consumed rest tail hStage hr ht.1 hConsumed (hPath.append hReach) hW hRest.1
  let value := fl (lse p batch head (stageRow tile 1 + rowOf l g))
  obtain ⟨blocks, ref, sums, maximum, hSoft, hBlocks, hCover, hSum, hMax, hScale,
    hRef, _⟩ := hStats1
  let F := [(1653, fl (sums (blocks - 1))), (1654, fl maximum), (7134, b32 p.scaleLog2Bits)] ++
    [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
      (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)]
  have hT := ht.mono (G := F) ⟨hSum, hMax, hScale, ht.2.2.2.2⟩
  obtain ⟨x, hx, hX⟩ := secondLsePredicateRun (l := l) (g := g) (sums (blocks - 1)) hT hSum (by
    intro rv hm hEq
    have h := List.mem_map_of_mem (f := Prod.fst) hm
    rw [hEq] at h
    exact (of_decide_eq_true rfl : 742 ∉ F.map Prod.fst) h)
  have hPos := hSoft.final_sum_pos hBlocks (hp.keyCount_pos hb hr) hCover
  have hPred : x.regs (lsePredReg 1) = some (.pred true) := by
    change x.regs 742 = _
    simpa only [decide_eq_true (ne_of_gt hPos)] using hX.2.2.2.2.1
  have hElse : (1 : Fin 2) ≠ 0 := by decide
  have hStatsX : LseStatisticsAt p batch head (stageRow tile 1 + rowOf l g) 1 x :=
    ⟨blocks, ref, sums, maximum, hSoft, hBlocks, hCover, hX.2.2.2.2.2.1,
      hX.2.2.2.2.2.2.1, hX.2.2.2.2.2.2.2.1, hRef, fun h => (hElse h).elim⟩
  have hX' := hX.mono hX.2.2.2.2.2.2.2.2
  obtain ⟨u, hu, hRun⟩ := lseComputed hp 1 hb hr hX' hStatsX hPred (lseNumericFrame 1 rfl)
  obtain ⟨y, hGuard, hTest, hy, hSaved⟩ := lseSecondGuardRun hp hb hTile (hu.mono hu.2.2.2.2.2)
  rcases advanceWalkLocals (run_comp (run_comp hx hRun) hGuard) hW with hNil | ⟨_, _, _, hY⟩
  · simp [hNil] at hRest
  have hy' := hy.mono (G := (1656, value) :: _) ⟨hSaved.trans hu.2.2.2.2.1, hy.2.2.2.2⟩
  exact lseReadoutAtGuard hp 1 hb hh hStage hy' hTest (by simp) List.mem_cons_self rfl hY hRest.1

end
end PTX.Kernels.TmlFa4Fwd.Correction
