-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundValueGate
import all Kernels.TmlFa4Fwd.Proof.LoaderSteadyOperandReload
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Kernels.TmlFa4Fwd.Flow.Code.Part026

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The physical ring stage of the V packet of steady round `round`. -/
def steadyValueStage (round : Nat) : Nat := (kvUseStage (cacheUseOfRound round+1)).val

theorem steadyValueStage_lt (round : Nat) : steadyValueStage round < 3 := (kvUseStage _).isLt

/-- The V carry that no V pair changes: the state of the pointer loop and the V acquire. -/
def steadyRoundValueRest (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  [(9540,b64 1),(780,.pred false)] ++ steadyRoundValueAcquired p l g batch round lane

/-- The lane column, the stage offset and both destination bases of the V pairs. -/
def steadyValuePairCarry (l : Launch) (stage tid : Nat) : List (Nat × Value) :=
  [(7825,b64 (16*(tid%8))),(2202,b32 (32768*stage)),
    (2203,b32 (kvCopyAddress l.sharedBase stage tid 0 false)),
    (2206,b32 (kvCopyAddress l.sharedBase stage tid 1 false))]

/-- The V pair checkpoint of one pointer half. -/
def steadyRoundValueGroupFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) : List (Nat × Value) :=
  steadyWords true (steadyKeySlotPair slot) (steadyRoundValuePointer p l g batch round lane slot) ++
    (steadyValuePairCarry l (steadyValueStage round) (warpLane l g lane%l.block) ++
      steadyRoundValueRest p l g batch round lane)

/-- The checkpoint before steady V pair `k`. The upper half begins with its pointer reload. -/
def steadyValueNextPc (k : Nat) : Nat :=
  if k = 8 then 1685 else if h : k < 16 then steadyPairShufflePc true ⟨k,h⟩ else 1734

theorem steadyValueWordsForSlot (pair : Fin 16) (slot : Fin 2) (base : Nat)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1)) :
    steadyWords true (steadyKeySlotPair slot) base = steadyWords true pair base := by
  fin_cases slot
  · change 0 ≤ pair.val ∧ pair.val < 8 at hRange
    have h : pair.val < 8 := hRange.2
    simp [steadyWords,steadyPairShuffleIn,steadyPairSlot,steadyKeySlotPair,h]
  · change 8 ≤ pair.val ∧ pair.val < 16 at hRange
    have h : ¬ pair.val < 8 := Nat.not_lt_of_ge hRange.1
    simp [steadyWords,steadyPairShuffleIn,steadyPairSlot,steadyKeySlotPair,h]

/-- The V row pointers are 64-bit, 16-byte aligned addresses. -/
theorem steadyRoundValuePointerBounds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch round lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) :
    steadyRoundValuePointer p l g batch round lane slot < 2^64 ∧
      steadyRoundValuePointer p l g batch round lane slot%16 = 0 := by
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let row := steadyRoundSlotRow p l g batch round lane slot
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  obtain ⟨hEq,hLt,hAl⟩ := sourceScratchPayload_live hp 1
    (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
  rw [hEq] at hLt hAl
  exact ⟨by simpa [steadyRoundValuePointer,primingVRowPointer] using hLt,
    by simpa [steadyRoundValuePointer,primingVRowPointer] using hAl⟩

/-- Every K copy size is part of the V carry. -/
theorem steadyKeySize_mem_valueRest {p : Params} {l : Launch} {g batch round lane : Nat}
    (k : Nat) (hk : k < 16) :
    (1154+k,b32 16) ∈ steadyRoundValueRest p l g batch round lane :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩))))

set_option maxRecDepth 100000 in
/-- A noninitial steady V pair exchanges the sender's pointer, forms its source and issues
both vectors with the copy size of the matching K pair. The lane's private cells are
preserved. -/
theorem steadyRoundValueLaterPairOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round ordinal votes : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (slot : Fin 2) (pair : Fin 16) (hLater : 2 ≤ pair.val)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1))
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (steadyPairShufflePc true pair)
      (steadyRoundValueGroupFrame p l g batch round · slot) ordinal votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 3) pair+2)
        (steadyRoundValueGroupFrame p l g batch round · slot) (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundValuePointer p l g batch round lane slot
  let stage := steadyValueStage round
  let C := fun lane => steadyValuePairCarry l stage (warpLane l g lane%l.block) ++
    steadyRoundValueRest p l g batch round lane
  have hWords (lane : Nat) : steadyWords true (steadyKeySlotPair slot) (ptr lane) =
      steadyWords true pair (ptr lane) := steadyValueWordsForSlot pair slot (ptr lane) hRange
  obtain ⟨start,hStart⟩ := cur.advanceLocalWithPosition (pc' := steadyPairShufflePc true pair)
    (G := fun lane => steadyWords true pair (ptr lane) ++ C lane) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      refine ⟨cur.state lane,.refl,?_⟩
      have h : steadyRoundValueGroupFrame p l g batch round lane slot =
          steadyWords true pair (ptr lane) ++ C lane := by
        simp only [steadyRoundValueGroupFrame,C]
        rw [← hWords]
      rw [← h]
      exact hs)
  obtain ⟨exchanged,hEx⟩ := steadyExchangeOfMaximal hp hMax hg true pair ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords true pair (ptr lane) ++ C lane).map Prod.fst).all
          (fun r => decide (r ≠ steadyPairShuffleOut true pair ∧
            r ≠ steadyPairShuffleOut true pair+1)) = true := by
        fin_cases pair <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) start
  let src := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane pair)) (warpLane l g lane%l.block)
  have hCut : steadyPairSourceCut true pair = steadyPairShufflePc true pair+2+2 := by
    revert hLater
    fin_cases pair <;> decide
  have hPairPc : packetPairPc (recurringPacketSite 3) pair = steadyPairSourceCut true pair := by
    revert hLater
    fin_cases pair <;> decide
  obtain ⟨ready,hReady⟩ := exchanged.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 3) pair)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 3) stage (warpLane l g lane%l.block)
      (src lane) 16 pair ++ steadyRoundValueGroupFrame p l g batch round lane slot) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords true pair (ptr (steadyPairSender lane pair)) ++
        steadyWords true pair (ptr lane) ++ C lane
      have hs := exchanged.checkpoint lane hl
      have hE : Holds (exchanged.state lane).regs E := hs.2.2.2.2
      have hC : Holds (exchanged.state lane).regs (C lane) := ((holds_append ..).mp hE).2
      have hNot0 : pair.val ≠ 0 := by omega
      have hIn : At (exchanged.state lane) (steadyPairShufflePc true pair+2)
          (steadyPairInputs true pair (ptr (steadyPairSender lane pair)) tid ++ E) := by
        have hInputs : steadyPairInputs true pair (ptr (steadyPairSender lane pair)) tid =
            steadyExchangeWords true pair (ptr (steadyPairSender lane pair)) ++
              [(7825,b64 (16*(tid%8)))] := by
          simp [steadyPairInputs,steadyPairColumn,steadyExchangeWords,hNot0]
        rw [hInputs]
        exact hs.mono ((holds_append ..).mpr ⟨(holds_append ..).mpr
          ⟨((holds_append ..).mp ((holds_append ..).mp hE).1).1,hC.1,trivial⟩,hE⟩)
      have hCore := steadyPairSourceCore (l := l) (g := t) (tid := tid)
        (steadyRoundValuePointerBounds hp (round := round) (lane := steadyPairSender lane pair)
          hb hLo hHi slot).1 true pair
      rw [hCut,show steadyPairShufflePc true pair+2+2-(steadyPairShufflePc true pair+2) = 2
        by omega] at hCore
      obtain ⟨u,hu,hU⟩ := roundStraightFrame
        (by fin_cases pair <;> decide) (by fin_cases pair <;> decide)
        (by revert hLater; fin_cases slot <;> fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl)
        (by revert hLater; fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl) hCore hIn
      refine ⟨u,run_rtg hu,?_⟩
      rw [hPairPc,hCut]
      have hR := hU.2.2.2.2
      have hRest : Holds u.regs E := hR.2
      have hCu : Holds u.regs (C lane) := ((holds_append ..).mp hRest).2
      have hWu := ((holds_append ..).mp ((holds_append ..).mp hRest).1).2
      have hRestu : Holds u.regs (steadyRoundValueRest p l g batch round lane) :=
        ((holds_append ..).mp hCu).2
      refine hU.mono ((holds_append ..).mpr ⟨?_,?_⟩)
      · refine ⟨?_,hR.1,holds_mem hRestu (steadyKeySize_mem_valueRest pair.val pair.isLt),
          trivial⟩
        have hParity : packetDstReg (recurringPacketSite 3) pair =
            (if pair.val%2 = 0 then 2203 else 2206) := by
          fin_cases pair <;> rfl
        rw [hParity]
        have hm := Nat.mod_lt pair.val (by decide : 0 < 2)
        by_cases hEven : pair.val%2 = 0
        · rw [ite_eq_left hEven,hEven]
          exact hCu.2.2.1
        · rw [ite_eq_right hEven,show pair.val%2 = 1 by omega]
          exact hCu.2.2.2.1
      · refine (holds_append _ (steadyWords true (steadyKeySlotPair slot) (ptr lane)) _).mpr
          ⟨?_,hCu⟩
        rw [hWords]
        exact hWu)
  obtain ⟨done,_,hResult⟩ := packetPairWarpOfMaximal hp hMax hg
    (recurringPacketSite 3) pair (by have := steadyValueStage_lt round; change stage+0 < 3; omega)
    src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => steadySourceAligned
      (steadyRoundValuePointerBounds hp (round := round) (lane := steadyPairSender lane pair)
        hb hLo hHi slot).2) (fun _ _ => le_rfl) ready
  refine ⟨done,fun lane hl pc cell data hCell => ?_⟩
  apply (hResult lane hl).2
  rw [hReady]
  apply (hEx lane hl).2
  rw [hStart]
  exact hCell

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
