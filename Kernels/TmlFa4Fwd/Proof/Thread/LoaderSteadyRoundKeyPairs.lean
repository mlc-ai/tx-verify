-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundExchange
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringSwizzle
public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringLengthSeed
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringKeyCopyLength
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The physical ring stage of the K packet of steady round `round`. -/
def steadyKeyStage (round : Nat) : Nat := (kvUseStage (cacheUseOfRound round)).val

theorem steadyKeyStage_lt (round : Nat) : steadyKeyStage round < 3 := (kvUseStage _).isLt

/-- The copy-size registers set by the first `k` steady K pairs. Every row of a steady tile
is live, so each pair copies its full 16 bytes. The V packet reuses these registers. -/
def steadyKeySizes (k : Nat) : List (Nat × Value) := (List.range k).map (fun i => (1154+i,b32 16))

theorem steadyKeySizes_succ (k : Nat) :
    steadyKeySizes (k+1) = steadyKeySizes k ++ [(1154+k,b32 16)] := by
  simp [steadyKeySizes,List.range_succ]

/-- The number of K rows of the selected request from this lane's first row of the steady
tile onwards. -/
def steadyRoundKeyResidual (p : Params) (l : Launch) (g batch round lane : Nat) : Nat :=
  p.kLength batch - (128*steadyRoundTile p l g batch round+(warpLane l g lane%l.block)/8%8)

/-- The K carry after the packet prelude: the residual row count, both swizzled destination
bases at stage zero, and the carry of the K acquire. -/
def steadyRoundKeyPacked (p : Params) (l : Launch) (g batch round lane : Nat) :
    List (Nat × Value) :=
  (2155,b32 (steadyRoundKeyResidual p l g batch round lane)) ::
    (recurringSwizzleFacts l (warpLane l g lane%l.block) 2 ++
      steadyRoundKeyCarry p l g batch round lane)

/-- The stage offset and both destination bases of the K pairs. -/
def steadyKeyPairCarry (l : Launch) (stage tid : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(2160,b32 (32768*stage)),(2161,b32 (kvCopyAddress l.sharedBase stage tid 0 false)),
    (2164,b32 (kvCopyAddress l.sharedBase stage tid 1 false))] ++ F

/-- The first pair that reads each saved pointer slot. -/
def steadyKeySlotPair : Fin 2 → Fin 16
  | 0 => 0
  | 1 => 8

/-- The K carry before pair `k` of the given pointer slot, with the copy sizes of the
earlier pairs. -/
def steadyRoundKeyGroupFrame (p : Params) (l : Launch) (g batch round lane : Nat)
    (slot : Fin 2) (k : Nat) : List (Nat × Value) :=
  steadyWords false (steadyKeySlotPair slot) (steadyRoundKeyPointer p l g batch round lane slot) ++
    steadyKeyPairCarry l (steadyKeyStage round) (warpLane l g lane%l.block)
      (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes k)

/-- The live-row comparison of each steady K pair. -/
def steadyKeyComparePc (pair : Fin 16) : Nat :=
  (![1468,1479,1488,1496,1504,1512,1520,1528,1536,1545,1553,1561,1569,1577,1585,1593] :
    Fin 16 → Nat) pair

/-- The checkpoint before steady K pair `k`, or the commit after the last pair. -/
def steadyKeyNextPc (k : Nat) : Nat :=
  if h : k < 16 then steadyKeyComparePc ⟨k,h⟩ else 1601

theorem steadyKeyCompareCode (pair : Fin 16) :
    kernel.code[steadyKeyComparePc pair]? =
      some ⟨none,signedCompareOp .gt (212+pair.val) 2155 (8*pair.val)⟩ :=
  compareCode true pair

theorem steadyKeySelectCode (pair : Fin 16) :
    kernel.code[packetPairPc (recurringPacketSite 2) pair-1]? = some ⟨none,.int ⟨.selp,
      .int .b 32,false,[some (1154+pair.val)],[.imm 16,.imm 0,.reg (212+pair.val)]⟩⟩ :=
  selectCode true pair

theorem steadyKeyWordsForSlot (pair : Fin 16) (slot : Fin 2) (base : Nat)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1)) :
    steadyWords false (steadyKeySlotPair slot) base = steadyWords false pair base := by
  fin_cases slot
  · change 0 ≤ pair.val ∧ pair.val < 8 at hRange
    have h : pair.val < 8 := hRange.2
    simp [steadyWords,steadyPairShuffleIn,steadyPairSlot,steadyKeySlotPair,h]
  · change 8 ≤ pair.val ∧ pair.val < 16 at hRange
    have h : ¬ pair.val < 8 := Nat.not_lt_of_ge hRange.1
    simp [steadyWords,steadyPairShuffleIn,steadyPairSlot,steadyKeySlotPair,h]

/-- Every row of a steady tile is live for each pair, and the residual fits a signed word. -/
theorem steadyRoundKeyLive {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch round lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (pair : Fin 16) :
    8*pair.val < steadyRoundKeyResidual p l g batch round lane ∧
      steadyRoundKeyResidual p l g batch round lane < 2^31 := by
  have hBound := (Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1).2.1
  have hLen := (hp.lengths batch hb).2.2
  refine ⟨?_,?_⟩
  · exact recurringKeyResidualLive (round := round) pair (by omega) hBound
      (Nat.mod_lt _ (by decide))
  · unfold steadyRoundKeyResidual
    omega

/-- The K row pointers are 64-bit, 16-byte aligned addresses. -/
theorem steadyRoundKeyPointerBounds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch round lane : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (slot : Fin 2) :
    steadyRoundKeyPointer p l g batch round lane slot < 2^64 ∧
      steadyRoundKeyPointer p l g batch round lane slot%16 = 0 := by
  let head := (assignedCoordinates p batch (g/l.block)).2/6
  let row := steadyRoundSlotRow p l g batch round lane slot
  have hh : head < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have h := sourceScratchPayload_live hp 0 (primingScratchPageBound hp (row := row) hb)
    (Nat.mod_lt row (by decide)) hh
  have hEq : sourceScratchPayload (primingScratchPage p batch row) (row%16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*(head*p.kLayout.headStride)) = primingKRowPointer p batch head row :=
    h.1
  show primingKRowPointer p batch head row < 2^64 ∧ primingKRowPointer p batch head row%16 = 0
  exact hEq ▸ h.2

/-- The source of a steady pair is 16-byte aligned when the sender's pointer is. -/
theorem steadySourceAligned {base tid : Nat} (h : base%16 = 0) :
    recurringSourceAddress base tid%16 = 0 := by
  unfold recurringSourceAddress
  rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
  simp [Nat.add_mod,h]

theorem steadyKeyGroupFrame_succ {R : Nat → Option Value} {p : Params} {l : Launch}
    {g batch round lane : Nat} {slot : Fin 2} {k : Nat}
    (h : Holds R (steadyRoundKeyGroupFrame p l g batch round lane slot k))
    (hk : R (1154+k) = some (b32 16)) :
    Holds R (steadyRoundKeyGroupFrame p l g batch round lane slot (k+1)) := by
  have h' := (holds_append ..).mp h
  have hc := (holds_append ..).mp h'.2
  refine (holds_append ..).mpr ⟨h'.1,(holds_append ..).mpr ⟨hc.1,?_⟩⟩
  rw [steadyKeySizes_succ,← List.append_assoc]
  exact (holds_append ..).mpr ⟨hc.2,hk,trivial⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch round ordinal votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
include hp hMax hg hb hLo

set_option maxRecDepth 100000 in
/-- After its live-row comparison, a noninitial steady K pair exchanges the sender's pointer,
forms its source, selects its size and issues both vectors. The lane's private cells are
preserved. -/
theorem steadyRoundKeyPairAfterMaskOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (slot : Fin 2) (pair : Fin 16) (hLater : 2 ≤ pair.val)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1)) {ends : Nat → Option TState}
    (masked : SchedulerWarpReached l X g (steadyPairShufflePc false pair)
      (fun lane => steadyWords false pair (steadyRoundKeyPointer p l g batch round lane slot) ++
        (212+pair.val,.pred true) :: steadyKeyPairCarry l (steadyKeyStage round)
          (warpLane l g lane%l.block)
          (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes pair.val))
        ordinal votes ends) :
    ∃ done : SchedulerWarpReached l X g (steadyKeyNextPc (pair.val+1))
        (fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot (pair.val+1))
        (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (masked.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundKeyPointer p l g batch round lane slot
  let stage := steadyKeyStage round
  let C := fun lane => steadyKeyPairCarry l stage (warpLane l g lane%l.block)
    (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes pair.val)
  have hWords (lane : Nat) : steadyWords false (steadyKeySlotPair slot) (ptr lane) =
      steadyWords false pair (ptr lane) := steadyKeyWordsForSlot pair slot (ptr lane) hRange
  -- the exchange
  obtain ⟨exchanged,hEx⟩ := steadyExchangeOfMaximal hp hMax hg false pair ptr
    (fun lane _ fact hm => by
      have h : ((steadyWords false pair (ptr lane) ++ (212+pair.val,.pred true) :: C lane).map
          Prod.fst).all (fun r => decide (r ≠ steadyPairShuffleOut false pair ∧
            r ≠ steadyPairShuffleOut false pair+1)) = true := by
        fin_cases pair <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) masked
  -- the source address and the size
  let src := fun lane =>
    recurringSourceAddress (ptr (steadyPairSender lane pair)) (warpLane l g lane%l.block)
  have hCut : steadyPairSourceCut false pair = steadyPairShufflePc false pair+2+2 := by
    simp [steadyPairSourceCut]
  have hPairPc : packetPairPc (recurringPacketSite 2) pair = steadyPairSourceCut false pair+1 := by
    revert hLater
    fin_cases pair <;> decide
  obtain ⟨ready,hReady⟩ := exchanged.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 2) pair)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 2) stage (warpLane l g lane%l.block)
      (src lane) 16 pair ++
        steadyRoundKeyGroupFrame p l g batch round lane slot (pair.val+1)) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      let E := steadyExchangeWords false pair (ptr (steadyPairSender lane pair)) ++
        steadyWords false pair (ptr lane) ++ (212+pair.val,.pred true) :: C lane
      have hs := exchanged.checkpoint lane hl
      have hE : Holds (exchanged.state lane).regs E := hs.2.2.2.2
      have hIn : At (exchanged.state lane) (steadyPairShufflePc false pair+2)
          (steadyPairInputs false pair (ptr (steadyPairSender lane pair)) tid ++ E) := by
        refine hs.mono ((holds_append ..).mpr ⟨⟨hE.1,hE.2.1,?_,trivial⟩,hE⟩)
        exact holds_lookup ((holds_append ..).mp hE).2.2 rfl
      have hCore := steadyPairSourceCore (l := l) (g := t) (tid := tid)
        (steadyRoundKeyPointerBounds hp (round := round) (lane := steadyPairSender lane pair)
          hb hLo hHi slot).1 false pair
      rw [hCut,show steadyPairShufflePc false pair+2+2-(steadyPairShufflePc false pair+2) = 2
        by omega] at hCore
      obtain ⟨u,hu,hU⟩ := roundStraightFrame
        (by fin_cases pair <;> decide) (by fin_cases pair <;> decide)
        (by revert hLater; fin_cases slot <;> fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl)
        (by revert hLater; fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl) hCore hIn
      have hSelPc : packetPairPc (recurringPacketSite 2) pair-1 =
          steadyPairShufflePc false pair+2+2 := by
        rw [hPairPc,hCut]
        rfl
      have hSel := liveKeySelectCore (l := l) (g := t) (hSelPc ▸ steadyKeySelectCode pair)
      obtain ⟨v,hv,hV⟩ := roundStraightFrame
        (by fin_cases pair <;> decide) (by fin_cases pair <;> decide)
        (by revert hLater; fin_cases slot <;> fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl) rfl hSel
        (show At u (steadyPairShufflePc false pair+2+2)
          ([(212+pair.val,.pred true)] ++ ((packetSrcReg (recurringPacketSite
            (steadySpillSite false)) pair,b64 (src lane)) :: E)) from
          hU.mono ⟨hU.2.2.2.2.2.2.2.2.2.1,hU.2.2.2.2⟩)
      refine ⟨v,run_rtg (run_comp hu hv),?_⟩
      rw [hPairPc,hCut]
      have hR := hV.2.2.2.2
      have hRest : Holds v.regs E := hR.2.2
      have hC : Holds v.regs (C lane) := ((holds_append ..).mp hRest).2.2
      refine hV.mono ((holds_append ..).mpr ⟨?_,?_⟩)
      · refine ⟨?_,hR.2.1,hR.1,trivial⟩
        have hParity : packetDstReg (recurringPacketSite 2) pair =
            (if pair.val%2 = 0 then 2161 else 2164) := by
          fin_cases pair <;> rfl
        rw [hParity]
        have hm := Nat.mod_lt pair.val (by decide : 0 < 2)
        by_cases hEven : pair.val%2 = 0
        · rw [ite_eq_left hEven,hEven]
          exact hC.2.1
        · rw [ite_eq_right hEven,show pair.val%2 = 1 by omega]
          exact hC.2.2.1
      · apply steadyKeyGroupFrame_succ _ hR.1
        refine (holds_append ..).mpr ⟨?_,hC⟩
        rw [hWords]
        exact ((holds_append ..).mp ((holds_append ..).mp hRest).1).2)
  obtain ⟨done,_,hResult⟩ := packetPairWarpOfMaximal hp hMax hg
    (recurringPacketSite 2) pair (by have := steadyKeyStage_lt round; change stage+0 < 3; omega)
    src (fun _ => 16) (fun _ _ => Nat.mod_lt _ (by decide))
    (fun lane _ => steadySourceAligned
      (steadyRoundKeyPointerBounds hp (round := round) (lane := steadyPairSender lane pair)
        hb hLo hHi slot).2) (fun _ _ => le_rfl) ready
  have hNext : packetPairPc (recurringPacketSite 2) pair+2 = steadyKeyNextPc (pair.val+1) := by
    revert hLater
    fin_cases pair <;> decide
  obtain ⟨done',hDone'⟩ := done.advanceLocalWithPosition (pc' := steadyKeyNextPc (pair.val+1))
    (G := fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot (pair.val+1))
    (fun lane hl => ⟨done.state lane,.refl,hNext ▸ done.checkpoint lane hl⟩)
  refine ⟨done',fun lane hl pc cell data hCell => ?_⟩
  rw [hDone']
  apply (hResult lane hl).2
  rw [hReady]
  exact (hEx lane hl).2 hCell

set_option maxRecDepth 100000 in
/-- A noninitial steady K pair that does not reload a pointer compares its row, exchanges
the sender's pointer, forms its source, selects its size and issues both vectors. The lane's
private cells are preserved. -/
theorem steadyRoundKeyNextPairOfMaximal (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : round+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (slot : Fin 2) (pair : Fin 16) (hLater : 2 ≤ pair.val)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1)) (hNoReload : pair.val ≠ 8)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (steadyKeyComparePc pair)
      (fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot pair.val)
        ordinal votes ends) :
    ∃ done : SchedulerWarpReached l X g (steadyKeyNextPc (pair.val+1))
        (fun lane => steadyRoundKeyGroupFrame p l g batch round lane slot (pair.val+1))
        (ordinal+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => steadyRoundKeyPointer p l g batch round lane slot
  let stage := steadyKeyStage round
  let C := fun lane => steadyKeyPairCarry l stage (warpLane l g lane%l.block)
    (steadyRoundKeyPacked p l g batch round lane ++ steadyKeySizes pair.val)
  have hWords (lane : Nat) : steadyWords false (steadyKeySlotPair slot) (ptr lane) =
      steadyWords false pair (ptr lane) := steadyKeyWordsForSlot pair slot (ptr lane) hRange
  have hShufflePc : steadyKeyComparePc pair+1 = steadyPairShufflePc false pair := by
    revert hLater hNoReload
    fin_cases pair <;> decide
  -- the live-row comparison
  obtain ⟨masked,hMasked⟩ := cur.advanceLocalWithPosition (pc' := steadyPairShufflePc false pair)
    (G := fun lane => steadyWords false pair (ptr lane) ++ (212+pair.val,.pred true) :: C lane) (by
      intro lane hl
      let F := steadyRoundKeyGroupFrame p l g batch round lane slot pair.val
      have hs := cur.checkpoint lane hl
      have hRes := steadyRoundKeyLive hp (lane := lane) hb hLo hHi hTrips pair
      have hIn : At (cur.state lane) (steadyKeyComparePc pair)
          ([(2155,b32 (steadyRoundKeyResidual p l g batch round lane))] ++ F) :=
        hs.mono ⟨holds_lookup hs.2.2.2.2 (by fin_cases slot <;> rfl),hs.2.2.2.2⟩
      obtain ⟨u,hu,hU⟩ := roundStraightFrame
        (by fin_cases pair <;> decide) (by fin_cases pair <;> decide)
        (by revert hLater; fin_cases slot <;> fin_cases pair <;> intro hL <;>
          first | exact absurd hL (by decide) | kernel_rfl) rfl
        (liveKeyCompareCore (steadyKeyCompareCode pair) hRes.1 hRes.2) hIn
      refine ⟨u,run_rtg hu,hShufflePc ▸ hU.mono ?_⟩
      have hF : Holds u.regs F := hU.2.2.2.2.2
      have hSplit := (holds_append ..).mp hF
      rw [hWords] at hSplit
      exact (holds_append ..).mpr ⟨hSplit.1,hU.2.2.2.2.1,hSplit.2⟩)
  obtain ⟨done,hDone⟩ := steadyRoundKeyPairAfterMaskOfMaximal hp hMax hg hb hLo hHi slot pair
    hLater hRange masked
  exact ⟨done,fun lane hl _ _ _ hCell => hDone lane hl (by rw [hMasked]; exact hCell)⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
