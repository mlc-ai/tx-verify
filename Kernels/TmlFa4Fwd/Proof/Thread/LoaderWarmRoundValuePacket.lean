-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePairs
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePairSites
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondValueReload
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePointers
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part020
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The V ring stage of warm round `round`, as computed by the K-to-V transition. -/
def warmValueStage (round : Nat) : Nat := ((kvUseStage (cacheUseOfRound round)).val+1)%3

theorem warmValueStage_lt (round : Nat) : warmValueStage round < 3 := Nat.mod_lt _ (by decide)

/-- The part of the V carry that no V pair changes. -/
def warmRoundVRest (p : Params) (l : Launch) (g batch round : Nat) (bias : Value)
    (lane : Nat) : List (Nat × Value) :=
  (2081,b32 (32768*warmValueStage round)) ::
    (recurringSwizzleFacts l (warpLane l g lane%l.block) 1 ++
      (9538,b64 1) :: (777,.pred false) :: warmRoundVAcquired p l g batch round bias lane)

/-- The V pair checkpoint of pair `pair`, reading pointer slot `slot`. -/
def warmRoundVPairFrame (p : Params) (l : Launch) (g batch round : Nat) (bias : Value)
    (slot : Fin 2) (pair : Fin 16) (lane : Nat) : List (Nat × Value) :=
  warmValueWords pair (warmRoundValuePointer p l g batch round lane slot) ++
    warmRoundVPairCarry l (warmValueStage round) (warpLane l g lane%l.block) ++
      warmRoundVRest p l g batch round bias lane

/-- Every K copy size is part of the V carry. -/
theorem keySize_mem_vAcquired {p : Params} {l : Launch} {g batch round : Nat} {bias : Value}
    {lane : Nat} (k : Nat) (hk : k < 16) :
    (1123+k,b32 16) ∈ warmRoundVAcquired p l g batch round bias lane :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩)))

private theorem warmVColumnCore {l : Launch} {g base tid : Nat} (hTid : tid < 512) :
    Seg kernel [] l g 4 1241 (warmVPairInputs 0 base tid) 1245
      [(7721,b64 (16*(tid%8)))] := by
  have hOffset3 : 16*tid < 4294967296 := by omega
  have hTid64 : 16*tid < 18446744073709551616 := by omega
  intro s hs
  change At s 1241 [(2079,b32 (base%2^32)),(2080,b32 (base/2^32)),(2066,b32 (16*tid))] at hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hOffset3,Nat.mod_eq_of_lt hTid64,columnMask16]

private theorem warmVSourceAndColumn {l : Launch} {g base tid : Nat}
    (hBase : base < 2^64) (hTid : tid < 512) :
    Seg kernel [] l g 4 1241 (warmVPairInputs 0 base tid) 1245
      [(7722,b64 (recurringSourceAddress base tid)),(7721,b64 (16*(tid%8)))] := by
  intro s hs
  have hSrc := warmVPairSourceCore (l := l) (g := g) hBase hTid 0
  change Seg kernel [] l g 4 1241 (warmVPairInputs 0 base tid) 1245
    [(7722,b64 (recurringSourceAddress base tid))] at hSrc
  obtain ⟨u,hu,hU⟩ := hSrc s hs
  obtain ⟨v,hv,hV⟩ := warmVColumnCore (l := l) (g := g) (base := base) hTid s hs
  have he : v = u := Option.some.inj (hv.symm.trans hu)
  exact ⟨u,hu,hU.mono ⟨hU.2.2.2.2.1,he ▸ hV.2.2.2.2⟩⟩

set_option maxRecDepth 4096 in
/-- The first two V pairs establish the lane column and both destination bases, issue their
four vectors, and keep the second saved pointer. -/
theorem WarmRoundVReloaded.firstPairsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} {bias : Value} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {ends : Nat → Option TState}
    (r : WarmRoundVReloaded p l X g batch round bias shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmVShufflePc 2)
        (warmRoundVPairFrame p l g batch round bias 0 2) (shuffles+4) votes ends,
      ∀ lane < 32, PrimingCellValue X (warpLane l g lane) (done.pos lane) 1223
        (pointerSaveAccess l (warpLane l g lane) 1 1)
        (b64 (warmRoundValuePointer p l g batch round lane 1)).toBytes := by
  let ptr := fun lane => warmRoundValuePointer p l g batch round lane 0
  let stage := warmValueStage round
  let VA := warmRoundVAcquired p l g batch round bias
  let F := fun lane => (2066,b32 (16*(warpLane l g lane%l.block))) ::
    (recurringSwizzleFacts l (warpLane l g lane%l.block) 1 ++
      (9538,b64 1) :: (777,.pred false) :: VA lane)
  have hh : (assignedCoordinates p batch (g/l.block)).2/6 < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPtr (lane : Nat) : ptr lane < 2^64 ∧ ptr lane%16 = 0 := by
    let row := warmRoundSlotRow p l g batch round lane 0
    obtain ⟨hEq,hLt,hAl⟩ := sourceScratchPayload_live hp 1
      (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
    rw [hEq] at hLt hAl
    exact ⟨by simpa [ptr,warmRoundValuePointer,primingVRowPointer] using hLt,
      by simpa [ptr,warmRoundValuePointer,primingVRowPointer] using hAl⟩
  have hSender (lane : Nat) (hl : lane < 32) (pair : Fin 16) :
      warmVShuffleSender lane pair < 32 := by
    have := Nat.mod_lt pair.val (by decide : 0 < 8)
    unfold warmVShuffleSender pointerBroadcastLane
    omega
  -- pair zero
  obtain ⟨cur0,hCur0⟩ := r.reached.advanceLocalWithPosition (pc' := warmVShufflePc 0)
    (G := fun lane => warmValueWords 0 (ptr lane) ++ F lane) (by
      intro lane hl
      have hs := r.reached.checkpoint lane hl
      exact ⟨r.reached.state lane,.refl,hs.mono hs.2.2.2.2⟩)
  obtain ⟨ex0,hEx0⟩ := warmValueExchangeOfMaximal hp hMax hg 0 ptr
    (fun lane _ fact hm => by
      have h : ((warmValueWords 0 (ptr lane) ++ F lane).map Prod.fst).all
          (fun r => decide (r ≠ 2079 ∧ r ≠ 2080)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) cur0
  let src0 := fun lane =>
    recurringSourceAddress (ptr (warmVShuffleSender lane 0)) (warpLane l g lane%l.block)
  let K1 := fun lane =>
    let tid := warpLane l g lane%l.block
    (7721,b64 (16*(tid%8))) :: (2082,b32 (kvCopyAddress l.sharedBase stage tid 0 false)) ::
      (2081,b32 (32768*stage)) :: warmValueWords 0 (ptr lane) ++ F lane
  obtain ⟨ready0,hReady0⟩ := ex0.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 1) 0)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 1) stage (warpLane l g lane%l.block)
      (src0 lane) 16 0 ++ K1 lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
      have hs := ex0.checkpoint lane hl
      have hIn : At (ex0.state lane) 1241
          (warmVPairInputs 0 (ptr (warmVShuffleSender lane 0)) tid ++
            (warmValueWords 0 (ptr lane) ++ F lane)) := by
        refine hs.mono ((holds_append ..).mpr ⟨?_,hs.2.2.2.2.2.2⟩)
        simp only [warmVPairInputs,List.cons_append,List.nil_append,Holds]
        exact ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,trivial⟩
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (warmVSourceAndColumn (l := l) (g := t) (hPtr _).1 hTid) hIn
      have hF := hU.2.2.2.2.2.2
      have hStageIn : u.regs 1139 = some (b32 stage) := holds_mem hF (by
        simp [F,VA,warmRoundVAcquired,warmRoundVCarry,recurringVTransitionFacts,
          recurringVTransitionRegs,stage,warmValueStage])
      have hBaseIn : u.regs 2076 = some (b32 (kvCopyAddress l.sharedBase 0 tid 0 false)) :=
        holds_mem hF (by simp [F,recurringSwizzleFacts,recurringSwizzleRegs,tid,t])
      have hAt2 : At u 1245 ([(1139,b32 stage),(2076,b32 (kvCopyAddress l.sharedBase 0 tid 0
          false))]
          ++ ([(7722,b64 (src0 lane)),(7721,b64 (16*(tid%8)))] ++
            (warmValueWords 0 (ptr lane) ++ F lane))) :=
        hU.mono ⟨hStageIn,hBaseIn,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (recurringEvenCore hp (g := t) (lane := tid) 1 (warmValueStage_lt round)) hAt2
      refine ⟨v,run_rtg (run_comp hu hv),?_⟩
      have hRest := hV.2.2.2.2.2.2
      exact hV.mono ⟨hV.2.2.2.2.1,hRest.1,holds_lookup hRest.2.2 rfl,hRest.2.1,hV.2.2.2.2.1,
        hV.2.2.2.2.2.1,hRest.2.2⟩)
  have hAlign0 (lane : Nat) (hl : lane < 32) : src0 lane%16 = 0 := by
    unfold src0 recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr _).2]
  obtain ⟨copied0,_,hCopied0⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 1) 0
    (by have := warmValueStage_lt round; change stage+0 < 3; omega) src0 (fun _ => 16)
    (fun _ _ => Nat.mod_lt _ (by decide)) hAlign0 (fun _ _ => le_rfl) ready0
  -- pair one
  let F1 := fun lane =>
    let tid := warpLane l g lane%l.block
    (7721,b64 (16*(tid%8))) :: (2082,b32 (kvCopyAddress l.sharedBase stage tid 0 false)) ::
      (2081,b32 (32768*stage)) :: F lane
  obtain ⟨cur1,hCur1⟩ := copied0.advanceLocalWithPosition (pc' := warmVShufflePc 1)
    (G := fun lane => warmValueWords 1 (ptr lane) ++ F1 lane) (by
      intro lane hl
      have hs := copied0.checkpoint lane hl
      have k := hs.2.2.2.2
      exact ⟨copied0.state lane,.refl,hs.mono ⟨k.2.2.2.1,k.2.2.2.2.1,k.1,k.2.1,k.2.2.1,
        k.2.2.2.2.2⟩⟩)
  obtain ⟨ex1,hEx1⟩ := warmValueExchangeOfMaximal hp hMax hg 1 ptr
    (fun lane _ fact hm => by
      have h : ((warmValueWords 1 (ptr lane) ++ F1 lane).map Prod.fst).all
          (fun r => decide (r ≠ 2083 ∧ r ≠ 2084)) = true := rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))) cur1
  let src1 := fun lane =>
    recurringSourceAddress (ptr (warmVShuffleSender lane 1)) (warpLane l g lane%l.block)
  obtain ⟨ready1,hReady1⟩ := ex1.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 1) 1)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 1) stage (warpLane l g lane%l.block)
      (src1 lane) 16 1 ++ warmRoundVPairFrame p l g batch round bias 0 2 lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
      have hs := ex1.checkpoint lane hl
      have hIn : At (ex1.state lane) 1251
          (warmVPairInputs 1 (ptr (warmVShuffleSender lane 1)) tid ++
            (warmValueWords 1 (ptr lane) ++ F1 lane)) := by
        refine hs.mono ((holds_append ..).mpr ⟨?_,hs.2.2.2.2.2.2⟩)
        change Holds _ [(2083,_),(2084,_),(7721,_)]
        exact ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,trivial⟩
      have hCore := warmVPairSourceCore (l := l) (g := t) (hPtr (warmVShuffleSender lane 1)).1
        hTid 1
      change Seg kernel [] l t 2 1251 (warmVPairInputs 1 (ptr (warmVShuffleSender lane 1)) tid)
        1253 [(7724,b64 (src1 lane))] at hCore
      obtain ⟨u,hu,hU⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hCore hIn
      have hK := hU.2.2.2.2.2
      have hAt2 : At u 1253 ([(2072,b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
          (2081,b32 (32768*stage))] ++ ([(7724,b64 (src1 lane))] ++
            (warmValueWords 1 (ptr lane) ++ F1 lane))) :=
        hU.mono ⟨holds_lookup hK rfl,holds_lookup hK rfl,hU.2.2.2.2⟩
      obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (recurringOddSeedRun hp (g := t) (lane := tid) 1 (warmValueStage_lt round)) hAt2
      refine ⟨v,run_rtg (run_comp hu hv),?_⟩
      have hR := hV.2.2.2.2.2
      have hW := hR.2
      have hF1 := hW.2.2
      have hFF := hF1.2.2.2
      refine hV.mono ⟨hV.2.2.2.2.1,hR.1,holds_lookup hFF rfl,hW.1,hW.2.1,hF1.1,hF1.2.1,
        hV.2.2.2.2.1,hF1.2.2.1,hFF.2⟩)
  have hAlign1 (lane : Nat) (hl : lane < 32) : src1 lane%16 = 0 := by
    unfold src1 recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr _).2]
  obtain ⟨copied1,_,hCopied1⟩ := packetPairWarpOfMaximal hp hMax hg (recurringPacketSite 1) 1
    (by have := warmValueStage_lt round; change stage+0 < 3; omega) src1 (fun _ => 16)
    (fun _ _ => Nat.mod_lt _ (by decide)) hAlign1 (fun _ _ => le_rfl) ready1
  refine ⟨copied1,fun lane hl => ?_⟩
  apply (hCopied1 lane hl).2
  rw [hReady1]
  apply (hEx1 lane hl).2
  rw [hCur1]
  apply (hCopied0 lane hl).2
  rw [hReady0]
  apply (hEx0 lane hl).2
  rw [hCur0]
  exact r.upper lane hl

/-- The checkpoint before V pair `n`. The upper half begins with the second pointer reload. -/
def warmValueNextPc (n : Nat) : Nat :=
  if n = 8 then 1292 else if h : n < 16 then warmVShufflePc ⟨n,h⟩ else 1341

def warmValueSlotPair : Fin 2 → Fin 16
  | 0 => 0
  | 1 => 8

/-- The V pair checkpoint of one pointer half, independent of the pair within the half. -/
def warmRoundVHalfFrame (p : Params) (l : Launch) (g batch round : Nat) (bias : Value)
    (slot : Fin 2) (lane : Nat) : List (Nat × Value) :=
  warmRoundVPairFrame p l g batch round bias slot (warmValueSlotPair slot) lane

private theorem warmValueWordsForSlot (pair : Fin 16) (slot : Fin 2) (base : Nat)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1)) :
    warmValueWords (warmValueSlotPair slot) base = warmValueWords pair base := by
  fin_cases slot
  · change 0 ≤ pair.val ∧ pair.val < 8 at hRange
    have h : pair.val < 8 := hRange.2
    simp [warmValueWords,warmVShuffleInput,warmValueSlotPair,h]
  · change 8 ≤ pair.val ∧ pair.val < 16 at hRange
    have h : ¬ pair.val < 8 := Nat.not_lt_of_ge hRange.1
    simp [warmValueWords,warmVShuffleInput,warmValueSlotPair,h]

set_option maxRecDepth 100000 in
private theorem warmRoundVLaterPairOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round shuffles votes : Nat} {bias : Value} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (slot : Fin 2) (pair : Fin 16) (hLater : 2 ≤ pair.val)
    (hRange : 8*slot.val ≤ pair.val ∧ pair.val < 8*(slot.val+1))
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmVShufflePc pair)
      (warmRoundVHalfFrame p l g batch round bias slot) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 1) pair+2)
        (warmRoundVHalfFrame p l g batch round bias slot) (shuffles+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let ptr := fun lane => warmRoundValuePointer p l g batch round lane slot
  have hh : (assignedCoordinates p batch (g/l.block)).2/6 < p.kvHeads := by
    have hv := (assignedCoordinates_valid hp hLo hHi).2
    unfold Params.heads at hv
    omega
  have hPtr (lane : Nat) (_ : lane < 32) : ptr lane < 2^64 ∧ ptr lane%16 = 0 := by
    let row := warmRoundSlotRow p l g batch round lane slot
    obtain ⟨hEq,hLt,hAl⟩ := sourceScratchPayload_live hp 1
      (primingScratchPageBound hp (row := row) hb) (Nat.mod_lt row (by decide)) hh
    rw [hEq] at hLt hAl
    exact ⟨by simpa [ptr,warmRoundValuePointer,primingVRowPointer] using hLt,
      by simpa [ptr,warmRoundValuePointer,primingVRowPointer] using hAl⟩
  have hWords (lane : Nat) :
      warmValueWords (warmValueSlotPair slot) (ptr lane) = warmValueWords pair (ptr lane) :=
    warmValueWordsForSlot pair slot (ptr lane) hRange
  obtain ⟨start,hStart⟩ := cur.advanceLocalWithPosition (pc' := warmVShufflePc pair)
    (G := fun lane => warmValueWords pair (ptr lane) ++
      warmRoundVPairCarry l (warmValueStage round) (warpLane l g lane%l.block) ++
        warmRoundVRest p l g batch round bias lane) (by
      intro lane hl
      have hs := cur.checkpoint lane hl
      refine ⟨cur.state lane,.refl,?_⟩
      have h : warmRoundVHalfFrame p l g batch round bias slot lane =
          warmValueWords pair (ptr lane) ++
            warmRoundVPairCarry l (warmValueStage round) (warpLane l g lane%l.block) ++
              warmRoundVRest p l g batch round bias lane := by
        simp only [warmRoundVHalfFrame,warmRoundVPairFrame]
        exact congrArg (fun x => x ++ _ ++ _) (hWords lane)
      rw [← h]
      exact hs)
  obtain ⟨done,hDone⟩ := warmValueLaterPairOfMaximal hp hMax hg (warmValueStage_lt round) pair
    hLater ptr hPtr
    (fun lane _ fact hm => by
      have h : ((warmRoundVRest p l g batch round bias lane).map Prod.fst).all
          (fun r => decide (r ≠ warmVShuffleOutput pair ∧ r ≠ warmVShuffleOutput pair+1)) =
            true := by fin_cases pair <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm)))
    (fun lane _ => by fin_cases pair <;> first | contradiction | kernel_rfl)
    (fun lane _ => by
      have h := keySize_mem_vAcquired (p := p) (l := l) (g := g) (batch := batch)
        (round := round) (bias := bias) (lane := lane) pair.val pair.isLt
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ h)))) start
  obtain ⟨done',hDone'⟩ := done.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 1) pair+2)
    (G := warmRoundVHalfFrame p l g batch round bias slot) (by
      intro lane hl
      have hs := done.checkpoint lane hl
      refine ⟨done.state lane,.refl,?_⟩
      have h : warmRoundVHalfFrame p l g batch round bias slot lane =
          warmValueWords pair (ptr lane) ++
            warmRoundVPairCarry l (warmValueStage round) (warpLane l g lane%l.block) ++
              warmRoundVRest p l g batch round bias lane := by
        simp only [warmRoundVHalfFrame,warmRoundVPairFrame]
        exact congrArg (fun x => x ++ _ ++ _) (hWords lane)
      rw [h]
      exact hs)
  refine ⟨done',fun lane hl pc cell data hCell => ?_⟩
  rw [hDone']
  apply hDone lane hl
  rw [hStart]
  exact hCell

private theorem warmRoundVHalfOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch round ordinal votes first : Nat} {bias : Value} (hg : g < l.threads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (slot : Fin 2) (hFirst : 2 ≤ first ∧ 8*slot.val < first)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmValueNextPc first)
      (warmRoundVHalfFrame p l g batch round bias slot) ordinal votes ends)
    (count : Nat) (hLast : first+count ≤ 8*(slot.val+1)) :
    ∃ done : SchedulerWarpReached l X g (warmValueNextPc (first+count))
        (warmRoundVHalfFrame p l g batch round bias slot) (ordinal+2*count) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  induction count with
  | zero => exact ⟨cur,fun _ _ _ _ _ h => h⟩
  | succ k ih =>
    obtain ⟨mid,hMid⟩ := ih (by omega)
    have hSlot := slot.isLt
    let pair : Fin 16 := ⟨first+k,by omega⟩
    have hNo : pair.val ≠ 8 := by
      fin_cases slot
      · change first+k+1 ≤ 8 at hLast
        change first+k ≠ 8
        omega
      · have h := hFirst.2
        change 8 < first at h
        change first+k ≠ 8
        omega
    have hEntry : warmValueNextPc (first+k) = warmVShufflePc pair := by
      simp [warmValueNextPc,hNo,pair,show first+k < 16 by omega]
    have hExit : packetPairPc (recurringPacketSite 1) pair+2 = warmValueNextPc (first+(k+1)) := by
      have hp16 : pair.val < 16 := pair.isLt
      change packetPairPc (recurringPacketSite 1) pair+2 = warmValueNextPc (pair.val+1)
      generalize pair = q at hNo hp16 ⊢
      fin_cases q <;> first | contradiction | decide
    obtain ⟨mid',hMid'⟩ := mid.advanceLocalWithPosition (pc' := warmVShufflePc pair)
      (G := warmRoundVHalfFrame p l g batch round bias slot)
      (fun lane hl => ⟨mid.state lane,.refl,hEntry ▸ mid.checkpoint lane hl⟩)
    obtain ⟨done,hDone⟩ := warmRoundVLaterPairOfMaximal hp hMax hg hb hLo hHi slot pair
      (by dsimp [pair]; omega) ⟨by dsimp [pair]; omega,by dsimp [pair]; omega⟩ mid'
    have hN : ordinal+2*k+2 = ordinal+2*(k+1) := by omega
    rw [← hN,← hExit]
    refine ⟨done,fun lane hl _ _ _ h => hDone lane hl ?_⟩
    rw [hMid']
    exact hMid lane hl h

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
