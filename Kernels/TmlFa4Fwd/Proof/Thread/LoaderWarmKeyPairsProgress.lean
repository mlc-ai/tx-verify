-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyExchange
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmFirstPackFrame
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringKeyCopyLength

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmKeyPairCarry (l : Launch) (stage tid : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  [(7666,b64 (16*(tid%8))),(2002,b32 (32768*stage)),
    (2003,b32 (kvCopyAddress l.sharedBase stage tid 0 false)),
    (2006,b32 (kvCopyAddress l.sharedBase stage tid 1 false))] ++ F

def warmKeyPairOperands (l : Launch) (stage tid : Nat) (group : Fin 16) (base : Nat)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  warmKeyWords group base ++ warmKeyPairCarry l stage tid F

def warmKeyPairMask (group : Fin 16) : Nat × Value := (169+group.val,.pred true)

set_option maxRecDepth 100000 in
/-- After computing both stage offsets, every later group uses the same straight-line copy
preparation with the particular pair's shuffle result and live mask. -/
theorem warmKeyPairReadyAfterExchange {l : Launch} {X : Execution}
    {g stage shuffles votes : Nat} (group : Fin 16) (hLater : 2 ≤ group.val) (ptr : Nat → Nat)
    (hPtr : ∀ lane < 32, ptr lane < 2^64)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFrame : ∀ lane < 32,
      ((kernel.code.drop (warmKShufflePc group+2)).take
        (packetPairPc (recurringPacketSite 0) group-(warmKShufflePc group+2))).all
        (fun i => ((F lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (cur : SchedulerWarpReached l X g (warmKShufflePc group+2) (fun lane =>
      let t := warpLane l g lane
      warmKeyExchangeWords group (ptr (warmKShuffleSender lane group)) ++
        warmKeyWords group (ptr lane) ++
        warmKeyPairMask group :: warmKeyPairCarry l stage (t%l.block)
          (F lane)) shuffles votes ends) :
    ∃ ready : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 0) group) (fun lane =>
      let t := warpLane l g lane
      packetCopyFacts l (recurringPacketSite 0) stage (t%l.block)
        (recurringSourceAddress (ptr (warmKShuffleSender lane group)) (t%l.block)) 16 group ++
        warmKeyPairOperands l stage (t%l.block) group (ptr lane) (F lane))
      shuffles votes ends, ready.pos = cur.pos := by
  apply cur.advanceLocalWithPosition
  intro lane hl
  let t := warpLane l g lane
  let tid := t%l.block
  let sender := warmKShuffleSender lane group
  let base := ptr sender
  let src := recurringSourceAddress base tid
  let entryPc := warmKShufflePc group+2
  let mid := warmKSourceCut group
  let finish := packetPairPc (recurringPacketSite 0) group
  let keep := warmKeyPairOperands l stage tid group (ptr lane) (F lane)
  let P := warmKeyPairMask group :: keep
  have hSender : sender < 32 := by
    have hByte := Nat.mod_lt group.val (by decide : 0 < 8)
    unfold sender warmKShuffleSender pointerBroadcastLane
    omega
  have hPc : mid = entryPc+2 ∧ finish = mid+1 := by
    fin_cases group <;> first | decide | contradiction
  have hLive : group.val ≠ 0 := by omega
  have hAt := cur.checkpoint lane hl
  have hStart : At (cur.state lane) entryPc (warmKPairInputs group base tid ++ P) := by
    refine hAt.mono ((holds_append ..).mpr ⟨?_,?_⟩)
    · simp only [warmKPairInputs,ite_eq_right hLive,List.cons_append,List.nil_append,Holds]
      exact ⟨hAt.2.2.2.2.1,hAt.2.2.2.2.2.1,hAt.2.2.2.2.2.2.2.2.2.1,trivial⟩
    · exact ⟨hAt.2.2.2.2.2.2.2.2.1,hAt.2.2.2.2.2.2.1,hAt.2.2.2.2.2.2.2.1,
        hAt.2.2.2.2.2.2.2.2.2⟩
  have hSpan : finish-entryPc = 3 := by omega
  have hKeep (n : Nat) (hn : n ≤ 3) :
      ((kernel.code.drop entryPc).take n).all
        (fun i => (P.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    have hmem : ins ∈ (kernel.code.drop entryPc).take 3 := List.take_subset_take_left _ hn hm
    let Lit := warmKeyPairMask group :: (warmKeyWords group (ptr lane) ++
      warmKeyPairCarry l stage tid [])
    have hSplit : P = Lit ++ F lane := by
      simp [P,Lit,keep,warmKeyPairOperands,warmKeyPairCarry,List.append_assoc]
    have hf : ((kernel.code.drop entryPc).take 3).all (fun i =>
        (Lit.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true := by
      fin_cases group <;>
        first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)
    have hF := hFrame lane hl
    change ((kernel.code.drop entryPc).take (finish-entryPc)).all _ = true at hF
    rw [hSpan] at hF
    have hw := List.all_eq_true.mp hf ins hmem
    have hFw := List.all_eq_true.mp hF ins hmem
    rw [hSplit,List.map_append,List.all_append,Bool.and_eq_true]
    exact ⟨hw,hFw⟩
  have hSource : Seg kernel [] l t 2 entryPc (warmKPairInputs group base tid)
      mid [(packetSrcReg (recurringPacketSite 0) group,b64 src)] := by
    have hn : mid-entryPc = 2 := by omega
    have h := warmKPairSourceCore (l := l) (g := t) (tid := tid) (hPtr sender hSender) group
    change Seg kernel [] l t (mid-entryPc) entryPc (warmKPairInputs group base tid)
      mid [(packetSrcReg (recurringPacketSite 0) group,b64 src)] at h
    rwa [hn] at h
  obtain ⟨u,hu,hU⟩ := straightFrame
    (by fin_cases group <;> decide) (by fin_cases group <;> decide)
    (hKeep 2 (by decide))
    (by fin_cases group <;> (set_option maxRecDepth 100000 in kernel_rfl))
    hSource hStart
  let Q := (packetSrcReg (recurringPacketSite 0) group,b64 src)::keep
  have hU' : At u mid ([(169+group.val,.pred true)]++Q) :=
    hU.mono ⟨hU.2.2.2.2.2.1,hU.2.2.2.2.1,hU.2.2.2.2.2.2⟩
  have hSel : keySelectPc false group = mid := by
    change finish-1 = mid
    omega
  have hCode := selectCode false group
  rw [hSel] at hCode
  have hChoice : Seg kernel [] l t 1 mid [(169+group.val,.pred true)]
      (mid+1) [(packetSizeReg (recurringPacketSite 0) group,b32 16)] :=
    liveKeySelectCore hCode
  obtain ⟨v,hv,hV⟩ := straightFrame
    (by fin_cases group <;> decide) (by fin_cases group <;> decide)
    (by
      have hAll := hKeep 3 le_rfl
      apply List.all_eq_true.mpr
      intro ins hi
      have hm : ins ∈ (kernel.code.drop entryPc).take 3 := by
        rw [show mid = entryPc+2 from hPc.1,← List.drop_drop] at hi
        have hStep : ((kernel.code.drop entryPc).take 3).drop 2 =
            ((kernel.code.drop entryPc).drop 2).take 1 := by
          rw [List.drop_take]
        exact List.mem_of_mem_drop (hStep.symm ▸ hi)
      have hRest := List.all_eq_true.mp hAll ins hm
      have hFresh : !(writesRegs ins.op).contains (packetSrcReg (recurringPacketSite 0) group) =
          true := by
        have hm' : ins ∈ (kernel.code.drop mid).take 1 := hi
        have hLit : ((kernel.code.drop mid).take 1).all
            (fun ins => !(writesRegs ins.op).contains
              (packetSrcReg (recurringPacketSite 0) group)) =
              true := by
          fin_cases group <;>
            first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)
        exact List.all_eq_true.mp hLit ins hm'
      simp only [Q,List.map_cons,List.all_cons,Bool.and_eq_true]
      have hRest' : ((keep.map Prod.fst).all fun r => !(writesRegs ins.op).contains r) =
          true := by
        exact (Bool.and_eq_true_iff.mp hRest).2
      exact ⟨hFresh,hRest'⟩)
    rfl hChoice hU'
  have hV' : At v finish ([(packetSizeReg (recurringPacketSite 0) group,b32 16)]++Q) :=
    hPc.2.symm ▸ hV
  have hDst : v.regs (packetDstReg (recurringPacketSite 0) group) = some
      (b32 (kvCopyAddress l.sharedBase stage tid (group.val%2) false)) := by
    have hFields := hV'.2.2.2.2
    fin_cases group <;> exact holds_lookup hFields rfl
  refine ⟨v,(run_rtg hu).trans (run_rtg hv),hV'.mono ?_⟩
  exact ⟨hDst,hV'.2.2.2.2.2.1,hV'.2.2.2.2.1,hV'.2.2.2.2.2.2⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
