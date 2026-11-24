-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaShuffleExit
import Lemmas.Order.ElectOrdinal
import Lemmas.Flow.ElectMask

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow

private theorem shflMate {l : Launch} {X : Execution} {g h i j rank : Nat}
    {mode : ShflMode} {pos pos' b c b' c' : Nat} {a a' r r' : Value} {ok ok' : Bool}
    (hw : SameWarp l g h)
    (he : X.get (g,i) = some ⟨pos,.shfl mode a b c r ok⟩) (hi : X.ShflK (g,i) rank)
    (hf : X.get (h,j) = some ⟨pos',.shfl mode a' b' c' r' ok'⟩) (hj : X.ShflK (h,j) rank) :
    Witness l X (.thread (g,i)) (h,j) := by
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hBit : (2^32-1 : Nat).testBit (laneOf l g) = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hLane
  have hNeed := maskNeeds_mem l shflClass X (h,j) hf rfl hLane hBit
  rw [Step.warpLane_of_sameWarp (sameWarp_symm hw)] at hNeed
  have hAt : X.MaskAt shflClass (h,j) (2^32-1) rank mode :=
    ⟨(maskK_shflClass _ _ _ _).mpr ⟨rfl,hj⟩,_,_,hf,rfl,rfl⟩
  have hPeer : X.MaskAt shflClass (g,i) (2^32-1) rank mode :=
    ⟨(maskK_shflClass _ _ _ _).mpr ⟨rfl,hi⟩,_,_,he,rfl,rfl⟩
  have hn : Need.node (fun x => ∃ n, x = .thread (g,n) ∧
      MaskWait l shflClass X (g,n) (h,j)) ∈ Needs l X (h,j) := by
    simpa only [Needs,hf,KindNeeds] using hNeed
  exact Witness.of_need l hn ⟨_,he⟩ ⟨i,rfl,hw,_,_,_,hAt,.inl hPeer⟩

variable {l : Launch} {m : Mem0} {X : Execution}

private theorem electionCountLeAtShuffle (hX : Consistent l kernel Assumptions.all m X)
    {g h i j rank : Nat} {mode : ShflMode} {pos pos' b c b' c' : Nat} {a a' r r' : Value}
    {ok ok' : Bool} (hw : SameWarp l g h) (he : X.get (g,i) = some ⟨pos,.shfl mode a b c r ok⟩)
    (hi : X.ShflK (g,i) rank) (hf : X.get (h,j) = some ⟨pos',.shfl mode a' b' c' r' ok'⟩)
    (hj : X.ShflK (h,j) rank) (hm : ElectMutual l X)
    (hFull : ∀ {k pc mask inst lead}, X.Elect (g,k) pc mask inst lead →
      electMember mask (laneOf l h)) :
    elections X g i ≤ elections X h j := by
  by_contra! hGt
  obtain ⟨k,hki,e,hE,hElect,hRank⟩ := Flow.exists_nth isElectEv (X.tr g)
    (n := elections X h j) (k := i) hGt
  obtain ⟨pc,mask,inst,lead,rfl⟩ : ∃ pc mask inst lead, e = ⟨pc,.elect mask inst lead⟩ := by
    obtain ⟨pc,kind⟩ := e
    cases kind <;> simp_all [isElectEv]
  have hEk : X.Elect (g,k) pc mask inst lead := hE
  obtain ⟨n,hPair⟩ := ElectOrd.partner hX hw hEk (hFull hEk)
  obtain ⟨p,q,mask',mask'',inst',lead',lead'',hK,hN⟩ := hPair
  have hCount := electOrdinal hX hm hw hK hN
  change elections X g k = elections X h n at hCount
  change elections X g k = elections X h j at hRank
  have hLater : j < n := by
    by_contra! hLe
    rcases Nat.lt_or_eq_of_le hLe with hlt | rfl
    · have hNCount := ElectOrd.elections_succ hN
      have hMono := countP_take_mono isElectEv (X.tr h) (show n+1 ≤ j by omega)
      change elections X h (n+1) ≤ elections X h j at hMono
      omega
    · cases congrArg Event.kind (Option.some.inj (hf.symm.trans hN))
  have hFirst := ElectOrd.resumes (L := l) (K := kernel) hEk hki (PTX.len_of_get he)
  have hPeer := DepStep.of_witness (K := kernel) l (shflMate hw he hi hf hj)
  have hNext : DepStep l kernel X (.thread (h,j),true) (.thread (h,n),false) :=
    .of_resumes l (Resumes.of_blocking hf rfl ⟨rfl,hLater,ElectOrd.lt_len hN⟩)
  have hBack := ElectOrd.depStep hX (sameWarp_symm hw)
    (show ElectOrd.Partner X (h,n) (g,k) from ⟨q,p,mask'',mask',inst',lead'',lead',hN,hK⟩)
  exact hX.depStepAcyclic _ ((((Relation.TransGen.single hFirst).tail hPeer).tail hNext).tail hBack)

private def fullElectOp : Op → Bool
  | .warp ⟨.elect,_,_,_,mask⟩ => mask == some (.imm (-1))
  | _ => true

set_option maxRecDepth 100000 in
private theorem fullElectionCode : kernel.code.all (fun ins => fullElectOp ins.op) = true := by
  kernel_rfl

/-- Every election actually issued by the kernel names the entire warp. -/
theorem actualFullElectionMask (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {pc mask inst lead : Nat} (h : X.Elect i pc mask inst lead) : mask = 2^32-1 := by
  have hGet : X.get i = some ⟨pc,.elect mask inst lead⟩ := h
  obtain ⟨ins,ty,d,p,mk,hCode,hOp,t,bits,hRead,hMask⟩ :=
    elect_mask (hX.thr _ (event_thread_lt hX hGet)) (List.mem_of_getElem? hGet) rfl
  have hFull := List.all_eq_true.mp fullElectionCode ins (List.mem_of_getElem? hCode)
  rw [hOp] at hFull
  have hOperand : mk = .imm (-1) := by simpa only [fullElectOp,beq_iff_eq,Option.some.injEq]
    using hFull
  subst mk
  have hRead' : readBits l i.1 t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 (2^32-1)) := rfl
  rw [hRead'] at hRead
  obtain rfl := Except.ok.inj hRead
  exact hMask.symm

/-- A matched pair of actual shuffles cuts the same number of elections.
Opposite ordering of a full-mask election and a matching shuffle would create a dependency cycle. -/
theorem electionCountAtMatchedShuffle (hX : Consistent l kernel Assumptions.all m X)
    {g h i j rank : Nat} {mode : ShflMode} {pos pos' b c b' c' : Nat} {a a' r r' : Value}
    {ok ok' : Bool} (hw : SameWarp l g h) (he : X.get (g,i) = some ⟨pos,.shfl mode a b c r ok⟩)
    (hi : X.ShflK (g,i) rank) (hf : X.get (h,j) = some ⟨pos',.shfl mode a' b' c' r' ok'⟩)
    (hj : X.ShflK (h,j) rank) :
    elections X g i = elections X h j := by
  have hm : ElectMutual l X := ElectMutual.of_full (L := l) (by
    intro e pc mask inst lead he
    exact actualFullElectionMask hX he)
  have hMember {peer mask : Nat} (h : mask = 2^32-1) : electMember mask (laneOf l peer) := by
    subst mask
    have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
    refine ⟨hLane,?_⟩
    rw [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact hLane
  exact Nat.le_antisymm
    (electionCountLeAtShuffle hX hw he hi hf hj hm (fun h => hMember (actualFullElectionMask hX h)))
    (electionCountLeAtShuffle hX (sameWarp_symm hw) hf hj he hi hm
      (fun h => hMember (actualFullElectionMask hX h)))

end PTX.Kernels.TmlFa4Fwd.Thread
