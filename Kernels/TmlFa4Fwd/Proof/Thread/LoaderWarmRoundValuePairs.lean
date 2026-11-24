-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundValuePointers
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePairSites
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmValuePairSites
import all Kernels.TmlFa4Fwd.Proof.LoaderRecurringDestinations
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part020

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

def warmValueWords (pair : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(warmVShuffleInput pair,b32 (base%2^32)),
   (warmVShuffleInput pair+1,b32 (base/2^32))]

def warmValueExchangeWords (pair : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(warmVShuffleOutput pair,b32 (base%2^32)),
   (warmVShuffleOutput pair+1,b32 (base/2^32))]

/-- Both subgroup shuffles of a V pair consume the same sender's pointer and leave the local
words current. -/
theorem warmValueExchangeOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (pair : Fin 16) (ptr : Nat → Nat)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ fact ∈ warmValueWords pair (ptr lane) ++ F lane,
      fact.1 ≠ warmVShuffleOutput pair ∧ fact.1 ≠ warmVShuffleOutput pair+1)
    (cur : SchedulerWarpReached l X g (warmVShufflePc pair)
      (fun lane => warmValueWords pair (ptr lane) ++ F lane) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmVShufflePc pair+2) (fun lane =>
      warmValueExchangeWords pair (ptr (warmVShuffleSender lane pair)) ++
        warmValueWords pair (ptr lane) ++ F lane)
      (shuffles+2) votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+2 ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
          PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let dst := warmVShuffleOutput pair
  let selector := pair.val%8
  let sender := fun lane => (shflSource .idx lane selector 6175).1
  let G := fun lane => warmValueWords pair (ptr lane) ++ F lane
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSelect : selector < 8 := Nat.mod_lt _ (by decide)
  have hOut₀ (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) = .ev
        (.shfl .idx (b32 (ptr lane%2^32)) selector 6175
          (fun v _ => next (setReg (cur.state lane) dst v))) := by
    have hs := cur.checkpoint lane hl
    apply primingPointerWordTemplate hBlock hSelect
      (by rw [hs.1]; fin_cases pair <;> decide)
      (by rw [hs.1]; fin_cases pair <;> decide) hs.2.2.2.1
    · rw [hs.1]
      exact warmVShuffleCode pair 0
    · exact hs.2.2.2.2.1
  obtain ⟨first,hFirst⟩ := cur.consumeShuffleWithEvents hp hMax hg .idx
    (fun lane => b32 (ptr lane%2^32)) (fun _ => selector) (fun _ => 6175)
    (fun lane hl fact hFact => (hFresh lane hl fact hFact).1) hOut₀
  have hFresh₁ (lane : Nat) (hl : lane < 32) :
      ∀ fact ∈ (dst,b32 (ptr (sender lane)%2^32))::G lane, fact.1 ≠ dst+1 := by
    intro fact hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact (hFresh lane hl fact hm).2
  have hOut₁ (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (first.state lane) = .ev
        (.shfl .idx (b32 (ptr lane/2^32)) selector 6175
          (fun v _ => next (setReg (first.state lane) (dst+1) v))) := by
    have hs := first.checkpoint lane hl
    apply primingPointerWordTemplate hBlock hSelect
      (by rw [hs.1]; fin_cases pair <;> decide)
      (by rw [hs.1]; fin_cases pair <;> decide) hs.2.2.2.1
    · rw [hs.1]
      exact warmVShuffleCode pair 1
    · exact hs.2.2.2.2.2.2.1
  obtain ⟨second,hSecond⟩ := first.consumeShuffleWithEvents hp hMax hg .idx
    (fun lane => b32 (ptr lane/2^32)) (fun _ => selector) (fun _ => 6175) hFresh₁ hOut₁
  obtain ⟨done,hDone⟩ := second.advanceLocalWithPosition (pc' := warmVShufflePc pair+2)
    (G := fun lane => warmValueExchangeWords pair (ptr (warmVShuffleSender lane pair)) ++ G lane)
    (by
      intro lane hl
      have hs := second.checkpoint lane hl
      have hSender : sender lane = warmVShuffleSender lane pair :=
        congrArg Prod.fst (kv_shuffle_source ⟨lane,hl⟩ ⟨selector,hSelect⟩)
      refine ⟨second.state lane,.refl,hs.mono ?_⟩
      exact ⟨by simpa only [← hSender] using hs.2.2.2.2.2.1,
        by simpa only [← hSender] using hs.2.2.2.2.1,hs.2.2.2.2.2.2⟩)
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨hp₀,_,_,he₀,_⟩ := hFirst lane hl
  obtain ⟨hp₁,_,_,he₁,_⟩ := hSecond lane hl
  simp only [hDone,hp₁,hp₀]
  refine ⟨trivial,fun hCell => ?_⟩
  have hCell' := hCell.step hMax.1 he₀ (by intro _ _ h; cases h)
  rw [← hp₀] at hCell'
  have hCell'' := hCell'.step hMax.1 he₁ (by intro _ _ h; cases h)
  simpa only [hp₀] using hCell''

/-- The lane column and both destination bases shared by all V pairs after the first two. -/
def warmRoundVPairCarry (l : Launch) (stage tid : Nat) : List (Nat × Value) :=
  [(7721,b64 (16*(tid%8))),(2082,b32 (kvCopyAddress l.sharedBase stage tid 0 false)),
    (2085,b32 (kvCopyAddress l.sharedBase stage tid 1 false))]

set_option maxRecDepth 100000 in
/-- A V pair after the first two exchanges its pointer, forms its source address and issues
both vectors with the destination bases and the K packet's size operand. -/
theorem warmValueLaterPairOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g stage shuffles votes : Nat} (hg : g < l.threads) (hStage : stage < 3)
    (pair : Fin 16) (hLater : 2 ≤ pair.val) (ptr : Nat → Nat)
    (hPtr : ∀ lane < 32, ptr lane < 2^64 ∧ ptr lane%16 = 0)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ fact ∈ F lane,
      fact.1 ≠ warmVShuffleOutput pair ∧ fact.1 ≠ warmVShuffleOutput pair+1)
    (hFrame : ∀ lane < 32, ((kernel.code.drop (warmVShufflePc pair+2)).take 2).all
      (fun i => ((F lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (hSize : ∀ lane < 32, (packetSizeReg (recurringPacketSite 1) pair,b32 16) ∈ F lane)
    (cur : SchedulerWarpReached l X g (warmVShufflePc pair) (fun lane =>
      warmValueWords pair (ptr lane) ++
        warmRoundVPairCarry l stage (warpLane l g lane%l.block) ++ F lane)
      shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 1) pair+2) (fun lane =>
      warmValueWords pair (ptr lane) ++
        warmRoundVPairCarry l stage (warpLane l g lane%l.block) ++ F lane)
      (shuffles+2) votes ends,
      ∀ lane < 32, ∀ {pc : Nat} {cell : Acc} {data : List Byte},
        PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
        PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let K := fun lane => warmValueWords pair (ptr lane) ++
    warmRoundVPairCarry l stage (warpLane l g lane%l.block) ++ F lane
  have hFresh' : ∀ lane < 32, ∀ fact ∈ K lane,
      fact.1 ≠ warmVShuffleOutput pair ∧ fact.1 ≠ warmVShuffleOutput pair+1 := by
    intro lane hl fact hMem
    rcases List.mem_append.mp hMem with hm | hm
    · have h : ((warmValueWords pair (ptr lane) ++
          warmRoundVPairCarry l stage (warpLane l g lane%l.block)).map Prod.fst).all
          (fun r => decide (r ≠ warmVShuffleOutput pair ∧ r ≠ warmVShuffleOutput pair+1)) =
          true := by fin_cases pair <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
    · exact hFresh lane hl fact hm
  obtain ⟨exchanged,hEx⟩ := warmValueExchangeOfMaximal hp hMax hg pair ptr
    (F := fun lane => warmRoundVPairCarry l stage (warpLane l g lane%l.block) ++ F lane)
    (fun lane hl fact hm => hFresh' lane hl fact (by simpa [K,List.append_assoc] using hm)) (by
      simpa only [List.append_assoc] using cur)
  have hNot0 : pair.val ≠ 0 := by omega
  have hCut : warmVSourceCut pair = warmVShufflePc pair+2+2 := by
    simp [warmVSourceCut,hNot0]
  have hPairPc : packetPairPc (recurringPacketSite 1) pair = warmVSourceCut pair := by
    fin_cases pair <;> first | contradiction | decide
  let src := fun lane =>
    recurringSourceAddress (ptr (warmVShuffleSender lane pair)) (warpLane l g lane%l.block)
  obtain ⟨ready,hReady⟩ := exchanged.advanceLocalWithPosition
    (pc' := packetPairPc (recurringPacketSite 1) pair)
    (G := fun lane => packetCopyFacts l (recurringPacketSite 1) stage (warpLane l g lane%l.block)
      (src lane) 16 pair ++ K lane) (by
      intro lane hl
      let t := warpLane l g lane
      let tid := t%l.block
      have hTid : tid < 512 := by dsimp [tid]; rw [hp.block]; exact Nat.mod_lt _ (by decide)
      have hSender : warmVShuffleSender lane pair < 32 := by
        have := Nat.mod_lt pair.val (by decide : 0 < 8)
        unfold warmVShuffleSender pointerBroadcastLane
        omega
      have hs := exchanged.checkpoint lane hl
      have hIn : At (exchanged.state lane) (warmVShufflePc pair+2)
          (warmVPairInputs pair (ptr (warmVShuffleSender lane pair)) tid ++ K lane) := by
        refine hs.mono ((holds_append ..).mpr ⟨?_,?_⟩)
        · simp only [warmVPairInputs,ite_eq_right hNot0,List.cons_append,List.nil_append,Holds]
          exact ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,trivial⟩
        · exact hs.2.2.2.2.2.2
      have hCore := warmVPairSourceCore (l := l) (g := t) (hPtr _ hSender).1 hTid pair
      rw [hCut,show warmVShufflePc pair+2+2-(warmVShufflePc pair+2) = 2 by omega] at hCore
      have hKeep : ((kernel.code.drop (warmVShufflePc pair+2)).take 2).all
          (fun i => ((K lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) =
            true := by
        have hLit : ((kernel.code.drop (warmVShufflePc pair+2)).take 2).all
            (fun i => ((warmValueWords pair (ptr lane) ++
              warmRoundVPairCarry l stage tid).map Prod.fst).all
              (fun r => !(writesRegs i.op).contains r)) = true := by
          fin_cases pair <;> first | contradiction | (set_option maxRecDepth 100000 in kernel_rfl)
        apply List.all_eq_true.mpr
        intro ins hm
        have h1 := List.all_eq_true.mp hLit ins hm
        have h2 := List.all_eq_true.mp (hFrame lane hl) ins hm
        simp only [K,List.map_append,List.all_append,Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨h1,h2⟩
      obtain ⟨u,hu,hU⟩ := roundStraightFrame
        (by fin_cases pair <;> decide) (by fin_cases pair <;> decide) hKeep
        (by fin_cases pair <;> first | contradiction | (set_option maxRecDepth 100000 in
            kernel_rfl))
        hCore hIn
      refine ⟨u,run_rtg hu,?_⟩
      rw [hPairPc,hCut]
      refine hU.mono ((holds_append ..).mpr ⟨?_,hU.2.2.2.2.2⟩)
      have hK : Holds u.regs (K lane) := hU.2.2.2.2.2
      have hCarry := ((holds_append ..).mp ((holds_append ..).mp hK).1).2
      refine ⟨?_,hU.2.2.2.2.1,holds_mem ((holds_append ..).mp hK).2 (hSize lane hl),trivial⟩
      have hParity : packetDstReg (recurringPacketSite 1) pair =
          (if pair.val%2 = 0 then 2082 else 2085) := by
        fin_cases pair <;> rfl
      rw [hParity]
      have hm := Nat.mod_lt pair.val (by decide : 0 < 2)
      by_cases hEven : pair.val%2 = 0
      · rw [ite_eq_left hEven,hEven]
        exact hCarry.2.1
      · rw [ite_eq_right hEven,show pair.val%2 = 1 by omega]
        exact hCarry.2.2.1)
  have hAlign (lane : Nat) (hl : lane < 32) : src lane%16 = 0 := by
    have hSender : warmVShuffleSender lane pair < 32 := by
      have := Nat.mod_lt pair.val (by decide : 0 < 8)
      unfold warmVShuffleSender pointerBroadcastLane
      omega
    unfold src recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr _ hSender).2]
  obtain ⟨done,_,hResult⟩ := packetPairWarpOfMaximal hp hMax hg
    (recurringPacketSite 1) pair (by change stage+0 < 3; omega) src (fun _ => 16)
    (fun _ _ => Nat.mod_lt _ (by decide)) hAlign (fun _ _ => le_rfl) ready
  refine ⟨done,fun lane hl pc cell data hCell => ?_⟩
  apply (hResult lane hl).2
  rw [hReady]
  exact (hEx lane hl).2 hCell

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
