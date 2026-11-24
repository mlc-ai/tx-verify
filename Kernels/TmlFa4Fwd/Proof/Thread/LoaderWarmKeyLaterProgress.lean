-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyPairsProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmKeyMasks

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A warm vector group after the base setup reaches its next checkpoint with the
same packet carry and preserves independent lane-local scratch cells. -/
theorem warmKeyLaterPairOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g stage shuffles votes : Nat} (hg : g < l.threads) (hStage : stage < 3)
    (group : Fin 16) (hLater : 2 ≤ group.val) (ptr : Nat → Nat)
    (hPtr : ∀ lane < 32, ptr lane < 2^64 ∧ ptr lane%16 = 0)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane,
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1)
    (hFrame : ∀ lane < 32,
      ((kernel.code.drop (warmKShufflePc group+2)).take
        (packetPairPc (recurringPacketSite 0) group-(warmKShufflePc group+2))).all
        (fun i => ((F lane).map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) = true)
    (cur : SchedulerWarpReached l X g (warmKShufflePc group) (fun lane =>
      let t := warpLane l g lane
      warmKeyWords group (ptr lane) ++ warmKeyPairMask group ::
        warmKeyPairCarry l stage (t%l.block) (F lane))
      shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (packetPairPc (recurringPacketSite 0) group+2) (fun lane =>
      warmKeyPairOperands l stage (warpLane l g lane%l.block) group (ptr lane) (F lane))
      (shuffles+2) votes ends,
      ∀ lane < 32,
        let t := warpLane l g lane
        let src := recurringSourceAddress (ptr (warmKShuffleSender lane group)) (t%l.block)
        done.pos lane = cur.pos lane+4 ∧
        (∀ upper : Bool, X.Copy (t,cur.pos lane+2+if upper then 1 else 0)
          (packetCopySpec l t (recurringPacketSite 0) stage (t%l.block) src 16 group upper)) ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X t (cur.pos lane) pc cell data →
          PrimingCellValue X t (done.pos lane) pc cell data := by
  let G := fun lane =>
    warmKeyPairMask group :: warmKeyPairCarry l stage (warpLane l g lane%l.block) (F lane)
  have hFresh' : ∀ lane < 32, ∀ pair ∈ warmKeyWords group (ptr lane) ++ G lane,
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1 := by
    intro lane hl pair hMem
    let Lit := warmKeyWords group (ptr lane) ++
      warmKeyPairMask group :: warmKeyPairCarry l stage (warpLane l g lane%l.block) []
    have hSplit : warmKeyWords group (ptr lane) ++ G lane = Lit ++ F lane := by
      simp [G,Lit,warmKeyPairCarry,List.append_assoc]
    rw [hSplit] at hMem
    rcases List.mem_append.mp hMem with hm | hm
    · have h : (Lit.map Prod.fst).all
          (fun r => decide (r ≠ warmKShuffleOutput group ∧ r ≠ warmKShuffleOutput group+1)) =
          true := by fin_cases group <;> exact of_decide_eq_true rfl
      exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
    · exact hFresh lane hl pair hm
  obtain ⟨exchanged,hEx⟩ := warmKeyExchangeOfMaximal hp hMax hg group ptr hFresh' cur
  obtain ⟨ready,hReady⟩ := warmKeyPairReadyAfterExchange group hLater ptr
    (fun lane hl => (hPtr lane hl).1) hFrame exchanged
  let src := fun lane =>
    recurringSourceAddress (ptr (warmKShuffleSender lane group)) (warpLane l g lane%l.block)
  have hAlign (lane : Nat) (hl : lane < 32) : src lane%16 = 0 := by
    have hSender : warmKShuffleSender lane group < 32 := by
      have hSlot := Nat.mod_lt group.val (by decide : 0 < 8)
      unfold warmKShuffleSender pointerBroadcastLane
      omega
    unfold src recurringSourceAddress
    rw [Nat.mod_mod_of_dvd _ (show 16 ∣ (2 : Nat)^64 by decide)]
    simp [Nat.add_mod,(hPtr _ hSender).2]
  obtain ⟨done,hDone,hResult⟩ := packetPairWarpOfMaximal hp hMax hg
    (recurringPacketSite 0) group hStage src (fun _ => 16)
    (fun _ _ => Nat.mod_lt _ (by decide)) hAlign (fun _ _ => le_rfl) ready
  refine ⟨done,fun lane hl => ?_⟩
  have hp := (hEx lane hl).1
  have hPos : ready.pos lane = cur.pos lane+2 := (congrFun hReady lane).trans hp
  have hStop : done.pos lane = ready.pos lane+2 := congrFun hDone lane
  refine ⟨by omega,?_,?_⟩
  · rw [← hPos]
    exact (hResult lane hl).1
  · intro pc cell data hCell
    apply (hResult lane hl).2
    rw [hReady]
    exact (hEx lane hl).2 hCell

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
