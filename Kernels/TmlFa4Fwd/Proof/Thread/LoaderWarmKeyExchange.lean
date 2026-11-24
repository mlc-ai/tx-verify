-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketWarpProgress
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The lane's original pointer words are retained for the other seven subgroup exchanges. -/
def warmKeyWords (group : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(warmKShuffleInput group,b32 (base%2^32)),
   (warmKShuffleInput group+1,b32 (base/2^32))]

def warmKeyExchangeWords (group : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(warmKShuffleOutput group,b32 (base%2^32)),
   (warmKShuffleOutput group+1,b32 (base/2^32))]

/-- Both subgroup shuffles consume the same sender's pointer and leave local words current. -/
theorem warmKeyExchangeOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (group : Fin 16) (ptr : Nat → Nat)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ pair ∈ warmKeyWords group (ptr lane) ++ F lane,
      pair.1 ≠ warmKShuffleOutput group ∧ pair.1 ≠ warmKShuffleOutput group+1)
    (cur : SchedulerWarpReached l X g (warmKShufflePc group)
      (fun lane => warmKeyWords group (ptr lane) ++ F lane) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (warmKShufflePc group+2) (fun lane =>
      warmKeyExchangeWords group (ptr (warmKShuffleSender lane group)) ++
        warmKeyWords group (ptr lane) ++ F lane)
      (shuffles+2) votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+2 ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
          PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let src := warmKShuffleInput group
  let dst := warmKShuffleOutput group
  let selector := group.val%8
  let sender := fun lane => (shflSource .idx lane selector 6175).1
  let G := fun lane => warmKeyWords group (ptr lane) ++ F lane
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSelect : selector < 8 := Nat.mod_lt _ (by decide)
  have hOut₀ (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) = .ev
        (.shfl .idx (b32 (ptr lane%2^32)) selector 6175
          (fun v _ => next (setReg (cur.state lane) dst v))) := by
    have hs := cur.checkpoint lane hl
    apply primingPointerWordTemplate hBlock hSelect
      (by rw [hs.1]; fin_cases group <;> decide)
      (by rw [hs.1]; fin_cases group <;> decide) hs.2.2.2.1
    · rw [hs.1]
      exact warmKShuffleCode group 0
    · exact hs.2.2.2.2.1
  obtain ⟨first,hFirst⟩ := cur.consumeShuffleWithEvents hp hMax hg .idx
    (fun lane => b32 (ptr lane%2^32)) (fun _ => selector) (fun _ => 6175)
    (fun lane hl pair hPair => (hFresh lane hl pair hPair).1) hOut₀
  have hFresh₁ (lane : Nat) (hl : lane < 32) :
      ∀ pair ∈ (dst,b32 (ptr (sender lane)%2^32))::G lane, pair.1 ≠ dst+1 := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact (hFresh lane hl pair hm).2
  have hOut₁ (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (first.state lane) = .ev
        (.shfl .idx (b32 (ptr lane/2^32)) selector 6175
          (fun v _ => next (setReg (first.state lane) (dst+1) v))) := by
    have hs := first.checkpoint lane hl
    apply primingPointerWordTemplate hBlock hSelect
      (by rw [hs.1]; fin_cases group <;> decide)
      (by rw [hs.1]; fin_cases group <;> decide) hs.2.2.2.1
    · rw [hs.1]
      exact warmKShuffleCode group 1
    · exact hs.2.2.2.2.2.2.1
  obtain ⟨second,hSecond⟩ := first.consumeShuffleWithEvents hp hMax hg .idx
    (fun lane => b32 (ptr lane/2^32)) (fun _ => selector) (fun _ => 6175) hFresh₁ hOut₁
  obtain ⟨done,hDone⟩ := second.advanceLocalWithPosition (pc' := warmKShufflePc group+2)
    (G := fun lane => warmKeyExchangeWords group (ptr (warmKShuffleSender lane group)) ++ G lane)
    (by
      intro lane hl
      have hs := second.checkpoint lane hl
      have hSender : sender lane = warmKShuffleSender lane group :=
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

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
