-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSteadyRoundKeyPointers
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyPairSites
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketWarpProgress
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The two words of the lane's own saved pointer that a steady pair broadcasts. -/
def steadyWords (value : Bool) (pair : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(steadyPairShuffleIn value pair,b32 (base%2^32)),
   (steadyPairShuffleIn value pair+1,b32 (base/2^32))]

/-- The two words of the sender's pointer after the exchange of a steady pair. -/
def steadyExchangeWords (value : Bool) (pair : Fin 16) (base : Nat) : List (Nat × Value) :=
  [(steadyPairShuffleOut value pair,b32 (base%2^32)),
   (steadyPairShuffleOut value pair+1,b32 (base/2^32))]

theorem steadyPairShufflePc_bounds (value : Bool) (pair : Fin 16) :
    174 ≤ steadyPairShufflePc value pair ∧ steadyPairShufflePc value pair+1 < 1906 := by
  cases value <;> fin_cases pair <;> decide

/-- Both subgroup shuffles of a steady K or V pair consume the same sender's pointer and
leave the local words current. -/
theorem steadyExchangeOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (value : Bool) (pair : Fin 16)
    (ptr : Nat → Nat) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ fact ∈ steadyWords value pair (ptr lane) ++ F lane,
      fact.1 ≠ steadyPairShuffleOut value pair ∧ fact.1 ≠ steadyPairShuffleOut value pair+1)
    (cur : SchedulerWarpReached l X g (steadyPairShufflePc value pair)
      (fun lane => steadyWords value pair (ptr lane) ++ F lane) shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g (steadyPairShufflePc value pair+2) (fun lane =>
      steadyExchangeWords value pair (ptr (steadyPairSender lane pair)) ++
        steadyWords value pair (ptr lane) ++ F lane)
      (shuffles+2) votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+2 ∧
        ∀ {pc : Nat} {cell : Acc} {data : List Byte},
          PrimingCellValue X (warpLane l g lane) (cur.pos lane) pc cell data →
          PrimingCellValue X (warpLane l g lane) (done.pos lane) pc cell data := by
  let dst := steadyPairShuffleOut value pair
  let selector := pair.val%8
  let sender := fun lane => (shflSource .idx lane selector 6175).1
  let G := fun lane => steadyWords value pair (ptr lane) ++ F lane
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSelect : selector < 8 := Nat.mod_lt _ (by decide)
  have hBounds := steadyPairShufflePc_bounds value pair
  have hOut₀ (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) = .ev
        (.shfl .idx (b32 (ptr lane%2^32)) selector 6175
          (fun v _ => next (setReg (cur.state lane) dst v))) := by
    have hs := cur.checkpoint lane hl
    apply primingPointerWordTemplate hBlock hSelect
      (by rw [hs.1]; omega) (by rw [hs.1]; omega) hs.2.2.2.1
    · rw [hs.1]
      exact steadyPairShuffleCode value pair 0
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
      (by rw [hs.1]; omega) (by rw [hs.1]; omega) hs.2.2.2.1
    · rw [hs.1]
      exact steadyPairShuffleCode value pair 1
    · exact hs.2.2.2.2.2.2.1
  obtain ⟨second,hSecond⟩ := first.consumeShuffleWithEvents hp hMax hg .idx
    (fun lane => b32 (ptr lane/2^32)) (fun _ => selector) (fun _ => 6175) hFresh₁ hOut₁
  obtain ⟨done,hDone⟩ := second.advanceLocalWithPosition (pc' := steadyPairShufflePc value pair+2)
    (G := fun lane => steadyExchangeWords value pair (ptr (steadyPairSender lane pair)) ++ G lane)
    (by
      intro lane hl
      have hs := second.checkpoint lane hl
      have hSender : sender lane = steadyPairSender lane pair :=
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
