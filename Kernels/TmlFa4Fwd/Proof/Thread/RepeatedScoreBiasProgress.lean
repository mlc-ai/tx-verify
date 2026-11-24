-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreRoundProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedScoreWait

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- The sixteen pairs of each actual score quarter as a frame for the Bias acquire. -/
noncomputable def repeatedBiasPackFrame (words : Fin 4 → List Value) : List (Nat × Value) :=
  (List.finRange 4).flatMap fun q => (List.finRange 16).map fun k =>
    (repeatedScorePairReg .biased q k.val,
      joinValue ((words q).getD (2*k.val) (b32 0)) ((words q).getD (2*k.val+1) (b32 0)))

private theorem biasedPairMember (words : Fin 4 → List Value) {x : Nat × Value}
    (hx : x ∈ repeatedBiasPackFrame words) :
    ∃ (q : Fin 4) (k : Fin 16), x =
      (repeatedScorePairReg .biased q k.val,
        joinValue ((words q).getD (2*k.val) (b32 0)) ((words q).getD (2*k.val+1) (b32 0))) := by
  obtain ⟨q,_,hm⟩ := List.mem_flatMap.mp hx
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hm
  exact ⟨q,k,rfl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g phase : Nat} (hg : g < l.threads)
    (hPhase : phase < 2) {stage : Fin 2} {F : List (Nat × Value)}
    {input : OpeningTripCursor l X g (scorePc .biased 0) F}
    (c : PackedScorePrefix l X g .biased stage 4 input)
    (hBase : input.ready.regs 4037 = some (b32 (l.sharedBase+8*stage.val)))
    (hParity : input.ready.regs 7250 = some (b32 phase))
include hp hMax hg hPhase c hBase hParity

/-- The biased score collectives reach the actual next Bias acquire. An available
Bias generation is sufficient for the return, including on a suspended warp. -/
theorem PackedScorePrefix.biasedAcquireOfPending
    (hReady : (X.tr g).countP (Execution.isBarId (11+stage.val)) =
        ((X.tr g).take c.cursor.pos).countP (Execution.isBarId (11+stage.val)) →
      ∀ {t}, Run kernel Assumptions.all l g {} (X.tr g) (some t) →
        OpeningPollReady X (waitLoc l g stage 5) phase) (facts : List (Nat × Value))
    (hFacts : Holds input.ready.regs facts)
    (hPreserved : ∀ x ∈ facts, ∀ q : Fin 4, RepeatedScorePreserved .biased q x.1)
    (hFresh : ∀ x ∈ facts, x.1 ≠ 3965 ∧ x.1 ≠ 9755) :
    ∃ index, ∃ u : OpeningTripCursor l X g 5184
        ((3965,b32 (waitLoc l g stage 5).addr)::(7250,b32 phase)::
          (repeatedBiasPackFrame c.words ++ facts)),
      X.get (g,index) = some ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩ ∧
      c.cursor.pos ≤ index ∧ u.pos = index+1 ∧ u.ending = input.ending ∧
        Thread.observedBarrierOrdinal X (g,u.pos) (11+stage.val) =
          Thread.observedBarrierOrdinal X (g,c.cursor.pos) (11+stage.val) ∧
        (X.tr g).drop c.cursor.pos = List.replicate (index-c.cursor.pos)
          ⟨5181,.wait (waitLoc l g stage 5) phase false true .cta⟩ ++
          ⟨5181,.wait (waitLoc l g stage 5) phase true true .cta⟩ :: (X.tr g).drop u.pos := by
  let packed := repeatedBiasPackFrame c.words
  let carry := (7250,b32 phase)::(packed ++ facts)
  have hBase' := (c.preserved 4037 (by
    intro q _
    unfold RepeatedScorePreserved
    fin_cases q <;> decide)).trans hBase
  have hPar := (c.preserved 7250 (by
    intro q _
    unfold RepeatedScorePreserved
    fin_cases q <;> decide)).trans hParity
  have hPacked : Holds c.cursor.ready.regs packed := by
    apply frameOfFacts
    intro x hx
    obtain ⟨q,k,rfl⟩ := biasedPairMember c.words hx
    exact c.packed q q.isLt k.val k.isLt
  have hKept : Holds c.cursor.ready.regs facts := by
    apply frameOfFacts
    intro x hx
    exact (c.preserved x.1 (fun q _ => hPreserved x hx q)).trans (holds_mem hFacts hx)
  have hCarry : At c.cursor.ready 5180 carry :=
    c.cursor.checkpoint.mono ⟨hPar,(holds_append ..).mpr ⟨hPacked,hKept⟩⟩
  have hSafe (r : Nat) (hR : r = 3965 ∨ r = 9755) (x : Nat × Value)
      (hx : x ∈ carry) : x.1 ≠ r := by
    rcases List.mem_cons.mp hx with rfl | hx
    · rcases hR with rfl | rfl <;> dsimp only <;> decide
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨q,k,rfl⟩ := biasedPairMember c.words hx
      have hq := q.isLt
      have hk := k.isLt
      rcases hR with rfl | rfl <;> simp [repeatedScorePairReg] <;> omega
    · rcases hR with rfl | rfl
      · exact (hFresh x hx).1
      · exact (hFresh x hx).2
  obtain ⟨v,_,hv,hLocal⟩ := biasedWaitAddress hp stage g hCarry hBase' (hSafe 3965 (.inl rfl))
  have hWaitFresh (x : Nat × Value)
      (hx : x ∈ (3965,b32 (waitLoc l g stage 5).addr)::carry) :
      x.1 ≠ (waitSite 5).result := by
    rcases List.mem_cons.mp hx with rfl | hx
    · change (3965 : Nat) ≠ 9755
      decide
    · exact hSafe 9755 (.inr rfl) x hx
  obtain ⟨n,after,u,he,hPast,hTail,hResume,hAt,trace⟩ :=
    waitAtCountOfMaximalWithTrace hp hMax hg stage 5 hPhase hWaitFresh (.head _) (.tail _ (.head _))
      (Execution.isBarId (11+stage.val)) rfl _ (fun rank {_ _} run _ _ => hReady rank run) rfl
      c.cursor.positive c.cursor.bounded c.cursor.released hv
      c.cursor.recorded c.cursor.remaining (c.cursor.localSteps.trans hLocal)
  refine ⟨c.cursor.pos+n,
    ⟨c.cursor.pos+n+1,after,u,c.cursor.ending,Nat.succ_pos _,len_of_get he,
      Prologue.releasedIfLast he (by intro h; cases h),hAt,hPast,hTail,hResume⟩,
    he,Nat.le_add_right _ _,rfl,c.ending,?_,
    by rw [Nat.add_sub_cancel_left]; exact trace⟩
  apply repeatedScorePollKeepsCount (index := c.cursor.pos+n) (Nat.le_add_right _ _) rfl
      (mark := Execution.isBarId (11+stage.val)) (pc := (waitSite 5).pc) (phase := phase)
      (object := waitLoc l g stage 5)
  · simpa only [Nat.add_sub_cancel_left] using trace
  · intro ok
    rfl

end PTX.Kernels.TmlFa4Fwd.Softmax
