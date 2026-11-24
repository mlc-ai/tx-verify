-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionOutputStores
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalizeNumerics
public import Kernels.TmlFa4Fwd.Proof.CorrectionTripReads
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocationValue
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.PlainWriteProgress
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Epilogue Prologue

private theorem noCorrectionAllocation {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (hw : warpIndex l g < 12) :
    ∀ c r, r ∈ X.tmemHistory c → (r.own.event l 0).1 ≠ g := by
  intro c r hr hEq
  have hCovered := (hX.tmemPair.1 c).1 r hr
  have hActor := (Tmem.Pair.WarpRequest.event_props hCovered.2.2 0).2.1
  rw [hEq,Thread.allocatorWarp hp hX hr] at hActor
  change warpIndex l g = 12 at hActor
  omega

/-- All four scalar write events of a reached staging vector occur in the maximal
trace. The final callback records the cursor at the next instruction. -/
theorem outputVectorOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12)
    (stage : Fin 2) (subbox : Fin 4) (chunk : Fin 8) (value : Fin 4 → Value)
    {F : List (Nat × Value)} (c : OpeningTripCursor l X g (outputStorePc stage subbox chunk) F)
    (hAddress : c.ready.regs (outputStoreAddrReg stage chunk) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) chunk.val).addr))
    (hValue : ∀ k, c.ready.regs (outputStoreValueReg stage subbox chunk k) = some (value k))
    (hBytes : ∀ k, (value k).bytes = 4) :
    (∀ k : Fin 4, X.get (g,c.pos+k.val) = some ⟨outputStorePc stage subbox chunk,
      .wr {
        loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4*k.val)
        size := 4
        elem := k.val } (value k).toBytes⟩) ∧
    ∃ d : OpeningTripCursor l X g (outputStorePc stage subbox chunk+1) F,
      d.pos = c.pos+4 ∧ d.ending = c.ending := by
  let state (n : Nat) := if n < 4 then {c.ready with sub := n} else next c.ready
  let site := outputStorePc stage subbox chunk
  let srcs := outputOperands stage subbox chunk
  let access (k : Fin 4) : Acc :=
    { loc := (outputChunkLoc l g stage subbox (rowOf l g) chunk.val).at (4*k.val)
      size := 4
      elem := k.val }
  let observed (k : Fin 4) := X.get (g,c.pos+k.val) = some ⟨site,.wr (access k) (value k).toBytes⟩
  have step (n : Nat) (hn : n ≤ 4) :
      ∃ before,
        Relation.ReflTransGen (Tau kernel Assumptions.all l g) before (state n) ∧
        Run kernel Assumptions.all l g {} ((X.tr g).take (c.pos+n)) (some before) ∧
        Run kernel Assumptions.all l g before ((X.tr g).drop (c.pos+n)) c.ending ∧
        c.pos+n ≤ (X.tr g).length ∧ (c.pos+n = (X.tr g).length → Step.Released l X g) ∧
        ∀ k : Fin 4, k.val < n → observed k := by
    induction n with
    | zero =>
      have hState : state 0 = c.ready := by
        change {c.ready with sub := 0} = c.ready
        rw [← c.checkpoint.2.1]
      rw [hState,Nat.add_zero]
      exact ⟨c.before,c.localSteps,c.recorded,c.remaining,c.bounded,c.released,
        fun k hk => (Nat.not_lt_zero k.val hk).elim⟩
    | succ n ih =>
      obtain ⟨before,hLocal,hPast,hTail,hBound,hRelease,hPrevious⟩ :=
        ih (Nat.le_of_succ_le hn)
      let k : Fin 4 := ⟨n,by omega⟩
      have hState : state n = {c.ready with sub := n} := ite_eq_left k.isLt
      have hNext : afterStore (state n) srcs = state (n+1) := by
        have hLen : srcs.length = 4 := List.length_ofFn
        rw [hState]
        simp only [afterStore,hLen,state]
        split
        · rfl
        · rw [next,c.checkpoint.2.1]
      have hPc : (state n).pc = site := by rw [hState]; exact c.checkpoint.1
      have hOut := outputStoreElementTemplate hp stage subbox chunk k (value k) (hBytes k)
        hPc (by rw [hState]) (by rw [hState]; exact c.checkpoint.2.2.2.1)
        (by rw [hState]; exact hAddress) (by rw [hState]; exact hValue k)
      rw [hNext] at hOut
      have hRun : Next kernel Assumptions.all l g before (state n)
          (.write (access k) (value k).toBytes (state (n+1))) := ⟨hLocal,hOut⟩
      obtain ⟨he,hPrefix,hRest⟩ := Step.plain_write_of_maximal hMax hg rfl hRun hPast hTail
        (by have := c.positive; omega) hBound hRelease
        (fun loc rec hr hEq =>
          noCorrectionAllocation hp hMax.1 hw loc rec hr (congrArg Prod.fst hEq))
        (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
      rw [hPc] at he
      have hRecorded : observed k := he
      have hLen : c.pos+n < (X.tr g).length := len_of_get he
      refine ⟨state (n+1),.refl,by simpa only [Nat.add_assoc] using hPrefix,
        by simpa only [Nat.add_assoc] using hRest,by omega,
        ?_,?_⟩
      · simpa only [Nat.add_assoc] using releasedIfLast he (by simp [Kind.resume])
      · intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hLt | hEq
        · exact hPrevious i hLt
        · exact (show i = k from Fin.ext hEq) ▸ hRecorded
  obtain ⟨before,hLocal,hPast,hTail,hBound,hRelease,hGet⟩ := step 4 (by decide)
  have hAt : At (state 4) (site+1) F := c.checkpoint.next
  exact ⟨fun k => hGet k k.isLt,
    ⟨c.pos+4,before,state 4,c.ending,by omega,hBound,hRelease,hAt,hPast,hTail,hLocal⟩,rfl,rfl⟩

/-- A ready normalized half-chunk unpacks and records the actual writes of
its shared vector while retaining the carried address and statistics frame. -/
theorem normalizedVectorOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12)
    (stage : Fin 2) (chunk : Fin 16) (half : Fin 2) (old : Nat → ℝ) (reciprocal : ℝ)
    {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (outputStorePc stage (finalizeSubset chunk)
      (finalizeVector chunk half)-2) (finalizeProductFacts stage chunk old reciprocal ++ F))
    (hAddr : c.ready.regs (outputStoreAddrReg stage (finalizeVector chunk half)) =
      some (b32 (outputChunkLoc l g stage 0 (rowOf l g) (finalizeVector chunk half).val).addr))
    (hFresh : ∀ r ∈ F.map Prod.fst, ∀ q ∈ finalizeUnpacks stage chunk half, q.2.1 ≠ r ∧ q.2.2 ≠ r) :
    (∀ k : Fin 4, X.get (g,c.pos+k.val) = some
      ⟨outputStorePc stage (finalizeSubset chunk) (finalizeVector chunk half),
        .wr {
          loc := (outputChunkLoc l g stage (finalizeSubset chunk) (rowOf l g)
            (finalizeVector chunk half).val).at (4*k.val)
          size := 4
          elem := k.val } (fl (old (4*half.val+k.val)*reciprocal)).toBytes⟩) ∧
    ∃ d : OpeningTripCursor l X g (outputStorePc stage (finalizeSubset chunk)
      (finalizeVector chunk half)+1) F, d.pos = c.pos+4 ∧ d.ending = c.ending := by
  obtain ⟨u,hAt,hAddr',hWords,hLocal⟩ :=
    finalizeUnpackLocal (l := l) (g := g) stage chunk half old reciprocal c.checkpoint hAddr hFresh
  let atStore : OpeningTripCursor l X g (outputStorePc stage (finalizeSubset chunk)
      (finalizeVector chunk half)) F :=
    ⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,hAt,c.recorded,
      c.remaining,c.localSteps.trans hLocal⟩
  exact outputVectorOfMaximal hp hMax hg hw stage (finalizeSubset chunk)
    (finalizeVector chunk half) (fun k => fl (old (4*half.val+k.val)*reciprocal))
    atStore hAddr' hWords (fun _ => rfl)

end PTX.Kernels.TmlFa4Fwd.Correction
