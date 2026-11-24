-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseStore
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionVectorProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionVectorProgress
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.PlainWriteProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The actual row guard either consumes the scalar LSE store or advances
locally, preserving the caller's frame in both cases. -/
theorem finishLseTailOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g tile batch head : Nat} (hg : g < l.threads) (hw : warpIndex l g < 12)
    (stage : Fin 2) (hb : batch < p.batch) (hh : head < p.heads)
    (value : Value) (hBytes : value.bytes = 4) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g (lseGuardPc stage)
      ((lseOutReg stage,value) ::
        (7491,b64 (p.lseLoc (p.qOffset batch+stageRow tile 0+rowOf l g) head).addr) :: F))
    (hTest : c.ready.regs (lseTailPred stage) =
      some (.pred (p.qLength batch ≤ stageRow tile stage+rowOf l g))) :
    (stageRow tile stage+rowOf l g < p.qLength batch →
      X.get (g,c.pos) = some ⟨lseGuardPc stage+1,.wr
        { loc := p.lseLoc (p.qOffset batch+stageRow tile stage+rowOf l g) head
          size := 4 } value.toBytes⟩) ∧
    ∃ d : OpeningTripCursor l X g (lseGuardPc stage+2) F,
      d.pos = c.pos+(if stageRow tile stage+rowOf l g < p.qLength batch then 1 else 0) ∧
      d.ending = c.ending := by
  obtain ⟨u,hu,hLocal⟩ := lseBranchLocal stage c.checkpoint hTest
  by_cases hRow : stageRow tile stage+rowOf l g < p.qLength batch
  · rw [ite_eq_left hRow] at hu
    let a : Acc :=
      {loc := p.lseLoc (p.qOffset batch+stageRow tile stage+rowOf l g) head,size := 4}
    have hOut := lseStoreTemplate hp stage hb hh hRow value hBytes hu
      hu.2.2.2.2.1 hu.2.2.2.2.2.1
    have hn : Next kernel Assumptions.all l g c.before u (.write a value.toBytes (next u)) :=
      ⟨c.localSteps.trans hLocal,hOut⟩
    obtain ⟨he,hRecorded,hRemaining⟩ := Step.plain_write_of_maximal hMax hg rfl hn
      c.recorded c.remaining c.positive c.bounded c.released
      (fun loc req hr hEq => noCorrectionAllocation hp hMax.1 hw loc req hr (congrArg Prod.fst hEq))
      (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
    rw [hu.1] at he
    exact ⟨fun _ => he,⟨c.pos+1,next u,next u,c.ending,Nat.succ_pos _,len_of_get he,
      releasedIfLast he (by simp [Kind.resume]),hu.next.mono hu.2.2.2.2.2.2,
      hRecorded,hRemaining,.refl⟩,by simp [hRow],rfl⟩
  · rw [ite_eq_right hRow] at hu
    exact ⟨fun h => (hRow h).elim,⟨c.pos,c.before,u,c.ending,c.positive,c.bounded,c.released,
      hu.mono hu.2.2.2.2.2.2,c.recorded,c.remaining,c.localSteps.trans hLocal⟩,by simp [hRow],rfl⟩

end PTX.Kernels.TmlFa4Fwd.Correction
