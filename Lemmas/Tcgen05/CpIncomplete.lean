-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcReadFinishCp
public import Lemmas.Tcgen05.TcFence

@[expose] public section

/-! # What can source a copy that is not done

A `tcgen05.cp` that has not completed is the source of a Tensor Memory write only through the
copy-to-A pipeline: a write before another event, with the copy not done, is a pipelined pair of
copy write and A read (`incomplete_cp_pipelined`), so it is no load's source
(`no_ld_source_of_incomplete_cp`). -/

namespace PTX
open AsyncCopy

noncomputable section

variable {L : Launch} {X : Execution}

/-- A pending copy's write is before another event only through the copy-to-A pipeline. -/
theorem incomplete_cp_pipelined {g i : Nat} {w : EvId} {c : TcCopy.Spec}
    (hCopy : X.CpIssue (g, i) c) (hCommit : CommitOk X)
    (hDone : X.async.mmaDone (g, i) = false)
    (h : TcMma.WriteBefore L X (g, i) w) :
    TcMma.Pipelined L X .cpWrite (g, i) .aRead w := by
  have apart : ∀ e, X.get (g, i) = some e → e.kind = .tc (.cp c) :=
    fun e he => congrArg Event.kind (Option.some.inj (he.symm.trans hCopy.choose_spec))
  rcases h with ⟨hBefore | hPipe⟩ | hStore | hPipe
  · have h := hDone.symm.trans (TcMma.DoneBefore.done hBefore hCommit)
    cases h
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, hm, _, _⟩ := hPipe
    cases apart _ hm.choose_spec
  · obtain ⟨_, _, _, hSt⟩ := hStore.1
    cases apart _ hSt.choose_spec
  · exact hPipe

/-- A pending query copy cannot be a Tensor Memory load's read source. -/
theorem no_ld_source_of_incomplete_cp {g i : Nat} {w : EvId} {c : TcCopy.Spec}
    {addr : Nat} {vals : List Value} {shape : TcShape}
    (hCopy : X.CpIssue (g, i) c) (hCommit : CommitOk X)
    (hDone : X.async.mmaDone (g, i) = false) (hLoad : X.TLd w addr vals shape)
    (cell : TcMma.Cell) : ¬ TcMma.ReadSource L X .ld (g, i) w cell := by
  intro hSource
  obtain ⟨_, _, _, _, _, _, _, _, _, hMma, _⟩ :=
    incomplete_cp_pipelined hCopy hCommit hDone hSource.2.2.1
  have h := congrArg Event.kind (Option.some.inj (hLoad.choose_spec.symm.trans hMma.choose_spec))
  cases h

/-- **Finishing the copy `i` keeps the Tensor Memory read rule**, whatever operand snapshot it
takes. -/
def CpReadKept (L : Launch) (A : List Assumption) (X : Execution) (i : EvId) : Prop :=
  ∀ (v : MmaOperands) (ra rb : Nat → Option AsyncCopy.Ref),
    TcMma.ReadOk L A (X.finishMma i v ra rb)

end
end PTX
