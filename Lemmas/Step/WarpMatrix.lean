-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.MatrixAppend

@[expose] public section

/-! # A warp-level matrix instruction performed by a whole warp

A proof tool, the counterpart of `Lemmas/Step/WarpShfl.lean` for the warp-level matrix
instructions (`ldmatrix`, `stmatrix`, `movmatrix`, `mma.sync`). A lane's matrix event
`.matrix op own recv` is ready only with the matrix events of the same ordinal of the 32 lanes of
its warp (DEP-ORDER), and receives the bytes `matrixRecv` computes from all lanes' contributions
(DEP-WARP-MATRIX), so the warp performs the instance at once.

* The lanes of a warp that have not exited have made equally many matrix events
  (`matrix_count_eq`, from DEP-ORDER), so the next matrix event of each lane belongs to one
  instance.
* `matrix_counted_extension`: when every thread of `g`'s warp can perform the matrix event of
  operation `op` at `pc` with its contribution `own h`, in a CTA whose size is a multiple of 32,
  the warp performs one instance. This is a counted extension. The received bytes are chosen by
  the lemma (`exists_matrixResultOk`): the computed bytes, or any bytes when a lane's result
  cannot be computed, in which case the extension is `MatrixUnsafe`.
* `matrix_extension_of_results` is the same step with the received bytes given by the caller
  (`MatrixResultOk`, for instance from `MatrixResultOk.of_bytes` when every lane's result is
  defined); it names the extension.

Only the `.matrix` events need these lemmas. A lane of `ldmatrix` that supplies a row first
performs an ordinary read of the 16 bytes of its row, and a supplier lane of `stmatrix` performs
an ordinary write of the 16 bytes it received after its matrix event (THREAD-MATRIX): those are
free events, appended one lane at a time by the read and plain-write extension lemmas
(`Step.read_source_counted_extension`, `Step.plain_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- A thread at a matrix template performs its matrix event with any received bytes (the bytes
are constrained by `Consistent.matrix`, not by the thread rules). -/
theorem estep_matrix {h : Nat} {t1 : TState} {op : MatrixOp} {own : List (Option Byte)}
    {k : List (Option Byte) → TState} (hout : out K A L h t1 = .ev (.matrix op own k))
    (recv : List (Option Byte)) :
    EStep K A L h t1 ⟨t1.pc, .matrix op own recv⟩ (some (k recv)) :=
  ⟨_, hout, recv, rfl, rfl⟩

/-- **A whole warp performs a warp-level matrix instruction with given results**: the execution
with the instance appended is consistent, extends `X` and is larger. The lane `l` of the warp
contributes `parts l` and receives `recv l`, a result of the instance (`MatrixResultOk`). -/
theorem matrix_extension_of_results (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc : Nat} {op : MatrixOp} {parts recv : Nat → List (Option Byte)} (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 (matrixBatch L pc op parts recv h) o)
    (hres : MatrixResultOk A op parts recv)
    (hasm : ∀ a ∈ A, a.wf L mem0
      (X.appendLanes (warpThreads L g) (matrixBatch L pc op parts recv))) :
    Consistent L K A mem0 (X.appendLanes (warpThreads L g) (matrixBatch L pc op parts recv)) ∧
      X.le (X.appendLanes (warpThreads L g) (matrixBatch L pc op parts recv)) ∧
      X.size L < (X.appendLanes (warpThreads L g) (matrixBatch L pc op parts recv)).size L := by
  have hlive : ∀ h, SameWarp L g h → ∀ i pc', X.get (h, i) ≠ some ⟨pc', .exit⟩ := by
    intro h hs i pc'
    obtain ⟨t, -, -, hr, -⟩ := hrun h hs
    exact hr.no_exit
  exact matrixInstance_consistent hX hb hg hst hrel hrun
    (fun h hs => matrix_count_eq hX hs (hlive g ⟨⟨hg, hg, rfl⟩, rfl⟩) (hlive h hs)) hres hasm

/-- A whole warp performs a warp-level matrix instruction, when its batch preserves the
assumptions: a counted extension. The thread `h` contributes `own h`. -/
theorem matrix_counted_extension_with_assumptions (hX : Consistent L K A mem0 X)
    (hb : L.block % 32 = 0) {g pc : Nat} {op : MatrixOp} (hop : op.LaneClosed)
    (own : Nat → List (Option Byte)) (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ recv, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 ⟨pc, .matrix op (own h) recv⟩ o)
    (hasm : ∀ recv, MatrixResultOk A op (fun l => own (warpLane L g l)) recv →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g)
        (matrixBatch L pc op (fun l => own (warpLane L g l)) recv))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨recv, hres⟩ := exists_matrixResultOk A hop (fun l => own (warpLane L g l))
  refine ⟨_, matrix_extension_of_results hX hb (pc := pc) hg hst hrel (fun h hs => ?_) hres
    (hasm recv hres)⟩
  obtain ⟨t, t1, o, hr, hl, he⟩ := hrun h hs (recv (laneOf L h))
  refine ⟨t, t1, o, hr, hl, ?_⟩
  simp only [matrixBatch, warpLane_of_sameWarp hs]
  exact he

/-- **A whole warp performs a warp-level matrix instruction**: a counted extension. Every thread
`h` of `g`'s warp can perform, after local steps of its run, the matrix event of operation `op`
at `pc` with its contribution `own h`, whatever bytes it receives; `op` is a form whose results
read the 32 lanes only (`MatrixOp.LaneClosed`). The assumptions keep their constraints when
events that read no memory are appended (`hasm`). -/
theorem matrix_counted_extension (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {g pc : Nat} {op : MatrixOp} (hop : op.LaneClosed) (own : Nat → List (Option Byte))
    (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∀ recv, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 ⟨pc, .matrix op (own h) recv⟩ o)
    (hasm : ∀ ev, (∀ h, (ev h).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes (warpThreads L g) ev)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  matrix_counted_extension_with_assumptions hX hb hop own hg hst hrel hrun
    (fun _ _ => hasm _ fun _ => rfl)

end
end PTX.Step
