-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheFiniteOperands
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheCopyOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Mma (qkByteIndex)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

/-- Both bytes of an actual MMA cache element use the same word of the same copy in
the identified ready generation. The copy's write precedes each byte read. -/
theorem Completed.actualCacheOperandWord {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait mma : EvId} {use phase d : Nat} {accum : Bool} {mask : List Nat} {op : OperandSpec}
    (h : Completed l X wait (kvUseStage use) phase)
    (block : Fin 4) (step : Fin 8) (plane : CachePlane) {row k : Nat}
    (hr : row < 128) (hk : k < 16)
    (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X wait mma)
    (hBytes : ∀ b : Fin 2, op.byteLoc .b (qkByteIndex row k b.val) =
      (cacheOperand l mma.1 block step use plane).byteLoc .b (qkByteIndex row k b.val)) :
    ∃ (issue : EvId) (group : PublishedCopyGroup l X issue) (j : Nat) (spec : Spec)
        (bytes : List Byte) (word : Nat),
      X.AsyncArrive issue (Thread.Loader.readyObject l wait.1 (kvUseStage use)) true ∧
      generation l X issue (kvUseStage use) = phase ∧ (j, spec) ∈ group.copies ∧
      word < 8 ∧ (X.async.copies (issue.1, j)).writeBytes = some bytes ∧
      ∀ b : Fin 2,
        let loc := spec.dst.loc.at (2 * word + b.val)
        op.byteLoc .b (qkByteIndex row k b.val) = some loc ∧
        modelCausality l X loc (.async (issue.1, j) (.write .copy))
          (.async mma (.mmaRead true (qkByteIndex row k b.val))) := by
  obtain ⟨lane, pair, upper, word, hWord, hGeometry⟩ :=
    cacheOperandWordVector hp mma.1 block step use plane hr hk
  let base := kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper
  let low : Loc := ⟨.shared, mma.1 / l.block, base + 2 * word⟩
  have hLow : op.byteLoc .b (qkByteIndex row k 0) = some low := by
    apply (hBytes 0).trans
    simpa [low,base] using hGeometry 0
  obtain ⟨issue, group, j, spec, bytes, hPub, _, hPhase, _, _, hMember, hDst, _, hWrite, _⟩ :=
    h.actualOperandCoveringCopyWithPublication hp hX lane pair upper (off := 2 * word) (by omega)
      hMma hEarlier (isB := true) hLow (by rw [hEarlier.1])
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hRecorded := ((Execution.memWrites_write_copy_of_whole hCopy hShape.whole).mp hWrite).2
  refine ⟨issue,group,j,spec,bytes,word,hPub,hPhase,hMember,hWord,hRecorded,?_⟩
  intro b
  have hNext : spec.dst.loc.at (2 * word + b.val) =
      ⟨.shared, mma.1 / l.block, base + (2 * word + b.val)⟩ := by
    have hb : (spec.dst.loc.at (2 * word)).at b.val = spec.dst.loc.at (2 * word + b.val) := by
      cases spec.dst.loc
      simp [Loc.at,Nat.add_assoc]
    rw [← hb, hDst]
    simp [low, Loc.at, Nat.add_assoc]
  have hLoc : op.byteLoc .b (qkByteIndex row k b.val) =
      some (spec.dst.loc.at (2 * word + b.val)) := by
    rw [hBytes b, hNext]
    exact hGeometry b
  have hCover : spec.dst.Covers (spec.dst.loc.at (2 * word + b.val)) := by
    have hb := b.isLt
    simp only [Acc.Covers, Loc.InRange, Loc.at, hShape.widthEq, true_and]
    exact ⟨by omega,by omega⟩
  exact ⟨hLoc, (h.publishedCacheCopyBeforeOperand hp hX hPub hPhase group hMember hCover
    hMma hEarlier hLoc).2⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
