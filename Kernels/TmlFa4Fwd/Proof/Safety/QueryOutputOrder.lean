-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Machine
public import Kernels.TmlFa4Fwd.Proof.Safety.QueryOutputAlias
public import Kernels.TmlFa4Fwd.Proof.Protocol.QueryOutputHandoff
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryIssue
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInputCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Epilogue Correction

/-- The first Q TMA subbox and a correction element reusing the stage-zero output subbox.
The issue, map, barrier, role and destination footprint identify the handoff. -/
structure QueryOutputReuse (p : Params) (l : Launch) (X : Execution)
    (input writer : EvId) (s : TensorCopy.Spec) (x y : Nat) : Prop where
  issued : Thread.Loader.FirstQueryIssue X input p.qMapAddress s
  map : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩
  base : s.sharedBase = sharedSlot l writer.1 0 0
  barrier : s.mbar = Thread.Output.queryObject l (writer.1 / l.block) 0
  sameCta : input.1 / l.block = writer.1 / l.block
  correction : Thread.roleOf l writer.1 = .correction
  column : x < 32
  row : y < 128
  written : ∃ data, X.Writes writer (outputElementAccess l writer.1 0 0 x y) data

/-- A mixed-size conflict unordered by the original direct byte relation. -/
def LegacyQueryOutputConflict (l : Launch) (X : Execution) : Prop :=
  ∃ src dst a b loc, Conflict X src dst a b ∧ ¬ a.SameFootprint b ∧ a.Covers loc ∧
    b.Covers loc ∧ ¬ modelCausality l X loc src dst ∧ ¬ modelCausality l X loc dst src

/-- The first Q subbox and the correction write that reuses it are unordered at their common
byte by the original direct byte relation. Both events must be witnessed in the same execution. -/
theorem queryOutputLegacyConflict {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input writer : EvId} {address x y : Nat} {data : List Byte} {s : TensorCopy.Spec}
    (hInput : Thread.Loader.FirstQueryIssue X input address s)
    (hMap : (⟨s.outer, s.descriptor⟩ : (n : Nat) × TensorDescriptor.Descriptor n) = ⟨2, p.qMap⟩)
    (hBase : s.sharedBase = sharedSlot l writer.1 0 0)
    (hObject : s.mbar = Thread.Output.queryObject l (writer.1 / l.block) 0)
    (hWrite : X.Writes writer (outputElementAccess l writer.1 0 0 x y) data)
    (hRole : Prologue.warpIndex l writer.1 ≠ 12) (hx : x < 32) (hy : y < 128) :
    LegacyQueryOutputConflict l X := by
  obtain ⟨qx, qy, k, a, loc, hConflict, hWidths, hSrc, hDst, _⟩ :=
    queryBoxConflictsWithOutputElement hp hx hy hInput.issue hMap hBase hWrite
  exact ⟨_, _, _, _, loc, hConflict, hWidths, hSrc, hDst,
    Thread.Output.queryLoadNotBeforeNonMma hp hX hInput.issue hObject hRole,
    Thread.Loader.noThreadBeforeFirstQuery hp hX hInput⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFrame : OutputFootprint p X) {cta : Nat} (hCta : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads)
include hp hX hDone hFrame hCta hWork

private theorem firstQueryOutputWitness :
    ∃ input writer spec wait, QueryOutputReuse p l X input writer spec 0 0 ∧
      Thread.Correction.FirstOutputAcquire l X wait ∧ po X wait writer := by
  let g := cta * l.block + 256
  have hg : g < l.threads := by
    change cta * l.block + 256 < l.grid * l.block
    rw [hp.block]
    omega
  have hOwner : g / l.block = cta := by
    dsimp [g]
    rw [hp.block]
    omega
  have hWarp : Prologue.warpIndex l g = 8 := by
    dsimp [g, Prologue.warpIndex]
    rw [hp.block]
    omega
  obtain ⟨input, spec, _, hIssue, hInputCta, hBase, hObject, hMap, _, _, _⟩ :=
    Thread.Loader.firstQueryIssue hp hX hDone hCta hWork hFrame
  obtain ⟨wait, pos, bytes, hAcquire, hLater, hWrite⟩ :=
    Thread.Correction.firstStagingWriteAfterAcquire hp hX hDone hg
    (by omega) (by omega) (by rwa [hOwner])
  have hRow : rowOf l g = 0 := by
    dsimp [g, rowOf]
    rw [hp.block]
    omega
  rw [hRow] at hWrite
  refine ⟨input, (g, pos), spec, (g, wait), ⟨hIssue, hMap, ?_, ?_, ?_, ?_, by decide,
    by decide, bytes, hWrite⟩, hAcquire, hLater⟩
  · simpa [sharedSlot, hOwner] using hBase
  · simpa [Thread.Output.queryObject, hOwner] using hObject
  · exact hInputCta.trans hOwner.symm
  · simp [Thread.roleOf, hWarp]

/-- A complete active CTA's first Q input and correction output share the first staging byte. -/
theorem queryOutputReuseOfComplete :
    ∃ input writer spec x y, QueryOutputReuse p l X input writer spec x y := by
  obtain ⟨input, writer, spec, _, h, _, _⟩ := firstQueryOutputWitness hp hX hDone hFrame hCta hWork
  exact ⟨input, writer, spec, 0, 0, h⟩

omit hp hX hDone hFrame hCta hWork in
private theorem correctionNotMma {l : Launch} {g : Nat}
    (h : Thread.roleOf l g = .correction) : Prologue.warpIndex l g ≠ 12 := by
  intro hw
  simp [Thread.roleOf, hw] at h

/-- The completed Q/O handoff has a mixed-size conflict under direct byte order. -/
theorem queryOutputLegacyConflictOfComplete : LegacyQueryOutputConflict l X := by
  obtain ⟨input, writer, spec, x, y, h⟩ := queryOutputReuseOfComplete hp hX hDone hFrame hCta hWork
  obtain ⟨_, hWrite⟩ := h.written
  exact queryOutputLegacyConflict hp hX h.issued h.map h.base h.barrier hWrite
    (correctionNotMma h.correction) h.column h.row

/-- Every Q byte overwritten by the actual first correction element is ordered through the MMA
that read it. -/
theorem queryOutputByteOrderOfComplete {offset : Nat} (hOffset : offset < 4) :
    ∃ input writer spec x y k loc, QueryOutputReuse p l X input writer spec 0 0 ∧
      loc = (outputElementAccess l writer.1 0 0 0 0).loc.at offset ∧
      TensorCopy.writeLoc spec x y k = some loc ∧
      (outputElementAccess l writer.1 0 0 0 0).Covers loc ∧
      X.AsyncPresent input (.write (.load x y k)) ∧
      ByteCausality l X loc (.async input (.write (.load x y k))) (.thread writer) ∧
      ¬ modelCausality l X loc (.async input (.write (.load x y k))) (.thread writer) := by
  obtain ⟨input, writer, spec, wait, hReuse, hWait, hBefore⟩ :=
    firstQueryOutputWitness hp hX hDone hFrame hCta hWork
  obtain ⟨_, plane, hBox⟩ :=
    Thread.Loader.querySubboxOfBarrier hp hX 0 hReuse.issued.issue hReuse.barrier
  have hBoxBase := congrArg Loc.addr (hBox.2.2.1.symm.trans hReuse.base)
  have hPlane : plane = 0 := by
    apply Fin.ext
    simp only [sharedSlot, Mma.qStart, Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hBoxBase ⊢
    omega
  subst plane
  let base : Loc := ⟨.shared, writer.1 / l.block, l.sharedBase + 3072⟩
  let loc := base.at offset
  have hBase : spec.sharedBase = base := by simpa [base, sharedSlot] using hReuse.base
  obtain ⟨x, y, k, hLoc⟩ := queryBoxWriteLoc hReuse.map (show offset < 16384 by omega)
  have hAddr : TensorCopy.writeLoc spec x y k = some loc := by simpa only [loc, hBase] using hLoc
  let dst := outputElementAccess l writer.1 0 0 0 0
  have hDst : dst.loc = base := by simp [dst, base, outputElementAccess, outputChunkLoc,
    sharedSlot, Loc.at]
  have hCover : dst.Covers loc := by
    change dst.Covers (base.at offset)
    rw [← hDst]
    exact Acc.covers_at (show offset < dst.size from hOffset)
  obtain ⟨bytes, hWrite⟩ := hReuse.written
  obtain ⟨hPresent, hOrder⟩ := Protocol.firstQueryByteBeforeOutput hp hX hDone hOffset
    hReuse.sameCta hBox hAddr hWait hBefore hWrite hCover
  exact ⟨input, writer, spec, x, y, k, loc, hReuse,
    congrArg (fun l => l.at offset) hDst.symm, hAddr, hCover, hPresent, hOrder,
    Thread.Output.queryLoadNotBeforeNonMma hp hX hReuse.issued.issue
      hReuse.barrier (correctionNotMma hReuse.correction)⟩

end PTX.Kernels.TmlFa4Fwd.Safety
