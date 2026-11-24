-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Epilogue
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservationMachine
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
public import Kernels.TmlFa4Fwd.Proof.InputRead
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX Epilogue

noncomputable section

/-- No performed write touches a key-length word used by the request scheduler. -/
def UsedKProtected (p : Params) (X : Execution) : Prop :=
  ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
    ¬ a.Covers ((globalLoc (p.usedKBase + 4 * i)).at k)

/-- **The global write frame of every consistent execution.** Every read of a
`cu_seqlens_q` word returns its launch word (`cuQReadsFromLaunch`, by the read-only input
assumption), so the LSE stores and the O tensor stores have their decoded footprints, including
pending writes. -/
theorem outputIntentFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    OutputIntentFootprint p X :=
  outputIntentFootprint_of_sites hp hX
    (fun _ _ _ hWrite hGlobal => Thread.lseWriteShape hp hX hWrite hGlobal)
    (fun _ _ _ hIssue =>
      OutputWarp.issuedBox hp hX hIssue)

/-- The output footprint protects the two scheduling arrays by the audited launch separation. -/
theorem OutputFootprint.metadataProtected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (h : OutputFootprint p X) :
    DrainCuQProtected p X ∧ UsedKProtected p X := by
  constructor
  · intro i hi k hk w a bs hw
    refine h.input_unwritten hp (region := ⟨p.cuQBase, 4 * (p.batch + 1)⟩)
      (by simp [Params.inputRegions]) ?_ hw
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega
  · intro i hi k hk w a bs hw
    refine h.input_unwritten hp (region := ⟨p.usedKBase, 4 * p.batch⟩)
      (by simp [Params.inputRegions]) ?_ hw
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    omega

/-- No write of a consistent execution touches a `cu_seqlens_q` word. -/
theorem drainCuQProtected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) : DrainCuQProtected p X :=
  ((outputIntentFootprint hp hX).performed.metadataProtected hp).1

/-- No write of a consistent execution touches a used key length. -/
theorem usedKProtected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) : UsedKProtected p X :=
  ((outputIntentFootprint hp hX).performed.metadataProtected hp).2

/-- In a consistent execution the global write frame and the protection of CuQ hold
together. -/
theorem outputIntent_iff_cuQProtected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    OutputIntentFootprint p X ↔ DrainCuQProtected p X :=
  ⟨fun _ => drainCuQProtected hp hX, fun _ => outputIntentFootprint hp hX⟩

end
end PTX.Kernels.TmlFa4Fwd
