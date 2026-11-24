-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.NoTma
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoAligned
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoCtaBar
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoMixed
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoRace
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoSharedLifetime
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemInstruction
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemReads
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemSource
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoTmemWrites
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoUnalloc
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoWarpDivergence
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.TmaRest
public import Lemmas.Kernel.Goals
import Kernels.TmlFa4Fwd.Proof.Lib.PollShape
import Kernels.TmlFa4Fwd.Proof.Lib.StaticCode
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InputSafe
public import Kernels.TmlFa4Fwd.Proof.Top.Safe.NoUb
import Kernels.TmlFa4Fwd.Proof.Lib.StoreForm
import Kernels.TmlFa4Fwd.Proof.Epilogue.Assign
import Kernels.TmlFa4Fwd.Proof.Epilogue.NoUb
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Loader.Export.NoUb
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.MmaNoUb
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Access
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Safety by class (Proof top level)

`SafeGoal` for every consistent execution, split by the classes of Core's `Unsafe`. A class is
proved here or in its own file (`Top/Safe/<Class>.lean`).

Proved here, by the decoded program alone (`Lib/StaticCode.lean`, `Lib/PollShape.lean`,
`Lib/StoreForm.lean`, `Lib/GlobalWrites.lean`: static checks of the
code): no CLC request (`ClcUnsafe`), no reduction
without a rule (`TensorStoreUnsafe`: every tensor store is a plain tile write and every ordinary
copy a whole vector), no cluster barrier (`ClusterFault`), no warp matrix instruction
(`MatrixUnsafe`), every commit to the issuing CTA's group (`TcCommitUnsafe`), every poll in a
canonical spin (`PollShapeUnsafe`), the uniform Tensor Core CTA group, and that only the read-only
input assumption declares undefined behaviour (its condition, an input write, is proved as
`noInputWrite`). ERR-UNDEFINED-INSTRUCTION is proved per role (`noUb`: the softmax, correction, MMA,
output and loader warps). ERR-SETMAXNREG is proved on the role table (`Top/Register.lean`,
`noRegister`), ERR-MBAR-UNINITIALIZED by the CTA barrier's hand-off of the startup's initializations
(`Protocol/Mbar/Init.lean`, `noUninit`), ERR-TMEM-RESOURCE and ERR-TMEM-NOT-RELEASED by the MMA
warp's three operations on column 0 (`Protocol/Tmem/Word.lean`), ERR-BARRIER-MISMATCH by a
warp-uniform schedule of every role's barrier events (`Protocol/Bar/Match.lean`, `noBarMismatch`).

How each class is discharged on the role table (shape tables, `Ref`, ghost ledger, sources) is
listed in `DECISIONS.md`, "Safety by class". -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Kernels.TmlFa4Fwd

variable {p : Params} {l : Launch} {m : Mem0}

/-- **No mbarrier object error** (ERR-OBJECT-LIFETIME): initialization and publication are
proved (`noTma_of_rest`), the rest is the class `tmaRest`. -/
theorem noTma (hp : Pre p l m) {X : Execution} (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TmaUnsafe l m X :=
  noTma_of_rest hp hX (launchFollow hp hX) (Safe.tmaRest hp hX)

/-- ERR-REDUCTION-NO-RULE: every tensor store of the code is a plain tile write and every ordinary
copy writes a whole vector, so no reduction is performed. -/
theorem noTensorStore {X : Execution} (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TensorStoreUnsafe Assumptions.all X := by
  rintro (⟨i, o, red, _, _, ho, hRed, _⟩ | hCopy)
  · obtain ⟨⟨address, hi⟩, _⟩ := hX.store i o ho
    change o.spec.reduce = some red at hRed
    rw [(actualTensorStoreForm hX hi).2.2] at hRed
    cases hRed
  · exact TensorStore.not_copyReduceNoRule_of_none
      (fun i s hi red => by rw [(actualCopyShape hX hi).whole]; intro h; cases h) hCopy

/-- ERR-TENSOR-FILL-VALUE: every tensor load is one of the loader's Q and Bias copies through
its ABI map, which zero-fills `bf16` elements (`input_noTensorUnsafe`, a static check of the
decoded copies and the ABI maps). -/
theorem noTensor (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hFw : Follow p l X) : ¬ TensorUnsafe X :=
  input_noTensorUnsafe hp hX hFw

/-- ERR-TENSOR-LARGE-OOB: every tensor store is the output warp's through the launch's O map
(`Epilogue.store_issue`), whose backing the ABI supplies; no tensor prefetch is issued; every
tensor load is a Q or Bias copy through its ABI map, whose backing the ABI supplies
(`input_backing`). -/
theorem noTensorAllocation (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (hFw : Follow p l X) :
    ¬ TensorAllocationUnsafe l m X := by
  rintro ⟨i, ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, hBad⟩ | ⟨address, s, hi, _⟩⟩
  · exact input_backing hp hX hFw hi hBad
  · obtain ⟨-, b, -, st, bx, -, -, rfl⟩ := Proof.Epilogue.store_issue hp hX
      (store_warp hp hX hFw hi) hi
    exact hBad.2.2 ((hp.maps 10 p.oMapAddress ⟨3, p.oMap⟩ (by simp)).2.2.2.2.2 hBad.1)
  · exact noTensorPrefetch hX hi

/-- **No undefined-behaviour event**: the softmax and correction warps' lanes by `Safe.dataNoUb`,
warp 12's by `Mma.mma_noUb`, warp 13's by `Epilogue.noUb`, warps 14 and 15 by `Loader.ld_noUb`. -/
theorem noUb (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  by_cases hs : Prologue.warpIndex l g < 12
  · exact Safe.dataNoUb hp hX hs he f rfl
  by_cases hw : Prologue.warpIndex l g = 13
  · exact Proof.Epilogue.noUb hp hX (Frame.lt_of_get hX he) hw he f rfl
  by_cases hm : Prologue.warpIndex l g = 12
  · exact Proof.Mma.mma_noUb hp hX (launchFollow hp hX)
      (Frame.lt_of_get hX he) hm he f rfl
  · have hl : Prologue.warpIndex l g = 14 ∨ Prologue.warpIndex l g = 15 := by
      have hw16 := Prologue.warpIndex_lt hp g
      omega
    exact Proof.Loader.ld_noUb hp hX (Frame.lt_of_get hX he) hl he f rfl

/-- **Safety**: no consistent execution is unsafe, class by class. -/
theorem safe (hp : Pre p l m) : SafeGoal kernel Assumptions.all l m := by
  refine ⟨tcGroupUniform, fun X hX hBad => ?_⟩
  have hAssume := noAssumptionUb (noInputWrite hp hX (launchFollow hp hX))
  have hFw := launchFollow hp hX
  simp only [Unsafe, noUb hp hX, Safe.noUnalloc hp hX, Safe.noRace hp hX, Safe.noMixed hp hX,
    noBarMismatch hp hX hFw, noTma hp hX, Safe.noTmemSource hp hX, hAssume,
    Safe.noAligned hp hX (noUb hp hX), Safe.noSharedLifetime hp hX, noClcUnsafe hX,
    noTensor hp hX hFw, noTensorStore hX, noTensorAllocation hp hX hFw, noTmemResource hp hX hFw,
    noTmemRelease hp hX hFw, noPollShapeUnsafe hX, noTmemAccess hp hX hFw,
    noTcCommitUnsafe hp hX, Safe.noTmemWrites hp hX, Safe.noTmemInstruction hp hX,
    Safe.noTmemReads hp hX, noRegister hp hX hFw, Safe.noCtaBar hp hX, noClusterFault hX,
    Safe.noWarpDivergence hp hX, noMatrixUnsafe hX, noUninit hp hX hFw, or_self] at hBad

end PTX.Kernels.TmlFa4Fwd.Proof.Top
