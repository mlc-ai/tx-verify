-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemInstruction
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemResource
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTma
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.MmaElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.PvAProof
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Values.DqValid
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Rescale
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Guarded
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Order
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Dealloc

@[expose] public section

/-! # The facts the values of the Tensor Memory words are built on

`Safe.TmEnv`: the facts every proof about the values of the MMA lane's results and of the words a
lane loads takes (the mbarrier records do not fault, the allocation outlives the MMAs, the
dequantized tiles are valid, the operand elements decode, the rescale stores' words are numbers);
`Safe.tmEnv` proves them from the inputs and the validity of warpgroup 0's trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **The mbarrier records do not fault**, so the Tensor Core order is acyclic. -/
theorem Safe.guarded (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    SyncGuarded L kernel X :=
  guardedOfNoObjectFault hX fun l r hr => by
    cases hf : r.fault with
    | none => rfl
    | some f => exact absurd (.inl ⟨l, r, hr, by simp [hf]⟩) (Safe.noTma hp hIn hX hFw)

/-- **The facts of the values that need no validity of warpgroup 0's words**: the allocation
outlives the MMAs and the dequantized tiles are valid. -/
structure Safe.TmBase (L : Launch) (X : Execution) : Prop where
  hmd : Tmem.AccessCp.AsyncDoneDealloc L X
  hv : ∀ h k, NoUbBefore X h k → DqValid X h k

/-- **The base facts of the values hold.** -/
theorem Safe.tmBase (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) : Safe.TmBase L X :=
  ⟨TmRace.dealloc_async hp hX hFw (hIn.bar hp X hX hFw) (hIn.mbar hp X hX hFw)
    (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw),
   fun h k => dq_valid hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
    (hIn.bar0 hp X hX hFw) (hIn.raw hp X hX hFw) (noUbInner hX) (hIn.coord hp X hX hFw) h k⟩

/-- **The facts of the values**: the allocation outlives the MMAs, the dequantized tiles are valid,
the operand elements of every done MMA decode, the rescale stores' words are numbers. -/
structure Safe.TmEnv (L : Launch) (X : Execution) : Prop where
  hmd : Tmem.AccessCp.AsyncDoneDealloc L X
  hv : ∀ h k, NoUbBefore X h k → DqValid X h k
  hE : MmaElements X
  hS : RescaleStep L X

/-- **The facts of the values hold.** -/
theorem Safe.tmEnv (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    Safe.TmEnv L X := by
  have hb := Safe.tmBase hp hIn hX hFw
  exact ⟨hb.hmd, hb.hv,
    TmRace.mma_elements hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
      (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw) hb.hv
      (fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi) (tmem_rows hp hX hFw)
      (mmaOne hp hX hFw) (Safe.tmemOne hp hIn hX hFw) hb.hmd
      (TmRace.pv_a_elements hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
        (hIn.bar0 hp X hX hFw) (hIn.bar hp X hX hFw)
        (fun _ _ _ _ _ hi => Safe.issueShape hp hX hFw hi) (tmem_rows hp hX hFw)
        (hR.w0Trace X hX hFw hnu)),
    w0_rescale_step hp hX hFw (hR.w0Trace X hX hFw hnu)⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
