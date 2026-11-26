-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemAccess
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.ASource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.AccSource
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoTmemInstruction
public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.Completed
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.SourceDone
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.CpValue
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.LdExists

@[expose] public section

/-! # ERR-TMEM-READ-SOURCE: Tensor Memory reads have a source

The safety class of Core's `Unsafe` this file owns (`TcMma.SourceUnsafe`). It has no open part of
its own: the word a source left exists once the completed MMAs have their results
(`TmRace.ld_wrote`, `TmRace.acc_wrote`), which `Safe.completed` proves (`ERR-TC-MMA`); the A reads'
words are `cp_defined`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- **ERR-TMEM-READ-SOURCE**: Tensor Memory reads have a source. -/
theorem Safe.noTmemSource (hp : Pre P L mem0) (hIn : Top.Inputs P L mem0)
    (hR : Safe.W0TraceValid P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) (hnu : ¬ HasUb X) :
    ¬ TcMma.SourceUnsafe L Assumptions.all X := by
  unfold TcMma.SourceUnsafe
  rw [not_not, TcMma.sourceSafe_iff]
  have hT := tmem_rows hp hX hFw
  have hG : SyncGuarded L kernel X := Safe.guarded hp hIn hX hFw
  have hCV := Safe.completed hp hIn hR hX hFw hnu
  have hCp : TmRace.CpDefined X := cp_defined hp hX hFw (hIn.mbar hp X hX hFw)
    (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
  have hO : MmaOne L X := mmaOne hp hX hFw
  have hmd : Tmem.AccessCp.AsyncDoneDealloc L X :=
    TmRace.dealloc_async hp hX hFw (hIn.bar hp X hX hFw) (hIn.mbar hp X hX hFw)
    (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw)
  refine ⟨fun e j cell hc => ?_, fun i cell hd hc => ?_, fun i cell hd ha => ?_⟩
  · obtain ⟨a, vals, sh, hld, hj, hcell⟩ := hc
    obtain ⟨source, hs⟩ := TmRace.ld_source hp hX hFw (hIn.mbar hp X hX hFw)
      (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw)
      (hIn.bar hp X hX hFw) (Safe.pvStore hp hIn hX hFw) hG (Safe.tmemOne hp hIn hX hFw)
      ⟨a, vals, sh, hld, hj, hcell⟩
      (TmRace.ld_write hp hX hFw (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw)
        (hIn.bar0 hp X hX hFw) (hIn.dequant hp X hX hFw) hld hj hcell)
    obtain ⟨value, hv⟩ := TmRace.ld_wrote hX hCV hCp hld hs
    exact ⟨source, value, hs, hv⟩
  · obtain ⟨source, hs⟩ := TmRace.acc_source hp hX hFw hT hO
      (Safe.pvStore hp hIn hX hFw) hG (Safe.tmemOne hp hIn hX hFw) hmd hc
    obtain ⟨value, hv⟩ := TmRace.acc_wrote hp hX hT hO hG hCV hCp hd hc hs
    exact ⟨source, value, hs, hv⟩
  · exact TmRace.a_source hp hX hFw hT hO
      (hIn.mbar hp X hX hFw) (hIn.initRows hp X hX hFw) (hIn.bar0 hp X hX hFw)
      (Safe.tmemOne hp hIn hX hFw) hmd
      hCp ha

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
