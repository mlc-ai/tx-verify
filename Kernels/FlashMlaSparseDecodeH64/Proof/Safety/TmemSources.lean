-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MmaAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.QueryCellValues
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemFinalLoadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemScoreLoadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.TmemRescaleLoadSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TcCollectiveOperands

@[expose] public section

/-! # Every tensor-memory read that requires a value has an actual source -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow

/-- Load registers, completed accumulators and Tensor Memory A reads have live, valued sources. -/
theorem no_tmem_source_unsafe {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) :
    ¬ TcMma.SourceUnsafe L Assumptions.all X := by
  intro hunsafe
  apply hunsafe
  apply TcMma.sourceSafe_iff.mpr
  refine ⟨?_, fun _ _ hd he => mma_acc_source hpre hX hs ht hd he,
    fun _ _ _ he => mma_a_source hpre hX hs ht he⟩
  rintro ⟨g, i⟩ n _ ⟨a, words, sh, hload, hn, rfl⟩
  have hg := Frame.lt_of_get hX hload.choose_spec
  obtain ⟨d, hd, rfl, hsite⟩ := TcCollectiveSites.load_fields hpre hX (hs g hg).machine ht hload
  rcases hsite with ⟨arm, part, hsite, rfl, hlen⟩ | ⟨tile, hsite, rfl, hlen⟩
  · exact score_load_source hpre hX hs ht ⟨n, hlen ▸ hn⟩ hd hsite hload hlen
  · let reg : Fin 64 := ⟨n, hlen ▸ hn⟩
    rcases hsite with h | h
    · exact rescale_load_source hpre hX hs ht reg hd h hload hlen
    · exact final_load_source hpre hX hs ht reg hd h hload hlen

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
