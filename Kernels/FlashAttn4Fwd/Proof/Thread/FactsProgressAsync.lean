-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressAsync
public import Lemmas.Flow.WriteBytes

@[expose] public section

/-! # The threads' writes (`ProgressAsyncFacts.write_length`, `no_release`)

Every write fires from its site's instruction (`event_origin`): a store's element writes the
bytes of a value as wide as its footprint, and the allocation's address store four bytes
(`fires_write_length`); the kernel has no release store (`kernel_no_release`), so no write
releases (`fires_write_release`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The kernel has no release store. -/
theorem kernel_no_release : OpPcsFast kernel.code releaseOp [] = true := by
  decide +kernel

/-- Every write of the kernel is as wide as its footprint: it has no `movmatrix` row store. -/
theorem kernel_sizedWrite : OpPcsFast kernel.code (fun op => !sizedWrite op) [] = true := by
  decide +kernel

/-- **A thread's write carries as many bytes as its footprint.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ProgressAsyncFacts_write_length
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
      X.get e = some ⟨pc, .wr a bs⟩ → bs.length = a.size := by
  intro ⟨g, k⟩ pc a bs he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  refine fires_write_length hf rfl ?_
  cases hs : sizedWrite ins.op
  · exact absurd (OpPcsFast.mem kernel_sizedWrite hc (by simp [hs])) List.not_mem_nil
  · rfl

/-- **No thread's write releases.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ProgressAsyncFacts_no_release
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) (ht : Frame.Tracked (code L) X) :
    ∀ {e : EvId} {pc : Nat} {a : Acc} {bs : List Byte},
      X.get e = some ⟨pc, .wr a bs⟩ → a.release = false := by
  intro ⟨g, k⟩ pc a bs he
  obtain ⟨d, t, ins, o, -, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  refine fires_write_release hf rfl ?_
  by_contra hr
  simpa using OpPcsFast.mem kernel_no_release hc (by simpa using hr)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
