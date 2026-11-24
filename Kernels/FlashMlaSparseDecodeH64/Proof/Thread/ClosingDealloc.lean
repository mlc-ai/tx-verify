-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress

public section

/-! # The closing Tensor Memory deallocation instruction -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingDealloc

open PTX PTX.Flow

/-- A lane at the deallocation site issues the warp's request to free its 512 columns. -/
theorem event {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hd : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hsite : d.site = .exit) :
    ∃ t t1 tag, Run kernel Assumptions.all L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1 ∧
      EStep kernel Assumptions.all L g t1
        ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ (some (PTX.next t1)) := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hLocal, hAt, _, hCode, hOut⟩ := Frame.end_at hs hp.1 hRun hd
  change kernel.code[d.site.pc]? = some ins at hCode
  rw [hsite] at hCode
  obtain rfl := Option.some.inj (hCode.symm.trans Flow.code_tmemDealloc_0)
  rw [Wg0.event_exit hpre hAt hsite] at hOut
  exact ⟨t, t1, t1.pc, hRun, hLocal, _, hOut, rfl, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.ClosingDealloc
