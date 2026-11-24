-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions
public import Kernels.FlashMlaSparseDecodeH64.Flow.Sites
public import Lemmas.Flow.WaitLoopPcs
public import Lemmas.Flow.NotBulk

@[expose] public section

/-! # The frozen kernel's mbarrier polls -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingSpins

open PTX PTX.Flow

set_option maxRecDepth 100000 in
private theorem poll_sites : OpPcsFast kernel.code pollOp Flow.mbarWait.toList = true := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem wait_loops : kernel.waitLoopPcs Flow.mbarWait.toList = true := by
  decide +kernel

/-- Every mbarrier poll belongs to a canonical spin in the frozen kernel. -/
theorem poll {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {site parity : Nat}
    {m : Loc} {ok acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait m parity ok acquire scope⟩) :
    ∃ exit, kernel.CanonicalSpin site exit := by
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hf
  · by_cases hw : ∃ q b off par a s, ins.op = .mbarWait q b off par a s
    · obtain ⟨q, b, off, par, a, s, hop⟩ := hw
      exact Kernel.canonicalSpin_of_waitLoopPcs poll_sites wait_loops hc hop
    · push Not at hw
      exact absurd rfl (fires_notWait (eventTmpl_notWait hw) hf m parity ok acquire scope)

/-- A successful mbarrier poll resumes from a canonical spin in the frozen kernel. -/
theorem successful_poll {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) {i : EvId} {site parity : Nat}
    {m : Loc} {acquire : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨site, .wait m parity true acquire scope⟩) :
    ∃ exit, kernel.CanonicalSpin site exit :=
  poll hX he

/-- Both successful and unsuccessful poll events obey the same canonical spin audit. -/
theorem no_pollShapeUnsafe {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) : ¬ PollShapeUnsafe kernel X := by
  rintro ⟨i, site, m, parity, ok, acquire, scope, he, hn, _⟩
  exact hn (poll hX he)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingSpins
