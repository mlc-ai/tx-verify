-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.Descent
public import Lemmas.Step.Issue

@[expose] public section

/-! # The next event of a released pending thread

A pending thread of a safe execution has a run that ends in a state (`Frame.run_some`), and
its machine is at a state of the kind of its site: by local steps it reaches a concrete state
whose template is undefined behaviour or of that kind (`ThreadFacts.fire`, `next_fire`). A
template of undefined behaviour is performed (`Descent.ub_steps`). The classes of the other kinds
take the template apart (`NextPlain.lean`, …). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Progress

open PTX

noncomputable section

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread at a state of a kind other than a warp collective has made an event: its machine
starts at the prologue's shuffle. -/
theorem ne_nil_of_kind {g : Nat} {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) (hk : nextKind d ≠ .warp) :
    X.tr g ≠ [] := by
  intro h0
  have h0' : Frame.stateAt (code L) X g (X.tr g).length = some (some (.inl ⟨.shfl, 0⟩)) := by
    rw [h0]
    rfl
  rw [h0'] at hσ
  cases hσ
  exact hk rfl

/-- **The next event of a pending thread of a safe execution**: its run ends in a state, from
which local steps reach a concrete state of its machine state whose template is undefined
behaviour or of its site's kind. -/
theorem next_fire (ht : ThreadFacts L X) (hX : Consistent L kernel Prod mem0 X) (hub : ¬ HasUb X)
    {g : Nat} (hp : Frame.Pending L X g) {d : ThreadD}
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d)) :
    ∃ t t1 m, Run kernel Prod L g {} (X.tr g) (some t) ∧
      Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧ (code L g).AtD d t1 ∧
      out kernel Prod L g t1 = .ev m ∧ ((∃ f, m = .ub f) ∨ KindTmpl L g (nextKind d) m) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, m, hl, hat, hout, hm⟩ := ht.fire hp.1 hσ hrun
  exact ⟨t, t1, m, hrun, hl, hat, hout, hm⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof.Progress
