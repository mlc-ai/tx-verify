-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Lemmas.Order.WaitOrderEnables
import Lemmas.Step.CtaBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier Loader Prologue

noncomputable section

/-- The first MMA release's actual notification targets empty slot zero. -/
theorem initialEmptyReleaseAddress {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec} {rank : Fin 16} {loc : Loc}
    (he : X.get (g, index) = some ⟨2274, .tc (.commit spec)⟩)
    (hTarget : TcCommit.target spec rank = some loc) :
    loc = initObject l (g / l.block) (emptySlot 0) := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨t, _, ht, hb, tm, hout, hf⟩ := mmaSharedBaseBeforeEvent hp hX he
    (show 2145 ≤ 2274 by decide) (show 2274 < 2768 by decide)
  change t.pc = 2274 at ht
  rcases out_ev hout with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · have hKind := congrArg Event.kind hf.1
    cases hKind
  rw [ht, Flow.code_2274] at hc
  obtain rfl := Option.some.inj hc.symm
  have hBase : t.regs 2535 = some (b32 (l.sharedBase + 0)) := hb
  have hLoc := commitExactAddress hp hg hBase (by unfold initializedMbarOffset; decide)
    hf rfl hTarget
  simpa [emptySlot_address] using hLoc

/-- The successful initial K-ready acquire is a dependency of the actual empty-slot
notification. Both operands resolve to their initialized slot-zero objects. -/
theorem initialReadyBeforeEmptyNotification {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec} {rank : Fin 16} {loc : Loc} {r : Record Ref}
    (he : X.get (g, index) = some ⟨2274, .tc (.commit spec)⟩)
    (hTarget : TcCommit.target spec rank = some loc)
    (hr : r ∈ X.objects loc) (hId : r.id = .async (g, index) (.tcNotify rank)) :
    loc = initObject l (g / l.block) (emptySlot 0) ∧
      ∃ j < index, X.get (g, j) =
        some ⟨2145, .wait (initObject l (g / l.block) (readySlot 0)) 0 true true .cta⟩ ∧
        Relation.TransGen (DepStep l kernel X) (.thread (g, j), true) (r.id, false) := by
  obtain ⟨j, hj, hGet, hResume⟩ := initialReadyBeforeCommit hp hX he
  have hPresent := object_record_present hX.tma hr
  rw [hId] at hPresent
  have hIssue : DepStep l kernel X (.thread (g, index), false)
      (.async (g, index) (.tcNotify rank), false) :=
    DepStep.issue (show X.RefPresent (.thread (g, index)) from ⟨_, he⟩) hPresent
      (by intro t ht; cases ht) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h)
  refine ⟨initialEmptyReleaseAddress hp hX he hTarget, j, hj, hGet, ?_⟩
  rw [hId]
  exact (Relation.TransGen.single (DepStep.of_resumes l hResume)).tail hIssue

end
end PTX.Kernels.TmlFa4Fwd.Mma
