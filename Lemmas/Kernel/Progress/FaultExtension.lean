-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Progress.Released
public import Lemmas.Kernel.Progress.Warp

@[expose] public section

/-! # A fault of a released lane is a step

A proof tool, generic over the kernel: when no thread waits for a launch, a released lane whose run
can reach undefined behaviour performs it, an extension of the execution (`hubx` of
`Sched.warpColl_steps_rel` and `Sched.warpVote_steps`). -/

namespace PTX.Sched

open PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A released lane whose run reaches undefined behaviour steps.** -/
theorem fault_extension (hX : Consistent L K A mem0 X) (hlaunch : ∀ h, Step.Launched L X h)
    (hc : Descent.NextEnvQ L K A mem0 X) :
    ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  fun hh hrl hrun hl hout => Step.plain_counted_extension hX hh (.inr (hlaunch _)) hrl hrun hl
    (o := none) ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
    (hX.tmemPairResult.snoc_not_wr nofun)
    (hc.wf.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl))

end

end PTX.Sched
