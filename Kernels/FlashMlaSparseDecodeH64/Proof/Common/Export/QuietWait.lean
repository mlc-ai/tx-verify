-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Next
import Lemmas.Flow.NotBulk
import Lemmas.Flow.WaitTmpl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Poll
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfStep

@[expose] public section

/-! # A released lane at a wait that cannot fail steps

The quiet rows (`NextRow.Quiet`) see a lane at a wait whose failed poll is no next event
(`FailsAt`). Such a lane polls successfully once the polled object has a final state
(`Sched.wait_site_stepsUN`'s `hfin`); the blocked branch is empty, since a failed poll would be a
next event. `role_quietWait` is that step with the state taken privately; the role supplies the
two poll facts of its state (as for `role_wait`, `Common/Export.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **A next event at an acquiring wait is a poll.** -/
theorem next_wait {e : Event} (hn : Sched.NextEv L kernel Assumptions.all m X g e)
    (hub : ∀ f, e.kind ≠ .ub f) {ins : Instr} (hc : kernel.code[e.pc]? = some ins)
    (hk : Sched.waitOp ins.op = true) : ∃ l q ok sc, e.kind = .wait l q ok true sc := by
  obtain ⟨Y, hY, -, he⟩ := hn
  rcases get_source hY he with ⟨f, hf⟩ | ⟨t, ins', o, -, hc', hfire⟩
  · exact (hub f hf).elim
  rw [hc] at hc'
  cases hc'
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [Sched.waitOp, Bool.false_eq_true] at hk
  subst hk
  rcases eventTmpl_mbarWait_cases (A := Assumptions.all) (L := L) (g := g) (t := t) with
    ⟨f, hf⟩ | ⟨l, q, k, sc, -, htm⟩
  · rw [hf] at hfire
    obtain ⟨h, -⟩ := hfire
    exact (hub f (by rw [h])).elim
  · rw [htm] at hfire
    obtain ⟨ok, h, -⟩ := hfire
    exact ⟨l, q, ok, sc, by rw [h]⟩

/-- **A wait of any role that cannot fail steps** when the polled object has a final state. -/
private theorem role_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before)
    (hrole : ∀ σ, (table P L).J g σ → (thread P L g).inv σ →
      (table P L).Ev g σ ⟨pc, .wait l q ok true sc⟩ → pc = (thread P L g).pc σ →
      σ ≠ (thread P L g).init ∧
      (∀ ins, kernel.code[(thread P L g).pc σ]? = some ins → Sched.waitOp ins.op = true) ∧
        ∀ l' q' ok' sc', (table P L).Ev g σ ⟨(thread P L g).pc σ, .wait l' q' ok' true sc'⟩ →
          l' = l ∧ q' = q) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := next_state hp hFw hn (fun f h => by cases h)
  obtain ⟨hin, hop, hdet⟩ := hrole σ hJ hi hev hpc
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [h0, List.length_nil, Frame.stateAt_zero] at hσ
    exact hin (Option.some.inj (Option.some.inj hσ)).symm
  rw [timed_eq]
  refine Sched.wait_site_stepsUN (M := ⟨thread P L, time P L⟩) wfQuiet_all hmax hnu
    (fun _ _ => thread_sound hp) hpd hσ hne hrel hop
    (P := (table P L).Ev g _) (fun hat hi' hc hf _ =>
      (shapeOk hp (fun _ => True)).shape g trivial _ _ _ _ _ hJ hat hi' hc hf)
    (fun l' q' ok' sc' hP => ?_) (fun l' q' sc' _ hn' => ?_) (time_ge P L g σ)
  · obtain ⟨hl', -⟩ := hdet l' q' ok' sc' hP
    exact hl' ▸ hfin
  · rw [← hpc] at hn'
    exact (hf ⟨l', q', sc', hn'⟩).elim

/-- **Warpgroup 2, a wait that cannot fail**: a pending released lane whose next event is a poll
at a pc of warpgroup 2's code, where no failed poll is a next event, steps when the polled
object has a final state. -/
theorem dequant_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hpc0 : 2606 ≤ pc ∧ pc ≤ 3610)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) :
    Sched.Steps (timed P L) m X (.thread g) :=
  role_quietWait hp hFw hmax hnu hpd hrel hn hf hfin fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := dequant_state hp hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Dequant.wait_op (Dequant.evK_wait_site hE.2 rfl),
      fun l' q' ok' sc' hP => Dequant.evK_wait_det hE.2 hP.2 rfl rfl⟩

/-- **The index warp, a wait that cannot fail**, as `dequant_quietWait`. -/
theorem index_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hpc0 : 2332 ≤ pc ∧ pc < 2587)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) :
    Sched.Steps (timed P L) m X (.thread g) :=
  role_quietWait hp hFw hmax hnu hpd hrel hn hf hfin fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := index_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Index.wait_op (Index.evK_wait_site hE.2 rfl),
      fun l' q' ok' sc' hP => Index.evK_wait_det hE.2 hP.2 rfl rfl⟩

/-- **The TMA warp, a wait that cannot fail**, as `dequant_quietWait`. -/
theorem tma_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hpc0 : 2162 ≤ pc ∧ pc < 2332)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) :
    Sched.Steps (timed P L) m X (.thread g) :=
  role_quietWait hp hFw hmax hnu hpd hrel hn hf hfin fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, -, hE, hl, -⟩ := tma_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Tma.wait_op (Tma.evK_wait_site hl hE.2 rfl),
      fun l' q' ok' sc' hP => Tma.evK_wait_det hl hE.2 hP.2 rfl rfl⟩

/-- **The MMA warp, a wait that cannot fail**, as `dequant_quietWait`. -/
theorem mma_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hpc0 : 1850 ≤ pc ∧ pc < 2162)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) :
    Sched.Steps (timed P L) m X (.thread g) :=
  role_quietWait hp hFw hmax hnu hpd hrel hn hf hfin fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, hl, -⟩ := mma_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Mma.wait_op (Mma.evK_wait_site hl hE.2 rfl),
      fun l' q' ok' sc' hP => Mma.evK_wait_det hl hE.2 hP.2 rfl rfl⟩

/-- **Warpgroup 0, a wait that cannot fail**, as `dequant_quietWait`. -/
theorem wg0_quietWait (hp : Pre P L m) (hFw : Follow P L X)
    (hmax : Maximal L kernel Assumptions.all m X) (hnu : ¬ HasUb X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {pc q : Nat} {l : Loc} {ok : Bool} {sc : MbarScope}
    (hpc0 : 103 ≤ pc ∧ pc < 1842)
    (hn : Sched.NextEv L kernel Assumptions.all m X g ⟨pc, .wait l q ok true sc⟩)
    (hf : ¬ FailsAt L m X g pc)
    (hfin : ∃ before, MBarrier.stateBefore (X.objects l) (X.objects l).length = some before) :
    Sched.Steps (timed P L) m X (.thread g) :=
  role_quietWait hp hFw hmax hnu hpd hrel hn hf hfin fun σ hJ hi hev hpc => by
    obtain ⟨d, n, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc ⟨by simp only; omega,
      by simp only; omega⟩
    exact ⟨(fun h => by cases h), Wg0.wait_op (Wg0.evK_wait_site hE.2 rfl),
      fun l' q' ok' sc' hP => Wg0.evK_wait_det hE.2 hP.2 rfl rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
