-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.NextEnv
public import Kernels.InklingRelDecode.Proof.Common.PendStep
import Kernels.InklingRelDecode.Proof.Common.Export.PollSite
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.Publication
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.InitFirst
import Kernels.InklingRelDecode.Proof.Top.Inputs
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Lemmas.Flow.WaitTmpl
import Lemmas.Protocol.UnitReachBlocker
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A released lane at a poll steps, or its next event is a failed poll

The polled object is one of the twelve its CTA initializes, which the lane has passed the
publication barriers for; its history has a final state. A poll that finds its parity ready
steps (`Step.poll_counted_extension`); a poll that does not is the lane's next event, the failed
poll (`Step.failed_poll_maximal`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Descent MBarrier

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private def waitOk (pc : Nat) (ins : Instr) : Bool :=
  opKind ins.op != .wait ||
    (Sched.waitOp ins.op && [1257, 2239, 2374, 2462, 2510, 2565].contains pc)

private theorem waitOk_all : kernel.code.zipIdx.all (fun x => waitOk x.2 x.1) = true := by
  decide +kernel

private theorem wait_at {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins)
    (hk : opKind ins.op = .wait) :
    Sched.waitOp ins.op = true ∧ Export.pollSite pc := by
  have := List.all_eq_true.mp waitOk_all (ins, pc) (List.mem_zipIdx_iff_getElem?.mpr h)
  simp only [waitOk, hk, bne_self_eq_false, Bool.false_or, Bool.and_eq_true,
    List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at this
  refine ⟨this.1, ?_⟩
  obtain ⟨x, hx, rfl⟩ := this.2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  exact hx

/-- **The final state of an initialized object's history.** -/
theorem final_exists (hX : Consistent L kernel Assumptions.all m X) (rows : MbarRows Q L X)
    (init : Protocol.Mbar.InitRows L X) {l : Loc} (hne : X.objects l ≠ []) :
    ∃ st, stateBefore (X.objects l) (X.objects l).length = some st :=
  MbarRing.Unit.final_of_init hX (Protocol.Mbar.initFirst hX rows init l)
    (AsyncCopy.objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => Lib.no_inval hX he) l) hne

/-- **A released pending lane at a poll steps, or its next event is the failed poll.** -/
theorem Prog.poll_pend (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hm : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) (hpd : Frame.Pending L X g)
    (hrel : Step.Released L X g) {t1 : TState} {ins : Instr} (h : PendAt L X g t1 ins)
    (hk : opKind ins.op = .wait) :
    Sched.Steps (schedule Q L) m X (.thread g) ∨ ∃ pc, FailsAt L m X g pc := by
  have hX := hm.1
  have hc := Prog.nextEnv hp hs hm hf
  obtain ⟨t, hrun, hl⟩ := h.run
  obtain ⟨hw, site⟩ := wait_at h.code hk
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [Sched.waitOp, Bool.false_eq_true] at hw
  rename_i pr b off par acq sc0
  subst hw
  have hlaunch : Step.Launched L X g := fun ⟨_, _, _, ⟨_, hi⟩⟩ => (Lib.no_clc hX hi).elim
  have hout := h.out
  have hub := hc.noUb
  have nu : Frame.NoUbBefore X g (X.tr g).length := fun j _ e he f hf' =>
    hub ⟨(g, j), e.pc, f, by obtain ⟨pc, kd⟩ := e; simp only at hf'; subst hf'; exact he⟩
  rcases eventTmpl_mbarWait_cases (A := Assumptions.all) (L := L) (g := g) (t := t1) (p := pr)
    (b := b) (off := off) (par := par) (acq := true) (sc := sc0) with
    ⟨f, hf'⟩ | ⟨l, q, k, sc, hq2, htm⟩
  · rw [hf'] at hout
    exact .inl (.inl (Step.plain_counted_extension hX hpd.1 (.inr hlaunch) hrel hrun hl (o := none)
      ⟨_, hout, rfl, rfl⟩ trivial rfl nofun nofun nofun rfl
      (hX.tmemPairResult.snoc_not_wr nofun) (hc.snoc_wf rfl)))
  have hfire : ∀ ok, Fires t1.pc
      (eventTmpl Assumptions.all L g t1 (.mbarWait pr b off par true sc0))
      ⟨t1.pc, .wait l q ok true sc⟩ (some (k ok)) := fun ok => by
    rw [htm]; exact ⟨ok, rfl, rfl⟩
  have occ : Occurs L X g (X.tr g).length ⟨t1.pc, .wait l q true true sc⟩ :=
    .inr ⟨hpd.1, rfl, nu, t, t1, _, _, hrun, hl, hout, hfire true⟩
  obtain ⟨⟨j, hj⟩, after⟩ := Export.poll_site hp hX hf occ (by simpa using (wait_at h.code hk).2)
  have live := Protocol.Mbar.occ_published hp hX hf occ (fun _ => nofun) after j
  have rows := mbarRows_of hp hX hf
  obtain ⟨before, hstate⟩ := final_exists hX rows (initRows_of hp hX hf) (l := l)
    (by rw [hj]; exact live)
  have hne : X.tr g ≠ [] := by
    intro hnil
    have := Export.after_initialization_occ hp hX hf occ (fun _ => nofun) after
    rw [hnil] at this
    simp at this
  have hasm : ∀ (ok : Bool) {sc' : MbarScope}, ∀ a ∈ Assumptions.all,
      ∀ {rec : MBarrier.Record AsyncCopy.Ref},
      rec.id = .thread (g, (X.tr g).length) →
      a.wf L m (X.snocObject g ⟨t1.pc, .wait l q ok true sc'⟩ (fun _ => none) l rec) :=
    fun _ _ a ha _ _ => hc.wf.quiet hX (Execution.le_trans le_snoc
      (Execution.le_appendObject ..)) rfl ((Execution.quietExt_snoc (r := fun _ => none) rfl).trans
        (Execution.quietExt_of_tr rfl)) a ha
  have he : ∀ ok, EStep kernel Assumptions.all L g t1 ⟨t1.pc, .wait l q ok true sc⟩ (some (k ok)) :=
    fun ok => ⟨_, hout, hfire ok⟩
  by_cases hready : before.phase % 2 ≠ q % 2
  · exact .inl (.inl (Step.poll_counted_extension hX hpd.1 hne hrel (hasm true) hrun hl (he true)
      hstate hready))
  · push Not at hready
    have hYmax := Step.failed_poll_maximal hm hpd.1 hne hrel (hasm false) hrun hl (he false) hstate
    refine .inr ⟨t1.pc, l, q, sc, ⟨_, hYmax.1, ?_, ?_⟩⟩
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc]
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc,
        Execution.get]

end PTX.Kernels.InklingRelDecode.Proof.Top
