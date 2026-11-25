-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Free
public import Lemmas.Kernel.Progress.WaitSite

@[expose] public section

/-!
# Progress at an mbarrier wait, under `WfStepE`

Kernel-independent restatements of the library's wait templates (candidates for
`Lemmas/Kernel/NextInOrder.lean`, `Lemmas/Kernel/Progress/Rank.lean` and
`Lemmas/Kernel/Progress/WaitSite.lean`), with `WfStepE` (`Wf.lean`) in the place of
`Assumption.WfStep` and the originals' proofs. A poll event reads no memory and is no election,
so the assumptions' constraints survive the append of a successful or a failed poll
(`WfStepE.snocObject`).

* `mbar_wait_stepsE` (`Descent.mbar_wait_steps_inOrder`): a released pending thread whose next
  event polls a barrier performs the successful poll when the barrier is ready; otherwise the
  failed poll is appended, the execution stays maximal, and the caller names an open obligation
  of smaller rank there.
* `mbar_at_stepsE` (`Sched.mbar_at_steps`): the same with the ranks of a time table.
* `wait_site_stepsE` (`Sched.wait_site_steps`): the same from the shape of the events the
  thread's machine state fires and a blocker in the execution itself.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Flow PTX.Descent PTX.Sched MBarrier AsyncCopy

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

section
variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A pending thread at an mbarrier wait steps.** -/
theorem mbar_wait_stepsE (hA : WfStepE sel L K mem0 A) (hub : ¬ HasUb X)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) (hne : X.tr g ≠ []) {m : Loc} {pcw par : Nat}
    {Q : MbarScope → Prop}
    (hpoll : ∀ t, Run K A L g {} (X.tr g) (some t) → ∀ ok : Bool, ∃ t1 u sc,
      Relation.ReflTransGen (Tau K A L g) t t1 ∧
      EStep K A L g t1 ⟨pcw, .wait m par ok true sc⟩ (some u) ∧ (ok = false → Q sc))
    {before : State} (hstate : stateBefore (X.objects m) (X.objects m).length = some before)
    (hblk : ∀ sc, Q sc → before.phase % 2 = par % 2 →
      Maximal L K A mem0 (Step.failedPoll X g pcw par m true sc before) →
      ∃ o', Obl (Step.failedPoll X g pcw par m true sc before) o' ∧
        rank (Step.failedPoll X g pcw par m true sc before) o' < rank X o) :
    Steps L K A mem0 Obl rank X o := by
  have hX := hmax.1
  have hg := hp.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  have hasm : ∀ (ok : Bool) {sc' : MbarScope}, ∀ a ∈ A, ∀ {rec : Record Ref},
      rec.id = .thread (g, (X.tr g).length) →
      a.wf L mem0 (X.snocObject g ⟨pcw, .wait m par ok true sc'⟩ (fun _ => none) m rec) :=
    fun _ _ a ha _ _ => hA.snocObject hX rfl rfl a ha
  by_cases hready : before.phase % 2 ≠ par % 2
  · obtain ⟨t1, u, sc, hl, he, -⟩ := hpoll t hrun true
    exact .inl (Step.poll_counted_extension hX hg hne hrel (hasm true) hrun hl he
      hstate hready)
  · push Not at hready
    obtain ⟨t1, u, sc, hl, he, hq⟩ := hpoll t hrun false
    have hYmax := Step.failed_poll_maximal hmax hg hne hrel (hasm false) hrun hl he hstate
    obtain ⟨o', hobl, hlt⟩ := hblk sc (hq rfl) hready hYmax
    exact .inr ⟨_, o', hYmax, hobl, hlt⟩

end

variable {M : Timed K A L}

/-- **A released thread at an mbarrier wait steps**, when its blockers are earlier than its
time. -/
theorem mbar_at_stepsE (hA : WfStepE sel L K mem0 A) (hub : ¬ HasUb X)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g)
    (hrel : Step.Released L X g) (hne : X.tr g ≠ []) {b : Nat} (h : MbarAt M mem0 X g b)
    (hb : b < threadTime M X g) (h2 : 2 ≤ threadTime M X g) : Steps M mem0 X (.thread g) := by
  obtain ⟨m, pcw, par, Q, before, hpoll, hstate, hB⟩ := h
  refine mbar_wait_stepsE hA hub hmax hp hrel hne hpoll hstate ?_
  intro sc hq hpar hY
  rw [rank_released hrel]
  exact (hB sc hq hpar hY).rank_lt hb h2

/-- **Progress at a wait, from the shapes of the state and the facts of a poll event.** A
released pending thread whose next instruction is an acquiring `mbarrier.try_wait` steps, given
the shape of the events its state fires (`P`), a state of every barrier such a shape polls, and
a blocker whenever that state has the poll's parity. -/
theorem wait_site_stepsE (hA : WfStepE sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → Sched.waitOp ins.op = true)
    {P : Event → Prop}
    (hS : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (M.code g).AtD d t →
      (M.code g).inv d → K.code[(M.code g).pc d]? = some ins →
      Fires ((M.code g).pc d) (eventTmpl A L g t ins.op) e o → P e)
    (hfin : ∀ l q ok sc, P ⟨(M.code g).pc d, .wait l q ok true sc⟩ →
      ∃ before, stateBefore (X.objects l) (X.objects l).length = some before)
    (hblk : ∀ l q sc before, P ⟨(M.code g).pc d, .wait l q false true sc⟩ →
      stateBefore (X.objects l) (X.objects l).length = some before →
      (∃ Y, Consistent L K A mem0 Y ∧ (Y.tr g).take (X.tr g).length = X.tr g ∧
        Y.get (g, (X.tr g).length) = some ⟨(M.code g).pc d, .wait l q false true sc⟩) →
      before.phase % 2 = q % 2 → Blk M X g)
    (h2 : 2 ≤ M.time g d) : Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hl, hat, hinv, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  have hop := hk ins hins
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp [Sched.waitOp] at hop
  rename_i pr b off par acq sc0
  subst hop
  have hpc : t1.pc = (M.code g).pc d := hat.1
  rcases eventTmpl_mbarWait_cases (A := A) (L := L) (g := g) (t := t1) (p := pr) (b := b)
    (off := off) (par := par) (acq := true) (sc := sc0) with ⟨f, hf⟩ | ⟨l, q, k, sc, hq2, htm⟩
  · rw [hf] at hout
    exact ub_stepsE hA hX hp.1 (.inl hne) hrel hrun hl hout
  have hfire : ∀ ok, Fires ((M.code g).pc d) (eventTmpl A L g t1 (.mbarWait pr b off par true sc0))
      ⟨(M.code g).pc d, .wait l q ok true sc⟩ (some (k ok)) := fun ok => by
    rw [htm]; exact ⟨ok, rfl, rfl⟩
  have hP : ∀ ok, P ⟨(M.code g).pc d, .wait l q ok true sc⟩ := fun ok => hS hat hinv hins (hfire ok)
  obtain ⟨before, hst⟩ := hfin l q true sc (hP true)
  have htime : threadTime M X g = M.time g d := threadTime_of hσ
  refine mbar_at_stepsE (b := threadTime M X g - 1) hA hub hmax hp hrel hne
    ⟨l, (M.code g).pc d, q, fun s => s = sc, before, fun t' hr' ok => ?_, hst, ?_⟩ (by omega)
    (by omega)
  · obtain rfl : t' = t := Option.some.inj (Run.det hr' hrun)
    exact ⟨t1, k ok, sc, hl, ⟨_, hout, by rw [hpc]; exact hfire ok⟩, fun _ => rfl⟩
  · rintro s rfl hpar hY
    refine blk_failedPoll (hblk l q s before (hP false) hst ⟨_, hY.1, ?_, ?_⟩ hpar)
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc]
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc,
        Execution.get]

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
