-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WaitSite
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Progress.Rank
public import Lemmas.Quiet.Kernel.NextReads

@[expose] public section

/-! # A wait site steps under quiet extensions

`Sched.wait_site_steps` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX PTX.Flow MBarrier
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

theorem wait_site_stepsQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → waitOp ins.op = true)
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
  cases op <;> simp [waitOp] at hop
  rename_i pr b off par acq sc0
  subst hop
  have hpc : t1.pc = (M.code g).pc d := hat.1
  rcases eventTmpl_mbarWait_cases (A := A) (L := L) (g := g) (t := t1) (p := pr) (b := b)
    (off := off) (par := par) (acq := true) (sc := sc0) with ⟨f, hf⟩ | ⟨l, q, k, sc, hq2, htm⟩
  · rw [hf] at hout
    exact Descent.ub_steps_inOrderQ hA hX hp.1 hne hrel hrun hl hout
  have hfire : ∀ ok, Fires ((M.code g).pc d) (eventTmpl A L g t1 (.mbarWait pr b off par true sc0))
      ⟨(M.code g).pc d, .wait l q ok true sc⟩ (some (k ok)) := fun ok => by
    rw [htm]; exact ⟨ok, rfl, rfl⟩
  have hP : ∀ ok, P ⟨(M.code g).pc d, .wait l q ok true sc⟩ := fun ok => hS hat hinv hins (hfire ok)
  obtain ⟨before, hst⟩ := hfin l q true sc (hP true)
  have htime : threadTime M X g = M.time g d := threadTime_of hσ
  refine mbar_at_stepsQ (b := threadTime M X g - 1) hA hub hmax hp hrel hne
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

end PTX.Sched
