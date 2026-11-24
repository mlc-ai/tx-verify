-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Next
public import Lemmas.Step.DrainInOrder

@[expose] public section

/-! # The descent step of a thread's next event, under assumptions kept in order

`Descent.dead_steps` and `Descent.mbar_wait_steps` for kernels whose assumptions constrain
executions, when the constraints survive every extension that performs its commit arrive-ons in
order and adds no read (`Assumption.WfStep`). Each extension appends a thread event that reads no
memory (undefined behaviour or a poll), and an object record for a poll, and performs no commit
arrive-on. -/

namespace PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

namespace Descent

open PTX.Flow MBarrier AsyncCopy

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released pending thread whose machine stopped steps** (as `dead_steps`). -/
theorem dead_steps_inOrder {C : (g : Nat) → Flow.Code K A L g}
    (hA : Assumption.WfStep sel L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) {h : Nat}
    (hC : ∀ g < L.threads, (C g).Sound) (hp : Frame.Pending L X h)
    (hσ : Frame.stateAt C X h (X.tr h).length = none) (hrel : Step.Released L X h) :
    Steps L K A mem0 Obl rank X o := by
  have hX := hmax.1
  obtain ⟨u, hrun⟩ := Frame.run_some hX hub hp
  have hne : X.tr h ≠ [] := by
    rintro hnil
    rw [hnil, List.length_nil, Frame.stateAt_zero] at hσ
    cases hσ
  exact .inl (Step.dead_counted_extension hX hp.1 hne hrel
    (fun _ _ => hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)) hrun
    (Frame.end_dead hC hp.1 hrun hσ))

/-- **A pending thread at an mbarrier wait steps** (as `mbar_wait_steps`). -/
theorem mbar_wait_steps_inOrder (hA : Assumption.WfStep sel L K mem0 A) (hub : ¬ HasUb X)
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
    fun _ _ a ha _ _ => hA.quiet hX (Execution.le_trans le_snoc (Execution.le_appendObject ..))
      rfl ((Execution.noNewRead_snoc (r := fun _ => none) rfl).trans
        (Execution.noNewRead_of_tr rfl)) a ha
  by_cases hready : before.phase % 2 ≠ par % 2
  · obtain ⟨t1, u, sc, hl, he, -⟩ := hpoll t hrun true
    exact .inl (Step.poll_counted_extension hX hg hne hrel (hasm true) hrun hl he
      hstate hready)
  · push Not at hready
    obtain ⟨t1, u, sc, hl, he, hq⟩ := hpoll t hrun false
    have hYmax := Step.failed_poll_maximal hmax hg hne hrel (hasm false) hrun hl he hstate
    obtain ⟨o', hobl, hlt⟩ := hblk sc (hq rfl) hready hYmax
    exact .inr ⟨_, o', hYmax, hobl, hlt⟩

end Descent

end

end PTX
