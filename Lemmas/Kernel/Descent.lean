-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Frame
public import Lemmas.Kernel.PlainStep
public import Lemmas.Kernel.Goals
public import Lemmas.Kernel.ProgressDescent
public import Lemmas.Execution.NoAsync
public import Lemmas.Execution.NoBarArrive

@[expose] public section

/-! # `ProgressGoal` by descent

A kernel's progress argument names the obligations of an incomplete execution (`Obl`, covering
every incomplete maximal execution) and ranks them. Every open obligation of a maximal execution
steps (`Steps`): it extends the execution by a counted event, or passes to an open obligation of
smaller rank in a maximal execution. Then every maximal execution is complete
(`progress_of_steps`).

Without asynchronous events the only obligations are the pending threads
(`Frame.Pending`, `pending_of_incomplete`, `progress_of_threads`). A pending thread of a kernel
without asynchronous and shuffle instructions whose last event is not an unreleased barrier, in
an execution without undefined behaviour, extends the execution (`plain_extends`): its machine's
last state is a site, from which it performs its next event, or the machine stopped and the
thread performs its undefined behaviour (`Execution.NoTma.next_extends`). A kernel without
barriers is then complete on every maximal execution (`progress_of_plain`). -/

namespace PTX.Descent

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}

/-- The descent step for obligation `o` of `X`: a counted consistent extension, or an open
obligation of smaller rank in a maximal execution. -/
def Steps (L : Launch) (K : Kernel) (A : List Assumption) (mem0 : Mem0) {ι : Sort _}
    (Obl : Execution → ι → Prop) (rank : Execution → ι → Nat) (X : Execution) (o : ι) : Prop :=
  (∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L) ∨
    ∃ Y o', Maximal L K A mem0 Y ∧ Obl Y o' ∧ rank Y o' < rank X o

/-- **Descent**: if the obligations cover every incomplete maximal execution and every open
obligation of a maximal execution steps, every maximal execution is complete. -/
theorem progress_of_steps {ι : Sort _} (Obl : Execution → ι → Prop)
    (rank : Execution → ι → Nat)
    (hcover : ∀ X, Maximal L K A mem0 X → ¬ Complete L X → ∃ o, Obl X o)
    (h : ∀ X o, Maximal L K A mem0 X → Obl X o → Steps L K A mem0 Obl rank X o) :
    ProgressGoal K A L mem0 :=
  Proof.ProgressDescent.maximal_complete_of_descent Obl rank hcover h

/-- An incomplete execution without asynchronous events has a pending thread. -/
theorem pending_of_incomplete {X : Execution} (hX : Consistent L K A mem0 X) (hn : X.NoTma)
    (h : ¬ Complete L X) : ∃ g, Frame.Pending L X g := by
  classical
  by_contra hno
  push Not at hno
  apply h
  refine hn.complete_of_exits L fun g hg => ?_
  have hng := hno g
  simp only [Frame.Pending, not_and, not_forall, not_not] at hng
  by_cases hc : ClcCanceled L X g
  · obtain ⟨-, req, ho⟩ := hc
    obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue ho
    cases hn _ _ _ hi
  · exact hng hg hc

/-- **Descent over the pending threads** of a kernel without asynchronous instructions. -/
theorem progress_of_threads (hK : K.NoTma) (rank : Execution → Nat → Nat)
    (h : ∀ X g, Maximal L K A mem0 X → Frame.Pending L X g →
      Steps L K A mem0 (Frame.Pending L) rank X g) :
    ProgressGoal K A L mem0 :=
  progress_of_steps (Frame.Pending L) rank
    (fun _ hmax hc => pending_of_incomplete hmax.1 (noTma_of_consistent hK hmax.1) hc) h

variable {C : (g : Nat) → Flow.Code K A L g} {X : Execution} {g : Nat}

/-- **A pending thread of a plain kernel extends the execution**, when its last event is no
barrier that is not ready, its first event is not a barrier, and the execution has no undefined
behaviour. -/
theorem plain_extends (hK : K.NoTma) (hS : K.NoShfl) (hR : K.NoAtomic)
    (hC : ∀ g < L.threads, (C g).Sound)
    (hX : Consistent L K A mem0 X) (ht : Frame.Tracked C X) (hub : ¬ HasUb X)
    (hp : Frame.Pending L X g)
    (hinit : ∀ ins, K.code[(C g).pc (C g).init]? = some ins → ins.op.isBar = false)
    (hbl : ∀ id count pc, X.IsBarrier (g, (X.tr g).length - 1) id count pc →
      Ready L X (g, (X.tr g).length - 1))
    (hwf : X.ExtWf A L mem0 g) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hg := hp.1
  have hn := noTma_of_consistent hK hX
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  cases hσ : Frame.stateAt C X g (X.tr g).length with
  | none =>
    obtain ⟨t1, f, hl, hout⟩ := Frame.end_dead hC hg hrun hσ
    exact hn.next_extends hX hg hrun hl hout rfl rfl rfl trivial nofun hbl hwf
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht g _ hg)
    | some d =>
      obtain ⟨t1, ins, hl, -, -, hc, hout⟩ := Frame.end_at hC hg hrun hσ
      obtain ⟨hm, hs, hrmw, hsr⟩ := out_plain hK hS hR hout
      refine hn.next_extends hX hg hrun hl hout hm hs hrmw hsr ?_ hbl hwf
      intro id u c hb h0
      have hd : d = (C g).init := by
        rw [h0] at hσ
        have h0' : Frame.stateAt C X g 0 = some (some d) := by simpa using hσ
        rw [Frame.stateAt_zero] at h0'
        exact (Option.some.inj (Option.some.inj h0')).symm
      subst hd
      have hop := List.all_eq_true.mp hK ins (List.mem_of_getElem? hc)
      simp only [Bool.not_eq_true'] at hop
      have := eventTmpl_not_bar (A := A) (L := L) (g := g) (t := t1) hop (hinit ins hc)
      rw [hb] at this
      cases this

/-- **`ProgressGoal` of a plain kernel without barriers**: every pending thread of a maximal
execution extends it. -/
theorem progress_of_plain (hK : K.NoTma) (hS : K.NoShfl) (hR : K.NoAtomic)
    (hC : ∀ g < L.threads, (C g).Sound)
    (hsafe : SafeGoal K A L mem0) (ht : ∀ X, Consistent L K A mem0 X → Frame.Tracked C X)
    (hnb : ∀ X, Consistent L K A mem0 X → ∀ e id count pc, ¬ X.IsBarrier e id count pc)
    (hinit : ∀ g < L.threads, ∀ ins, K.code[(C g).pc (C g).init]? = some ins →
      ins.op.isBar = false)
    (hwf : ∀ X g, Consistent L K A mem0 X → X.ExtWf A L mem0 g) : ProgressGoal K A L mem0 :=
  progress_of_threads hK (fun _ _ => 0) fun X g hmax hp =>
    .inl (plain_extends hK hS hR hC hmax.1 (ht X hmax.1) (fun h => hsafe.2 X hmax.1 (.inl h)) hp
      (hinit g hp.1) (fun _ _ _ hb => (hnb X hmax.1 _ _ _ _ hb).elim) (hwf X g hmax.1))

end

end PTX.Descent
