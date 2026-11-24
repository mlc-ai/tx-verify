-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitOrderEnables
public import Lemmas.Order.WaitOrderWaits
public import Core.Assembly.WaitOrder
public import Lemmas.Order.JointWaits
public import Lemmas.Flow.Hooks
public import Core.Assembly.Execution
public import Lemmas.Tensor.TensorDescriptor
public import Mathlib.Data.Fintype.Card
public import Lemmas.Async.AsyncCopy

@[expose] public section

/-! # Acyclicity and object coherence

Tools for the execution-order axioms of `Consistent` (MEM-OBJECT-ORDER-CAUSALITY). The acyclicity
facts that `Consistent` provides (`Consistent.observationCausal`, `Consistent.depStepAcyclic`, from
`WaitAcyclic`). No `stageCausality` path leads from a thread instruction to an asynchronous stage
(`stageCausality.not_to_async`). Induction over a finite node set needs only acyclicity of the
relation it follows (`induction_of_acyclic`, `acyclic_of_rank`). Canonical spins are shapes of the
kernel's code (`Kernel.CanonicalSpin`, DEP-CANONICAL-SPIN), not a property of the execution. -/

namespace PTX
noncomputable section

section
variable {L : Launch} {X : Execution}

/-- The joint requirement implies the observation axiom. -/
theorem WaitAcyclic.observationCausal (h : WaitAcyclic L X) : ObservationCausal L X :=
  fun _ _ ho hc =>
    h _ ((SyncObserved.waits ho).trans
      (Relation.TransGen.lift' id (fun _ _ => stageCausality.waits) _ _ hc))

/-- The joint requirement implies per-object coherence. -/
theorem WaitAcyclic.objectCoherent (h : WaitAcyclic L X) : ObjectCoherent L X := by
  intro o n hn
  have object : ∀ {a c : AsyncCopy.Ref × Bool}, SyncObjectOrder L X o a c → Waits L X a c := by
    cases o with
    | mbar m => exact fun h => ObjectOrder.waits h.1
    | ctaBar c id => exact fun h => ObjectOrder.waits (o := .ctaBar c id) h
    | cluster c => exact fun h => ObjectOrder.waits (o := .cluster c) h
    | tmem cta => exact fun h => ObjectOrder.waits (o := .tmem cta) h
  exact h n (Relation.TransGen.lift' id
    (fun _ _ hac => Or.elim hac stageCausality.waits (fun h => .single (object h))) n n hn)

/-- No local step leaves a state that performs an event. -/
theorem Tau.stuck {K : Kernel} {A : List Assumption} {g : Nat} {t t' : TState} {e : Tmpl}
    (he : out K A L g t = .ev e) (h : Relation.ReflTransGen (Tau K A L g) t t') : t' = t := by
  rcases h.cases_head with rfl | ⟨s, hs, -⟩
  · rfl
  · simp [Tau, he] at hs

/-- The joint requirement implies DEP-ORDER's acyclicity: the dependency steps alone have no
cycle. -/
theorem WaitAcyclic.depStepAcyclic {K : Kernel} (h : WaitAcyclic L X) : DepStepAcyclic L K X :=
  fun n hn => h n (Relation.TransGen.lift' id (fun _ _ hac => DepStep.waits (K := K) hac) n n hn)

/-- A causal edge from a thread instruction's node ends at a thread instruction's node: no
issue edge enters an asynchronous stage. -/
theorem stageCausality.thread_closed {a c : AsyncCopy.Ref × Bool} (h : stageCausality L X a c)
    (ha : ∃ i, a.1 = .thread i) : ∃ j, c.1 = .thread j := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  obtain ⟨i, hi⟩ := ha
  simp only at hi
  subst hi
  rcases h with hstep | ⟨-, -, _, j, -, hf, -⟩ | ⟨-, -, j, hf, -⟩
  · rcases hstep with ⟨rfl, -⟩ | ⟨-, -, hE⟩
    · exact ⟨i, rfl⟩
    · exact hE.elim
  · exact ⟨j, hf⟩
  · exact ⟨j, hf⟩

/-- No causal path leads from a thread instruction to an asynchronous stage. So
`ObservationCausal` places no constraint on the observation of an asynchronous notification,
and the issuer's earlier instructions are never ordered before an observer through the
operation's lifetime (§8.9.1.1). -/
theorem stageCausality.not_to_async {i : EvId} {j : EvId} {p : AsyncCopy.Part} {b b' : Bool} :
    ¬ Relation.TransGen (stageCausality L X) (.thread i, b) (.async j p, b') := by
  intro h
  have : ∀ a c, Relation.TransGen (stageCausality L X) a c → (∃ i, a.1 = .thread i) →
      ∃ j, c.1 = .thread j := by
    intro a c h ha
    induction h with
    | single h => exact stageCausality.thread_closed h ha
    | tail _ h ih => exact stageCausality.thread_closed h ih
  obtain ⟨k, hk⟩ := this _ _ h ⟨i, rfl⟩
  cases hk

end

/-- MEM-OBJECT-ORDER-CAUSALITY: an observation never precedes its source in causality. -/
theorem Consistent.observationCausal {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) : ObservationCausal L X :=
  hX.observation

/-- DEP-ORDER: no dependency step precedes itself (`DependencyOk.acyclic`, no object order
needed). -/
theorem Consistent.depStepAcyclic {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X) : DepStepAcyclic L K X :=
  DepStepAcyclic.of_dependency hX.dependency

/-- A relation along which a natural-number rank strictly increases has no cycle. -/
theorem acyclic_of_rank {α : Type} {R : α → α → Prop} (rank : α → Nat)
    (h : ∀ a c, R a c → rank a < rank c) : ∀ n, ¬ Relation.TransGen R n n := by
  have hlt : ∀ a c, Relation.TransGen R a c → rank a < rank c := fun a c hac => by
    induction hac with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact fun n hn => Nat.lt_irrefl _ (hlt n n hn)

/-- Well-founded induction along any acyclic relation on a finite node set. -/
theorem induction_of_acyclic {α : Type} {R : α → α → Prop}
    (hacyclic : ∀ n, ¬ Relation.TransGen R n n) (nodes : Finset α) (P : α → Prop)
    (step : ∀ node ∈ nodes,
      (∀ previous ∈ nodes, Relation.TransGen R previous node → P previous) → P node) :
    ∀ node ∈ nodes, P node := by
  let Q (a b : {n // n ∈ nodes}) := Relation.TransGen R a.val b.val
  let _ : IsTrans {n // n ∈ nodes} Q := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  let _ : Std.Irrefl Q := ⟨fun a h => hacyclic a.val h⟩
  have hwf : WellFounded Q := Finite.wellFounded_of_trans_of_irrefl Q
  intro node hnode
  apply hwf.induction (C := fun n => P n.val) ⟨node, hnode⟩
  intro current ih
  exact step current.val current.property (fun previous hp hdep => ih ⟨previous, hp⟩ hdep)

end

end PTX
