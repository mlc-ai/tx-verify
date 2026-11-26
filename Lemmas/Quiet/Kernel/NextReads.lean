-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.NextReads
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Kernel.NextInOrder

@[expose] public section

/-! # Undefined behaviour, quiet and object steps under quiet extensions

`Lemmas/Kernel/NextReads.lean` under `Assumption.WfQuiet`. -/

namespace PTX
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
  {sel : Nat → Bool}

namespace Descent
open PTX.Flow MBarrier AsyncCopy

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released thread whose template is undefined behaviour steps** (as `ub_steps`). -/
theorem ub_steps_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g) {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {f : Fault}
    (hout : out K A L g t1 = .ev (.ub f)) : Steps L K A mem0 Obl rank X o :=
  .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := none) ⟨_, hout, rfl, rfl⟩
    trivial rfl nofun nofun nofun rfl (hX.tmemPairResult.snoc_not_wr nofun)
    (hA.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl)))

/-- **A released thread performs a proxy fence, an mbarrier-initialization fence, a CLC response
query or a bulk commit** (as `quiet_steps`). -/
theorem quiet_steps_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X) (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s)
    {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g)
    {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} {k : Kind} {u : TState}
    (hout : out K A L g t1 = .ev m) (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
    (hk : (∃ f s, k = .fenceProxy f s) ∨ k = .fenceMbarInit ∨ (∃ q r, k = .clcQuery q r) ∨
      k = .bulkCommit) :
    Steps L K A mem0 Obl rank X o := by
  refine .inl (Step.quiet_counted_extension_reads hX hord hg hne hrel hrun hl ⟨_, hout, hf⟩ ?_ ?_
    (Step.objectAction_snoc_new ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hA.quiet hX le_snoc rfl (Execution.quietExt_snoc ?_ ?_))
    (hsg.snoc hnr hnrmw hnf ?_ ?_ ?_ ?_)) <;>
  rcases hk with ⟨f, s, rfl⟩ | rfl | ⟨q, r, rfl⟩ | rfl <;> first | trivial | (intros; simp_all)

/-- **A released thread initializes or arrives on an mbarrier** (as `object_steps`). -/
theorem object_steps_inOrderQ (hA : Assumption.WfQuiet sel L K mem0 A)
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X) (hsg : SyncGuarded L K X)
    (hnr : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e pc a o n, X.get e = some ⟨pc, .rmw a o n⟩ → a.release = false)
    (hnf : ∀ e sem s, ¬ X.ThreadFence e sem s)
    {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g)
    {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl} {k : Kind} {u : TState}
    (hout : out K A L g t1 = .ev m) (hf : Fires t1.pc m ⟨t1.pc, k⟩ (some u))
    (hk : (∃ l tx c rl sc, k = .arrive l tx c rl sc) ∨ ∃ l c, k = .mbInit l c)
    {mb : Loc} {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g ⟨t1.pc, k⟩ (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none) :
    Steps L K A mem0 Obl rank X o := by
  refine .inl (Step.object_counted_extension_reads hX hord hg hne hrel hrun hl ⟨_, hout, hf⟩
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnp hact
    (fun _ => hA.quiet hX (Execution.le_trans le_snoc (Execution.le_appendObject ..)) rfl
      ((Execution.quietExt_snoc (r := fun _ => none) ?_ ?_).trans
        (Execution.quietExt_of_tr rfl)))
    (fun _ hw => hsg.snocObject hnr hnrmw hnf ?_ ?_ ?_ ?_ hw)) <;>
  rcases hk with ⟨l, tx, c, rl, sc, rfl⟩ | ⟨l, c, rfl⟩ <;>
    first
      | exact Kind.WaitFree.mk trivial (fun _ h => by cases h)
      | trivial
      | (intros; simp_all)

end Descent

end

end PTX
