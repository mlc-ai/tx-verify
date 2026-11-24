-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
public import Lemmas.Kernel.NextReads
import Lemmas.Step.Object

public section

/-! # Counted scoped barrier arrivals -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof MBarrier AsyncCopy

/-- A released lane can append its defined one-participant CTA release arrival. -/
theorem role_arrival_extension {L : Launch} {mem0 : Mem0} {X : Execution}
    {g bytes : Nat} {obj : Loc} {t u : TState}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hsg : SyncGuarded L kernel X)
    (hnr : ∀ e tag a bs, X.get e = some ⟨tag, .wr a bs⟩ → a.release = false)
    (hnrmw : ∀ e tag a old new, X.get e = some ⟨tag, .rmw a old new⟩ → a.release = false)
    (hnf : ∀ e sem scope, ¬ X.ThreadFence e sem scope)
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : PTX.Step.Released L X g)
    (hRun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hout : out kernel Assumptions.all L g u = .ev (.arrive obj bytes (PTX.next u) 1 true .cta)) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let ev : Event := ⟨u.pc, .arrive obj bytes 1 true .cta⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  have hA (r : Record Ref) : ∀ a ∈ Assumptions.all,
      a.wf L mem0 (X.snocObject g ev (fun _ => none) obj r) :=
    all_wf_snoc_object_of_not_nc hX (ev := ev) (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h)
  have hG (r : Record Ref) (hr : r.reply.waited = none) :
      SyncGuarded L kernel (X.snocObject g ev (fun _ => none) obj r) :=
    hsg.snocObject hnr hnrmw hnf (ev := ev)
      (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h)
      (fun _ _ h => Kind.noConfusion h)
      (fun _ _ _ _ _ h => Kind.noConfusion (congrArg Event.kind h)) hr
  have hAction (l : Loc) : objectAction (X.snoc g ev (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = obj then some (.arrive 1 bytes) else none := by
    rw [objectAction, snoc_get_new]
    change (if obj = l then some (Action.arrive 1 bytes) else none) = _
    by_cases h : obj = l
    · simp [h]
    · simp [h, Ne.symm h]
  refine PTX.Step.object_counted_extension_reads (e := ev) (mb := obj) (act := .arrive 1 bytes)
    hX hord hg (.inl hne) hrel hRun hTau hStep ⟨trivial, ?_⟩ trivial
    (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
    (fun _ _ h => Kind.noConfusion h) (fun _ _ h => Kind.noConfusion h)
    (fun _ _ _ _ _ h => Kind.noConfusion h) rfl
    (fun _ _ h => Action.noConfusion h) hAction hA hG
  intro k hk
  exact Kind.noConfusion hk

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
