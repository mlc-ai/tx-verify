-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressNext
public import Lemmas.Kernel.NextReads
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ClosingProgress
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressGuard
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressPoll
import Lemmas.Step.Object
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Lemmas.Flow.AllocTmpl
import Lemmas.Step.TcLoad

public section

/-! # Counted extensions for the launch prologue's local issue sites -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The first allocation substep and permit relinquishment are warp-collective requests. -/
theorem prologue_resource_extension (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    {s : Site}
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.prologue s)))
    (hSite : s = .alloc ∨ s = .relinquish) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hn := ClosingProgress.nonempty_tail hState (by
    rcases hSite with rfl | rfl <;> simp)
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, ins, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have steps : ∃ dst act v,
      out kernel Assumptions.all L g u = .ev (.tc (.resource .one dst act) v) := by
    rcases hSite with rfl | rfl
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
      have hr : u.regs 554 = some (b32 (L.sharedBase + 222752)) :=
        holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
      have hcols : u.regs 555 = some (b32 512) :=
        holds_mem ha.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
      have hSub : u.sub = 0 := ha.2.1
      have hBase := sharedBase_lt hpre
      have hAlign := hpre.sharedAlignment
      rw [← hpre.sharedBase] at hAlign
      rw [tcAlloc_tmpl0 hb hr (by omega) (by omega) hcols hSub] at hout
      exact ⟨_, _, _, hout⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
      refine ⟨none, .relinquish, PTX.next u, ?_⟩
      simpa [eventTmpl, tcTmpl, hb, ofExec, pure, Except.pure] using hout
  obtain ⟨dst, act, v, ho⟩ := steps
  exact PTX.Step.tccoll_counted_extension hX hp.1 (.inl hn) hrel hRun hTau
    (pc := u.pc) (k := .resource .one dst act) (o := some v) ⟨_, ho, rfl, rfl⟩ rfl
    (hX.tmemPairResult.snoc_not_wr nofun) (hX.tcRead_snoc_tc nofun)
    (Interface.all_wf_snoc_of_not_nc hX nofun nofun)

/-- After the local prologue operations, the lane can issue its CTA-wide gate arrival. -/
theorem prologue_gate_extension
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hub : ¬ HasUb X) (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue .barrier))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨t, hRun⟩ := Frame.run_some hX hub hp
  obtain ⟨u, _, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_0)
  change out kernel Assumptions.all L g u = .ev (.bar 0 (PTX.next u) none .sync) at hout
  exact PTX.Step.bar_counted_extension hX hp.1
    (.inl (ClosingProgress.nonempty_tail hState (by simp))) hrel
    (Interface.all_wf_snoc_of_not_nc hX nofun nofun) hRun hTau (o := some (PTX.next u))
    ⟨_, hout, rfl, rfl⟩

/-- A released initializer can execute its mbarrier-initialization fence. -/
theorem prologue_fence_extension
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g)
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue .fence))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne := ClosingProgress.nonempty_tail hState (by simp)
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun h => hSafe (.inl h)) hp
  obtain ⟨u, _, hTau, _, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
  let ev : Event := ⟨u.pc, .fenceMbarInit⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  refine PTX.Step.quiet_counted_extension_reads hX hord hp.1 (.inl hne) hrel hRun hTau
    hStep ?_ ?_ (Step.objectAction_snoc_new ?_ ?_ ?_ ?_ ?_)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ((sync_guarded hX hSafe).snoc (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX) ?_ ?_ ?_ ?_) <;>
  first
    | exact Interface.all_wf_snoc_of_not_nc hX (fun _ _ h => Kind.noConfusion h)
        (fun h => Kind.noConfusion h)
    | trivial
    | (intros; simp_all [ev])

private theorem init_extension
    {t u : TState} {obj : Loc} {count : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : PTX.Step.Released L X g)
    (hRun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hTau : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u)
    (hout : out kernel Assumptions.all L g u = .ev (.mbInit obj count (PTX.next u))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  let ev : Event := ⟨u.pc, .mbInit obj count⟩
  have hStep : EStep kernel Assumptions.all L g u ev (some (PTX.next u)) :=
    ⟨_, hout, rfl, rfl⟩
  have hA (r : Record Ref) : ∀ a ∈ Assumptions.all,
      a.wf L mem0 (X.snocObject g ev (fun _ => none) obj r) :=
    all_wf_snoc_object_of_not_nc hX (ev := ev) (fun _ _ h => Kind.noConfusion h)
      (fun h => Kind.noConfusion h)
  have hG (r : Record Ref) (hr : r.reply.waited = none) :
      SyncGuarded L kernel (X.snocObject g ev (fun _ => none) obj r) :=
    (sync_guarded hX hSafe).snocObject (fun _ _ _ _ he => write_no_release hX he)
      (fun _ tag _ _ _ he => (GlobalWrites.no_rmw hX ⟨tag, he⟩).elim)
      (no_thread_fence hX) (ev := ev)
      (fun _ _ h => Kind.noConfusion h) (fun _ _ _ h => Kind.noConfusion h)
      (fun _ _ h => Kind.noConfusion h)
      (fun _ _ _ _ _ h => Kind.noConfusion (congrArg Event.kind h)) hr
  have hAction (l : Loc) : objectAction (X.snoc g ev (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = obj then some (.init count) else none := by
    rw [objectAction, snoc_get_new]
    change (if obj = l then some (Action.init count) else none) = _
    by_cases h : obj = l
    · simp [h]
    · simp [h, Ne.symm h]
  refine PTX.Step.object_counted_extension_reads (e := ev) (mb := obj) (act := .init count)
    hX hord hg (.inl hne) hrel hRun hTau hStep ⟨trivial, ?_⟩ trivial
    (fun _ _ _ h => Kind.noConfusion h) (fun _ _ _ _ _ _ h => Kind.noConfusion h)
    (fun _ _ h => Kind.noConfusion h) (fun _ _ h => Kind.noConfusion h)
    (fun _ _ _ _ _ h => Kind.noConfusion h) rfl
    (fun _ _ h => Action.noConfusion h) hAction hA hG
  intro k hk
  exact Kind.noConfusion hk

/-- The elected initializer publishes the table entry of the pending barrier. -/
theorem prologue_init_extension (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : SoundThreads P L)
    (hord : ReadsOrdered L X) (hSafe : ¬ Unsafe L kernel Assumptions.all mem0 X)
    (hp : Frame.Pending L X g) (hrel : PTX.Step.Released L X g) {j : Fin 23}
    (hState : Frame.stateAt (Machine.code P L) X g (X.tr g).length =
      some (some (.prologue (.init j)))) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hne := ClosingProgress.nonempty_tail hState (by simp)
  obtain ⟨t, hRun⟩ := Frame.run_some hX (fun h => hSafe (.inl h)) hp
  obtain ⟨u, _, hTau, ha, _, hc, hout⟩ := Frame.end_at hs hp.1 hRun hState
  rw [RingEvents.init_template hpre ha hc] at hout
  exact init_extension hX hord hSafe hp.1 hne hrel hRun hTau hout

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
