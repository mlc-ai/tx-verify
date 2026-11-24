-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Descent
public import Lemmas.Step.Object
public import Lemmas.Step.TcLoad
public import Lemmas.Step.Drain
public import Lemmas.Order.GuardSnoc

@[expose] public section

/-! # The descent step of a thread's next event

A kernel's progress argument ranks open obligations (`Descent.Steps`); a released pending thread
steps by its next event, for every obligation type and rank. The kernel's assumptions put no
well-formedness constraint on executions (`Assumption.WfFree`), and a safe execution has no race
and no mixed-size conflict (`noRace_of_safe`, `noMixed_of_safe`).

* A template of undefined behaviour is performed (`ub_steps`), and so is the undefined behaviour
  of a thread whose machine stopped (`dead_steps`).
* A proxy fence, an mbarrier-initialization fence, a CLC response query and a bulk commit use no
  mbarrier object, no Tensor Core and no memory (`quiet_steps`); an mbarrier initialization or
  arrival is performed with the object's checked record of it (`object_steps`). Either may be a
  thread's first event when its cluster has been launched or no cancellation request exists
  (`Step.Launched`), and keeps synchronization guarded when no write or read-modify-write of the
  execution releases and it has no thread fence.
* A warp-collective `tcgen05` instruction (`coll_steps`) and a named barrier arrival
  (`bar_steps`) are performed, also as a thread's first event once its cluster has been launched
  or no cancellation request exists.
* At an mbarrier wait (`mbar_wait_steps`): a ready barrier is polled successfully, a counted
  extension; otherwise a failed poll is appended, which keeps the execution maximal, and the
  kernel's blocker gives an open obligation of smaller rank there. -/

namespace PTX

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A safe execution has no race. -/
theorem noRace_of_safe (hsafe : ¬ Unsafe L K A mem0 X) : ¬ Race L X :=
  fun h => hsafe (.inr (.inr (.inl h)))

/-- A safe execution has no mixed-size conflict. -/
theorem noMixed_of_safe (hsafe : ¬ Unsafe L K A mem0 X) : ¬ Mixed L X :=
  fun h => hsafe (.inr (.inr (.inr (.inl h))))

namespace Descent

open PTX.Flow MBarrier AsyncCopy

variable {ι : Sort _} {Obl : Execution → ι → Prop} {rank : Execution → ι → Nat} {o : ι}

/-- **A released thread whose template is undefined behaviour steps**: it performs it. -/
theorem ub_steps (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X) {g : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ []) (hrel : Step.Released L X g) {t t1 : TState}
    (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {f : Fault}
    (hout : out K A L g t1 = .ev (.ub f)) : Steps L K A mem0 Obl rank X o :=
  .inl (Step.plain_counted_extension hX hg (.inl hne) hrel hrun hl (o := none) ⟨_, hout, rfl, rfl⟩
    trivial rfl nofun nofun nofun rfl (hX.tmemPairResult.snoc_not_wr nofun) (fun a ha => hA a ha _))

/-- **A released pending thread whose machine stopped steps**: it performs the undefined
behaviour its run reaches (`Frame.end_dead`). -/
theorem dead_steps {C : (g : Nat) → Flow.Code K A L g} (hA : Assumption.WfFree L mem0 A)
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
  exact .inl (Step.dead_counted_extension hX hp.1 hne hrel (fun _ _ a ha => hA a ha _) hrun
    (Frame.end_dead hC hp.1 hrun hσ))

/-- **A released thread performs a proxy fence, an mbarrier-initialization fence, a CLC response
query or a bulk commit**: an event that uses no mbarrier object, no Tensor Core and no memory,
and adds no waiting edge. -/
theorem quiet_steps (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hsafe : ¬ Unsafe L K A mem0 X) (hst : StrongOrdered L X) (hsg : SyncGuarded L K X)
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
  refine .inl (Step.quiet_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
    hst hg hne hrel hrun hl ⟨_, hout, hf⟩ ?_ ?_ (Step.objectAction_snoc_new ?_ ?_ ?_ ?_ ?_) ?_ ?_ ?_
    ?_ ?_ ?_ ?_ (fun a ha => hA a ha _) (hsg.snoc hnr hnrmw hnf ?_ ?_ ?_ ?_)) <;>
  rcases hk with ⟨f, s, rfl⟩ | rfl | ⟨q, r, rfl⟩ | rfl <;>
    first | trivial | (intros; simp_all)

/-- **A released thread initializes or arrives on an mbarrier**, recording `act` on the object
`mb` it names, with the object's checked record. -/
theorem object_steps (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    (hsafe : ¬ Unsafe L K A mem0 X) (hst : StrongOrdered L X) (hsg : SyncGuarded L K X)
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
  refine .inl (Step.object_counted_extension hX (noMixed_of_safe hsafe) (noRace_of_safe hsafe)
    hst hg hne hrel hrun hl ⟨_, hout, hf⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hnp hact
    (fun _ a ha => hA a ha _) (fun _ hw => hsg.snocObject hnr hnrmw hnf ?_ ?_ ?_ ?_ hw)) <;>
  rcases hk with ⟨l, tx, c, rl, sc, rfl⟩ | ⟨l, c, rfl⟩ <;>
    first
      | exact Kind.WaitFree.mk trivial (fun _ h => by cases h)
      | trivial
      | (intros; simp_all)

/-- **A pending thread at an mbarrier wait steps**: a poll of a ready barrier is a counted
extension; otherwise the execution with a failed poll appended is maximal, and `hblk` gives an
open obligation of smaller rank there. -/
theorem mbar_wait_steps (hA : Assumption.WfFree L mem0 A) (hub : ¬ HasUb X)
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
    fun _ _ a ha _ _ => hA a ha _
  by_cases hready : before.phase % 2 ≠ par % 2
  · obtain ⟨t1, u, sc, hl, he, -⟩ := hpoll t hrun true
    exact .inl (Step.poll_counted_extension hX hg hne hrel (hasm true) hrun hl he
      hstate hready)
  · push Not at hready
    obtain ⟨t1, u, sc, hl, he, hq⟩ := hpoll t hrun false
    have hYmax := Step.failed_poll_maximal hmax hg hne hrel (hasm false) hrun hl he hstate
    obtain ⟨o', hobl, hlt⟩ := hblk sc (hq rfl) hready hYmax
    exact .inr ⟨_, o', hYmax, hobl, hlt⟩

/-- **A released thread performs a warp-collective `tcgen05` instruction**, possibly its first
event, given the Tensor Memory allocator result and read obligation of the extended execution. -/
theorem coll_steps (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X) {g : Nat}
    (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Step.Released L X g)
    {t t1 : TState} {u : Option TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {pc : Nat} {k : TcKind}
    (he : EStep K A L g t1 ⟨pc, .tc k⟩ u) (hcoll : isTcColl ⟨pc, .tc k⟩ = true)
    (hres : Tmem.Pair.ResultOk L (X.snoc g ⟨pc, .tc k⟩ (fun _ => none)))
    (hread : TcMma.ReadOk L A (X.snoc g ⟨pc, .tc k⟩ (fun _ => none))) :
    Steps L K A mem0 Obl rank X o :=
  .inl (Step.tccoll_counted_extension hX hg hne hrel hrun hl he hcoll hres hread
    fun a ha => hA a ha _)

/-- **A released thread arrives on a named barrier**, possibly as its first event. -/
theorem bar_steps (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X) {id : Nat}
    {count : Option Nat} {g : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [] ∨ Step.Launched L X g)
    (hrel : Step.Released L X g) {t t1 : TState} {u : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨t1.pc, .bar id count⟩ u) : Steps L K A mem0 Obl rank X o :=
  .inl (Step.bar_counted_extension hX hg hne hrel (fun a ha => hA a ha _) hrun hl he)

end Descent

end

end PTX
