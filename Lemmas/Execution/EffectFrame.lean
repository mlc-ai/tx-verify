-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.WaitingClosure
public import Lemmas.Order.CompletionFrame

@[expose] public section

/-! An effect-only extension `{ X with rf, tensor, tensorStores, clc }` adds asynchronous
stages (the refs `N`) that wait on nothing and are recorded in no object. Outside `N` every
order relation of the extension is one of `X`, so the execution-order axioms transfer. -/
namespace PTX
open AsyncCopy
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}
  {T : EvId → Option TensorCopy.Observation} {S : EvId → Option TensorStore.Observation}
  {C : EvId → Clc.Effects} {R : Ref → Nat → Option Ref}

set_option quotPrecheck false in
local notation "Y" => ({ X with rf := R, tensor := T, tensorStores := S, clc := C } : Execution)

/-- Keeping thread read sources fixes every base happens-before edge. -/
theorem baseCausality_new_effect (hrf : ∀ e k, R (.thread e) k = X.rf (.thread e) k) {e f : EvId} :
    baseCausality L Y e f ↔ baseCausality L X e f := by
  have hbase : ∀ a b, (po Y a b ∨ CtaBarSync L Y a b ∨ MSync L Y a b ∨ ClusterSync L Y a b ∨
      WarpBarSync L Y a b ∨ synchronizesWith L Y a b ∨ FenceSync L Y a b) ↔
      (po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
        WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) := by
    intro a b
    have hm : synchronizesWith L Y a b ↔ synchronizesWith L X a b := by
      simp only [synchronizesWith, Execution.MemWrites, Execution.MemReads, Execution.Rmw,
        Execution.Writes, Execution.Reads, Execution.get, hrf]
    have hf : FenceSync L Y a b ↔ FenceSync L X a b := by
      simp only [FenceSync, FenceScSync, StrongRead, ScStrong, ReleaseHead, AcquireTail,
        Execution.MemWrites, Execution.Rmw, Execution.Writes, Execution.Reads,
        Execution.ThreadFence, Execution.get, hrf]
    rw [hm, hf]
    rfl
  constructor <;> intro h
  · induction h with
    | single h => exact .single ((hbase _ _).mp h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mp h)
  · induction h with
    | single h => exact .single ((hbase _ _).mpr h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mpr h)

/-- No `Waits` edge of `Y` leaves the new refs `N`, so `N` is closed under `Waits` with a growing
rank. This is the `closed` field of `SinkFrame` for `S = fun n => N n.1`. -/
theorem closed_new_effect (N : Ref → Prop)
    (hnew : ∀ u v, N u.1 → Waits L Y u v → N v.1 ∧ u.2 = false ∧ v.2 = true) :
    ∃ rank : AsyncCopy.Ref × Bool → Nat,
      ∀ u v, Waits L Y u v → N u.1 → N v.1 ∧ rank u < rank v := by
  refine ⟨fun n => if n.2 then 1 else 0, ?_⟩
  rintro ⟨e, b⟩ ⟨f, b'⟩ h hu
  obtain ⟨hv, hb, hb'⟩ := hnew (e, b) (f, b') hu h
  have hb₂ : b = false := hb
  have hb₃ : b' = true := hb'
  refine ⟨hv, ?_⟩
  show (if b then 1 else 0) < (if b' then 1 else 0)
  rw [hb₂, hb₃]
  exact Nat.zero_lt_one

-- The eleven fields of `SinkFrame` over `S = fun n => N n.1` fall into two groups.
--   * `get`, `asyncObserved`, `object`, `objectSync` and `asyncSelf` read `tr`, `async`,
--     `objects`, `barriers`, `clusters` and `tmemHistory`, which an effect-only extension keeps,
--     so each transfers definitionally; `issue` needs only `hthr`.
--   * `cause`, `observed` and `dep` read a relation that mentions `rf`, `tensor`, `tensorStores`
--     or `clc` at asynchronous nodes, and the extension changes exactly those rows: the
--     `StageOrder` disjunct of `cause` reads `StageEdge` and its `CopyReleaseSync` disjunct reads
--     `AsyncCopy.AsyncObserved`, the `MbarObserved` disjunct of `observed` reads `AsyncPresent`
--     and `AsyncCopy.WaitObserves`, and `dep` reads those same relations. Nothing else in this
--     lemma fixes those rows (the read sources of the thread events are not enough), so these
--     three fields are the hypotheses `hstage`, `hsync` and `hdep`.
-- `closed` is `closed_new_effect` above, from the sink closure `hnew`. `initFence` then follows
-- from `hinit` and `hstage`: a `stageCausality` edge lies on a `Waits` path, and `S` is closed
-- under `Waits`, so a `stageCausality` path between two old nodes stays outside `S`
-- (`SinkFrame.old_path`), and its endpoints are thread nodes, where `hthr` keeps it outside.
/-- **An effect-only extension is a sink frame.** The new refs `N` are asynchronous stages that
wait on nothing, the orders of the extension at the old nodes are those of `X`, and the first
clause of EXT-ASYNC-OBJECT at an update whose issue is old is that of `X`. -/
theorem sinkFrame_new_effect (N : Ref → Prop)
    (hthr : ∀ j, ¬ N (.thread j))
    (hnew : ∀ u v, N u.1 → Waits L Y u v → N v.1 ∧ u.2 = false ∧ v.2 = true)
    (hX : AsyncObjectOrdered L X) (hinit : InitFenceOrdered L X)
    (hstage : ∀ u v, ¬ N u.1 → ¬ N v.1 → stageCausality L Y u v →
      Relation.TransGen (stageCausality L X) u v)
    (hsync : ∀ x w, ¬ N x → ¬ N w → SyncObserved L Y x w → SyncObserved L X x w)
    (hdep : ∀ u v, ¬ N u.1 → ¬ N v.1 → DepStep L K Y u v →
      Relation.TransGen (DepStep L K X) u v) :
    SinkFrame L K A X Y (fun n => N n.1) := by
  obtain ⟨rank, hrank⟩ := closed_new_effect N hnew
  refine ⟨⟨rank, hrank⟩, hstage, hsync, fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h, hdep,
    fun _ i _ _ _ hi => (hthr i hi).elim, fun m i p y hb => (hX m i p y hb).1,
    fun _ _ _ _ _ _ h => h, ?_, fun _ _ => rfl⟩
  intro m init w y hs ht
  exact hinit m init w y hs (SinkFrame.old_path (S := fun n => N n.1) hrank
    (fun _ _ h => stageCausality.waits h) hstage ht (hthr y.issuer)).2

/-- **An effect-only extension that adds stages is a sink frame.** The new stages `N` are
asynchronous stages absent from `X`; no stage edge and no object record starts at one, so they
lead by `Waits` only to their own completion points and to the returns of the group waits they
witness, which have not returned in `X` (`sinkFrame_completion`). Outside these nodes the presence
of every node, the needs of every event, the thread read sources and the observed notifications
are those of `X`, which fixes every order relation. -/
theorem sinkFrame_effect {mem0 : Mem0} (hX : Consistent L K A mem0 X) (N : Ref → Prop)
    (hthr : ∀ j, ¬ N (.thread j))
    (habsent : ∀ i p, N (.async i p) → ¬ X.AsyncPresent i p)
    (hpres : ∀ e, ¬ N e → (Y).RefPresent e → X.RefPresent e)
    (hneeds : ∀ e, Needs L Y e = Needs L X e)
    (hrf : ∀ e k, R (.thread e) k = X.rf (.thread e) k)
    (hobs : ∀ i p w ws, AsyncObserved Y i p w true ws → AsyncObserved X i p w true ws)
    (hedge : ∀ x f, N x → ¬ StageEdge Y x f)
    (hrec : ∀ m r, r ∈ X.objects m → ¬ N r.id) :
    SinkFrame L K A X Y (CompletionNodes L Y N) := by
  have hold : ∀ {u : Ref × Bool}, ¬ CompletionNodes L Y N u → ¬ N u.1 :=
    fun hu h => hu (.inl h)
  refine sinkFrame_completion N hthr (fun u v hu h => ?_) (fun w x hx hw v => ?_)
    (fun u v hu hv hc => ?_) (fun x w hx hw h => ?_) (fun _ _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) (fun u v hu hv hc => ?_)
    (fun m j p y hb => (hX.asyncObject m j p y hb).1) (fun _ _ _ _ _ _ h => h) hX.initFence
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ => rfl)
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    change N e at hu
    rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
      ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
      ⟨_, _, ha⟩ | ⟨_, _, m, a, c, r, q, ha, hid, _⟩ | ⟨j, k, he, _⟩ | ⟨hb, hb', w, hw, hwit⟩ |
      ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
      ⟨_, _, j, k, he, _⟩ | ⟨_, _, _, _, j, p, he, _⟩
    · subst he
      exact .inl ⟨hu, hb, hb'⟩
    all_goals try (subst he; exact (hthr _ hu).elim)
    · rcases ha with ⟨he, hb, hb', _⟩ | ⟨_, _, ha⟩
      · subst he
        exact .inl ⟨hu, hb, hb'⟩
      · exact (hedge e f hu ha).elim
    · exact (hrec m r (List.mem_of_getElem? ha) (hid ▸ hu)).elim
    · exact .inr ⟨hb, hb', w, hw, hwit⟩
  · cases x with
    | thread j => exact (hthr j hx).elim
    | async i p =>
      obtain ⟨hgw, hr⟩ := witness_absent_pending hX.dependency.ready (hneeds w)
        (habsent i p hx) hw
      exact groupWait_return_not_waits (X := Y) hgw (hgw.last hr)
        (fun m r hr' => hgw.not_record hX.tma.2.2.1 hr')
        (fun c r hr' => hgw.not_cluster hX.cluster hr')
        (fun cta x hx' => hgw.not_participates hX.tmemPair hx') v
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | ⟨h1, h2, j, k, h3, h4, hc⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X) («Y» := Y) (fun _ _ h => h)
        (fun _ _ h => h) (hpres _ (hold hu)) (hpres _ (hold hv)) hc))
    · exact .single (.inr (.inl ⟨h1, h2, j, k, h3, h4, (baseCausality_new_effect hrf).mp hc⟩))
    · obtain ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, h7, h8⟩ := hc
      exact .single (.inr (.inr ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, hobs _ _ _ _ h7, h8⟩))
  · rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · exact .inl ⟨⟨hpres _ (hold hx) hm.1, hm.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres _ (hold hx) h3, h4, h5⟩
  · obtain ⟨e, b⟩ := u
    obtain ⟨f, b'⟩ := v
    rcases hc with hc | hc | ⟨h1, h2, j, hj, fills, hn', hx, hf⟩ | hc
    · exact .single (.inl (StageOrder.transfer (X := X) («Y» := Y) (fun _ _ h => h)
        (fun _ _ h => h) (hpres _ (hold hu)) (hpres _ (hold hv)) hc))
    · exact .single (.inr (.inl (IssueStage.transfer (X := X) («Y» := Y) (fun _ => rfl)
        (hpres _ (hold hv)) hc)))
    · rw [hneeds] at hn'
      exact .single (.inr (.inr (.inl ⟨h1, h2, j, hj, fills, hn', hpres _ (hold hu) hx, hf⟩)))
    · exact .single (.inr (.inr (.inr hc)))

end
end PTX
