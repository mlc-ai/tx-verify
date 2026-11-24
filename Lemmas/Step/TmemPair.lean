-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairRecord
public import Lemmas.Tmem.TmemPairOrder
public import Lemmas.Tmem.TmemPairCompletionFrame
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Snoc.QuietReturnSink
public import Lemmas.Order.WaitingClosure

@[expose] public section

/-! # Tensor Memory allocator records and pairings as progress steps

A proof tool for the progress argument about Tensor Memory allocation management. Two kinds of
counted steps complete resource operations, generically in the kernel `K` and the assumptions
`A`:

* `entry_counted`: a CTA's allocator performs a warp request (`Execution.recordEntry`) when
  `EntryReady` holds: the request is valid, for cta_group::1 the earlier requests of its warp
  are completed, its CTA's allocator has not performed it, and the replay accepts it. A
  cta_group::1 record completes its operation. Since a returned instruction is performed
  (DEP-TMEM-ALLOC-WAIT), every lane of a request not yet performed is its thread's last
  event (`EntryReady.last`), so the request can be performed after its CTA's history
  (`EntryReady.after`).
* `pairing_counted`: two recorded cta_group::2 requests of a CTA pair are paired
  (`Execution.recordPairing`) when `PairingReady` holds, completing their operation. Its
  waiting participants are pending and terminal, so the new waiting edges end in sinks.

Both records are counted by `pairSize`, so each is a counted extension. Further:

* `warp_entry_counted`: the cta_group::1 normalization for a thread's last event, built from
  its warp: all 32 lanes of its warp sit at the same operation, and the record is the owner
  warp's request (`ownerRecord`).
* `last_of_not_performed`, `pending_is_last`: an operation not performed, or waiting and not
  covered, is the last event of its thread. -/

namespace PTX.Step
open PTX AsyncCopy Tmem.Pair
noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {cta : Nat} {r : Requests} {q : WarpRequest × WarpRequest}

/-- An allocation-management event that its CTA's allocator has not performed has no later
event of its thread: its instruction has not returned. -/
theorem last_of_not_performed (hX : Consistent L K A mem0 X) {j : EvId} {pc : Nat}
    {group : CtaGroup} {dst : Option Loc} {request : Tmem.Request}
    (hget : X.get j = some ⟨pc, .tc (.resource group dst request)⟩) (hn : ¬ Performed L X j) :
    j.2+1 = (X.tr j.1).length := by
  have hlt := len_of_get hget
  by_contra hne
  exact hn (hX.tmemPairBlocking.performed hget (by omega))

/-- A waiting participant that is not covered has no later event of its thread, since a later
event of a blocking operation requires it to be covered. -/
theorem pending_is_last (hX : Consistent L K A mem0 X) {j : EvId} (hm : MustWait X j)
    (hn : ¬ Covered L X j) : j.2+1 = (X.tr j.1).length := by
  have hlt : j.2 < (X.tr j.1).length := by
    obtain ⟨pc, grp, dst, act, hget, -⟩ := hm
    exact len_of_get hget
  by_contra hne
  exact hn (hX.tmemPairBlocking.covered hm (by omega))

/-- A lane of a warp request that is not yet recorded has no outgoing allocator order edge. -/
theorem not_precedes_of_fresh (hX : Consistent L K A mem0 X) (hv : r.Valid L X)
    (hnew : ∀ x ∈ X.tmemHistory cta, ∀ l l' : Fin 32, x.own.event L l ≠ r.own.event L l')
    (hkey : r.own.cta = cta)
    (l : Fin 32) (cta' : Nat) (j : EvId) : ¬ Precedes L X cta' (r.own.event L l) j := by
  intro hp
  obtain ⟨⟨x, hx, l', he⟩, -⟩ := hp.recorded
  have hxv := ((hX.tmemPair.1 cta').1 x hx).2.2
  by_cases hc : cta' = cta
  · subst hc
    exact hnew x hx l' l he
  · have e1 := (WarpRequest.event_props hxv l').1
    have e2 := (WarpRequest.event_props hv.2.2 l).1
    rw [he, e2, hkey, ((hX.tmemPair.1 cta').2.1 x hx)] at e1
    exact hc e1.symm

/-- A pending allocation's lane-0 return cannot publish coverage: the return is terminal and
no happens-before chain leaves it. This is the source fact behind the read obligation. -/
theorem pending_entry_no_covers (hX : Consistent L K A mem0 X) (hv : r.Valid L X)
    (hlast : (r.own.event L 0).2 + 1 = (X.tr (r.own.event L 0).1).length)
    (hord : ∀ cta' j, ¬ Precedes L X cta' (r.own.event L 0) j)
    (hnp : ∀ q ∈ X.tmemPairing, q.1 ≠ r.own ∧ q.2 ≠ r.own) :
    ∀ owner e col, ¬ Covers L (X.recordEntry cta r) r owner e col := by
  intro owner e col ⟨n, base, ha, _, _, _, hhb⟩
  rcases hhb with hhb | ⟨q, hq, p, hqp, -⟩
  swap
  · rcases hqp with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact (hnp q hq).1 h1
    · exact (hnp q hq).2 h2
  have hget := hv.2.2.2.2.1 0
  have hreq : r.own.request = .alloc n := by rw [← hv.2.1, ha]; rfl
  rw [hreq] at hget
  change PTX.baseCausality L X (r.own.event L 0) e at hhb
  obtain ⟨v, hfirst, _⟩ := Relation.TransGen.head'_iff.mp (baseCausality_waits hhb)
  exact quiet_return_sink_of_effects hX.effectValidity hX.cluster hget rfl hlast
    hord v hfirst

/-- The premises under which CTA `cta`'s allocator can perform the request of record `r` now.
Each field is an actual fact about the execution: the valid warp request, for cta_group::1 its
completed predecessors, that the CTA's allocator has not performed it, its CTA, and the replay
(`run`). -/
structure EntryReady (L : Launch) (X : Execution) (cta : Nat) (r : Requests) : Prop where
  valid : r.Valid L X
  ready : r.group = .one → CompletionReady L X [r.own]
  fresh : ∀ x ∈ X.tmemHistory cta, x.own ≠ r.own
  src : r.own.cta = cta
  run : runRequests {} (X.tmemHistory cta ++ [r]) ≠ .blocked

/-- No lane of a request that its CTA's allocator has not performed is a lane of a record. -/
theorem EntryReady.lane_ne (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r)
    {x : Requests} (hx : x ∈ X.tmemHistory cta) (l l' : Fin 32) :
    x.own.event L l ≠ r.own.event L l' :=
  fun he => hR.fresh x hx (((hX.tmemPair.1 cta).1 x hx).2.2.ext hR.valid.2.2 he)

/-- No lane of a ready request is performed. -/
theorem EntryReady.not_performed (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r)
    (l : Fin 32) : ¬ Performed L X (r.own.event L l) := by
  rintro ⟨cta', x, hx, l', he⟩
  have hxr : x.own = r.own := ((hX.tmemPair.1 cta').1 x hx).2.2.ext hR.valid.2.2 he
  have hc : cta' = cta := by rw [← (hX.tmemPair.1 cta').2.1 x hx, hxr, hR.src]
  subst hc
  exact hR.fresh x hx hxr

/-- **Every lane of a ready request is its thread's last event** (DEP-TMEM-ALLOC-WAIT): an
instruction whose request is not performed has not returned. -/
theorem EntryReady.last (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r)
    (l : Fin 32) : (r.own.event L l).2 + 1 = (X.tr (r.own.event L l).1).length :=
  last_of_not_performed hX (hR.valid.2.2.2.2.1 l) (hR.not_performed hX l)

/-- A ready request can be performed after its CTA's history: each lane's return is a sink. -/
theorem EntryReady.after (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r) :
    AfterHistory L X cta r := by
  rintro x hx i j ⟨l, rfl⟩ ⟨l', rfl⟩ hc
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp hc with heq | ht
  · simp only [Prod.mk.injEq, AsyncCopy.Ref.thread.injEq, and_true] at heq
    exact hR.lane_ne hX hx l l' heq
  · obtain ⟨c, hfirst, -⟩ := Relation.TransGen.head'_iff.mp ht
    obtain ⟨v, hw, -⟩ := Relation.TransGen.head'_iff.mp (stageCausality.waits hfirst)
    have hget := hR.valid.2.2.2.2.1 l'
    exact quiet_return_sink_of_effects hX.effectValidity hX.cluster hget rfl (hR.last hX l')
      (not_precedes_of_fresh hX hR.valid (fun _ hx => hR.lane_ne hX hx) hR.src l') v hw

/-- A ready request is in no pairing: a paired request is recorded (`HistoriesOk`). -/
theorem EntryReady.not_paired (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r) :
    ∀ q ∈ X.tmemPairing, q.1 ≠ r.own ∧ q.2 ≠ r.own := by
  intro q hq
  obtain ⟨-, ⟨a, ha, ha1, -⟩, b, hb, hb1, -⟩ := hX.tmemPair.2.1 q hq
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · rw [h1, hR.src] at ha
    exact hR.fresh a ha (ha1.trans h1)
  · rw [h2, hR.src] at hb
    exact hR.fresh b hb (hb1.trans h2)

/-- Recording a ready request keeps the execution consistent. -/
theorem consistent_entry (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordEntry cta r)) :
    Consistent L K A mem0 (X.recordEntry cta r) :=
  consistent_recordEntry hX hR.valid (hR.after hX) hR.src (fun _ hx => hR.lane_ne hX hx)
    (hR.last hX) (not_precedes_of_fresh hX hR.valid (fun _ hx => hR.lane_ne hX hx) hR.src) hR.run
    (ResultOk.recordEntry hX.tmemPairResult (hR.last hX 0))
    (readOk_recordEntry hX.tcRead hX.tma.2.1 (pending_entry_no_covers hX hR.valid (hR.last hX 0)
      (not_precedes_of_fresh hX hR.valid (fun _ hx => hR.lane_ne hX hx) hR.src 0)
      (hR.not_paired hX))
      (hR.not_paired hX))
    hR.ready hasm

/-- Normalization: recording a ready request gives a consistent extension that extends `X`,
completes a cta_group::1 operation, and strictly grows the size (`pairSize`). -/
theorem entry_counted (hX : Consistent L K A mem0 X) (hR : EntryReady L X cta r)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordEntry cta r)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L ∧
      (r.group = .one → ∀ i, Participates L r.own i → Covered L Y i) := by
  have hk : cta < L.grid := hR.src ▸ hR.valid.2.2.1
  refine ⟨X.recordEntry cta r, consistent_entry hX hR hasm, le_recordEntry,
    Execution.recordEntry_size X L cta hk r, fun hg i hi => ⟨[r.own], .inl ⟨cta, r, ?_, hg, rfl⟩,
      r.own, List.mem_singleton_self _, hi⟩⟩
  simp [Execution.recordEntry]

/-- The premises under which two recorded cta_group::2 requests can be paired now: the valid
pair, both records, no earlier pairing of either request, the readiness of the operation, and
its waiting participants, which are pending and have no outgoing allocator order edge. -/
structure PairingReady (L : Launch) (X : Execution) (q : WarpRequest × WarpRequest) : Prop where
  valid : PairValid L X q
  first : ∃ r ∈ X.tmemHistory q.1.cta, r.own = q.1 ∧ r.group = .two
  second : ∃ r ∈ X.tmemHistory q.2.cta, r.own = q.2 ∧ r.group = .two
  fresh : ∀ q' ∈ X.tmemPairing, q'.1.event L 0 ≠ q.1.event L 0 ∧ q'.2.event L 0 ≠ q.2.event L 0
  ready : CompletionReady L X [q.1, q.2]
  pending : ∀ j, (Participates L q.1 j ∨ Participates L q.2 j) → MustWait X j → ¬ Covered L X j
  last : ∀ j, (Participates L q.1 j ∨ Participates L q.2 j) → MustWait X j →
    ∀ cta' j', ¬ Precedes L X cta' j j'

/-- The returns of the participants of `q` that must wait. -/
def PairReturn (L : Launch) (X : Execution) (q : WarpRequest × WarpRequest)
    (n : Ref × Bool) : Prop :=
  ∃ j, n = (.thread j, true) ∧ (Participates L q.1 j ∨ Participates L q.2 j) ∧ MustWait X j

private theorem participates_pair {j : EvId} {w : WarpRequest} (hw : w ∈ [q.1, q.2])
    (hp : Participates L w j) : Participates L q.1 j ∨ Participates L q.2 j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact .inl hp
  · exact .inr hp

/-- A pairing changes the needs of no event, except the returns of its own waiting participants:
it completes only their operation. -/
theorem needs_recordPairing {j : EvId}
    (h : ¬ ((Participates L q.1 j ∨ Participates L q.2 j) ∧ MustWait X j)) :
    Needs L (X.recordPairing q) j = Needs L X j := by
  unfold Needs
  change (match X.get j with
    | none => []
    | some ev => KindNeeds L (X.recordPairing q) ev.kind j) = _
  cases X.get j with
  | none => rfl
  | some ev =>
    simp only
    cases ev.kind
    all_goals try rfl
    cases ‹TcKind›
    all_goals try rfl
    rename_i group dst request
    by_cases hm : MustWait X j
    · have hp : ¬ (Participates L q.1 j ∨ Participates L q.2 j) := fun hp => h ⟨hp, hm⟩
      have hcov : Covered L (X.recordPairing q) j ↔ Covered L X j := by
        constructor
        · rintro ⟨ws, hws, w, hw, hpw⟩
          rcases completed_recordPairing hws with hws | rfl
          · exact ⟨ws, hws, w, hw, hpw⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
            rcases hw with rfl | rfl
            · exact (hp (.inl hpw)).elim
            · exact (hp (.inr hpw)).elim
        · exact Covered.mono le_recordPairing
      have hfill : ∀ l : Fin 32, (fun (x : Ref) => ∃ q' ∈ (X.recordPairing q).tmemPairing,
          (Participates L q'.1 j ∧ x = .thread (q'.2.event L l)) ∨
            (Participates L q'.2 j ∧ x = .thread (q'.1.event L l))) =
          (fun (x : Ref) => ∃ q' ∈ X.tmemPairing,
          (Participates L q'.1 j ∧ x = .thread (q'.2.event L l)) ∨
            (Participates L q'.2 j ∧ x = .thread (q'.1.event L l))) := by
        intro l
        funext x
        apply propext
        constructor
        · rintro ⟨q', hq', hx⟩
          rcases List.mem_append.mp hq' with hq' | hq'
          · exact ⟨q', hq', hx⟩
          · rw [List.mem_singleton.mp hq'] at hx
            rcases hx with ⟨h1, -⟩ | ⟨h2, -⟩
            · exact (hp (.inl h1)).elim
            · exact (hp (.inr h2)).elim
        · rintro ⟨q', hq', hx⟩
          exact ⟨q', List.mem_append_left _ hq', hx⟩
      simp only [KindNeeds, resourceNeeds, hcov, hfill]
      rfl
    · have hm' : ¬ MustWait (X.recordPairing q) j := hm
      simp only [KindNeeds, resourceNeeds, needsIf, hm, hm', ↓reduceIte]
      rfl

/-- A `Waits` edge of the pairing is one of `X`, or a witness edge into a waiting return of its
operation. -/
theorem pairing_waits_cases {u v : Ref × Bool} (h : Waits L (X.recordPairing q) u v) :
    Waits L X u v ∨ (u.2 = false ∧ PairReturn L X q v) := by
  obtain ⟨u1,u2⟩ := u
  obtain ⟨v1,v2⟩ := v
  rcases h with h | h | h | h | h | h | h | h |
    ⟨hb,hb',j,rfl,hw⟩ | h | h | h | h | h | h
  · exact .inl (.inl h)
  · exact .inl (.inr (.inl h))
  · exact .inl (.inr (.inr (.inl h)))
  · exact .inl (.inr (.inr (.inr (.inl h))))
  · exact .inl (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))
  · by_cases hp : (Participates L q.1 j ∨ Participates L q.2 j) ∧ MustWait X j
    · exact .inr ⟨hb, j, by rw [hb'], hp.1, hp.2⟩
    · unfold Witness at hw
      rw [needs_recordPairing hp] at hw
      exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl ⟨hb, hb', j, rfl, hw⟩)))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl h))))))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl h)))))))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inl h))))))))))))))
  · exact .inl (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr h))))))))))))))

/-- Pairing adds edges only into terminal waiting returns without allocator order edges, which
are sinks: a sink frame for those returns. -/
theorem pairing_sinkFrame (hX : Consistent L K A mem0 X) (hR : PairingReady L X q) :
    SinkFrame.Base L K A X (X.recordPairing q) (PairReturn L X q) := by
  have sink : ∀ u v, PairReturn L X q u → ¬ Waits L (X.recordPairing q) u v := by
    intro u v hu hw
    obtain ⟨j, rfl, hp, hm⟩ := hu
    rcases pairing_waits_cases hw with hold | ⟨hb, _⟩
    · have hn := hR.pending j hp hm
      have hlast := pending_is_last hX hm hn
      have hord := hR.last j hp hm
      obtain ⟨pc, group, dst, action, hget, _⟩ := hm
      exact quiet_return_sink_of_effects hX.effectValidity hX.cluster hget rfl hlast
        hord v hold
    · cases hb
  exact {
    closed := ⟨fun _ => 0, fun u v h hu => (sink u v hu h).elim⟩
    cause := fun _ _ _ _ h => .single h
    observed := fun _ _ _ _ h => h
    object := fun _ _ _ _ _ _ h => objectOrder_recordPairing h
    objectSync := fun o ho u v _ _ h => by
      cases o with
      | tmem _ => exact ho.elim
      | mbar _ => exact h
      | ctaBar _ _ => exact h
      | cluster _ => exact h
    dep := fun u v _ hv h => by
      obtain ⟨e, b⟩ := u
      obtain ⟨f, b'⟩ := v
      rcases h with h | h | ⟨rfl, rfl, j, rfl, hw⟩ | h
      · exact .single (.inl h)
      · exact .single (.inr (.inl h))
      · have hp : ¬ ((Participates L q.1 j ∨ Participates L q.2 j) ∧ MustWait X j) :=
          fun hp => hv ⟨j, rfl, hp.1, hp.2⟩
        refine .single (.inr (.inr (.inl ⟨rfl, rfl, j, rfl, ?_⟩)))
        unfold Witness at hw ⊢
        rwa [needs_recordPairing hp] at hw
      · exact .single (.inr (.inr (.inr h)))
    issue := fun _ _ _ _ _ ⟨_, h, _⟩ => by cases congrArg Prod.snd h
    asyncSelf := fun m i p y hb => (hX.asyncObject m i p y hb).1
    asyncObserved := fun _ _ _ _ _ _ h => h
    initFence := hX.initFence
    get := fun _ _ => rfl }

/-- **A ready pairing of allocations publishes nothing**: every lane of an allocation must wait,
so a lane of a ready pair of allocations is pending, its thread's last event and without an
allocator order edge, and its return is a sink. -/
theorem PairingReady.quiet (hX : Consistent L K A mem0 X) (hR : PairingReady L X q) :
    PairingQuiet L X q := by
  intro cta r hr hown ⟨n, base, hac⟩ lane e
  have hreq : r.own.request = .alloc n := by
    rw [← ((hX.tmemPair.1 cta).1 r hr).2.1, hac]
    rfl
  obtain ⟨-, hv1, hv2, -, -, -, hcomp⟩ := hR.valid
  have halloc : (∃ m, q.1.request = .alloc m) ∧ ∃ m, q.2.request = .alloc m := by
    rcases hown with h | h <;> rw [h] at hcomp ⊢ <;> rw [hreq] at hcomp ⊢
    · refine ⟨⟨n, rfl⟩, ?_⟩
      cases h2 : q.2.request <;> simp_all [compatible]
    · refine ⟨?_, ⟨n, rfl⟩⟩
      cases h1 : q.1.request <;> simp_all [compatible]
  have quiet : ∀ {w : WarpRequest}, w.Valid L X .two → (∃ m, w.request = .alloc m) →
      (Participates L w (w.event L lane) → Participates L q.1 (w.event L lane) ∨
        Participates L q.2 (w.event L lane)) → ¬ baseCausality L X (w.event L lane) e := by
    intro w hv ⟨m, hm⟩ hp hhb
    have hget := hv.2.2.1 lane
    rw [hm] at hget
    have hmw : MustWait X (w.event L lane) := ⟨_, _, _, _, hget, trivial⟩
    have hpq := hp ⟨lane, rfl⟩
    have hlast := pending_is_last hX hmw (hR.pending _ hpq hmw)
    obtain ⟨v, hfirst, _⟩ := Relation.TransGen.head'_iff.mp (baseCausality_waits hhb)
    exact quiet_return_sink_of_effects hX.effectValidity hX.cluster hget rfl hlast
      (hR.last _ hpq hmw) v hfirst
  exact ⟨quiet hv1 halloc.1 .inl, quiet hv2 halloc.2 .inr⟩

/-- Pairing a ready pair keeps the execution consistent. -/
theorem consistent_pairing (hX : Consistent L K A mem0 X) (hR : PairingReady L X q)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordPairing q)) :
    Consistent L K A mem0 (X.recordPairing q) :=
  consistent_recordPairing hX
    ((pairing_sinkFrame hX hR).orderOk hX.orderOk fun cta' n h => hX.object (.tmem cta') n h)
    (hX.tmemPair.recordPairing hR.valid hR.first hR.second hR.fresh) hR.ready (hR.quiet hX) hasm

/-- Normalization: pairing a ready pair gives a consistent extension that extends `X`, covers
both requests' participants, and strictly grows the size (`pairSize`). -/
theorem pairing_counted (hX : Consistent L K A mem0 X) (hR : PairingReady L X q)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordPairing q)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L ∧
      ∀ i, (Participates L q.1 i ∨ Participates L q.2 i) → Covered L Y i := by
  refine ⟨X.recordPairing q, consistent_pairing hX hR hasm, le_recordPairing,
    Execution.recordPairing_size X L q, fun i hi => ⟨[q.1, q.2], .inr ⟨q, ?_, rfl⟩, ?_⟩⟩
  · simp [Execution.recordPairing]
  · rcases hi with hi | hi
    · exact ⟨q.1, by simp, hi⟩
    · exact ⟨q.2, by simp, hi⟩

/-! ## The owner warp's record for a thread's last event -/

/-- Lane `t` of the warp that holds thread `g`. -/
def warpThread (L : Launch) (g t : Nat) : Nat :=
  g / L.block * L.block + g % L.block / 32 * 32 + t

/-- The owner warp's request: each lane's index is its thread's last event. -/
def warpRequest (L : Launch) (X : Execution) (g pc : Nat) (dst : Option Loc)
    (request : Tmem.Request) : WarpRequest :=
  { cta := g / L.block, warp := g % L.block / 32,
    indices := fun t => (X.tr (warpThread L g t.val)).length - 1,
    pc := pc, dst := dst, request := request }

/-- The owner warp's cta_group::1 record for the operation of thread `g`. -/
def ownerRecord (L : Launch) (X : Execution) (g pc : Nat) (dst : Option Loc)
    (action : Tmem.Action) : Requests :=
  ⟨warpRequest L X g pc dst action.request, .one, action⟩

/-- The lane `g % L.block % 32` of the warp of `g` is `g` itself. -/
theorem warpThread_self (L : Launch) (g : Nat) :
    warpThread L g (g % L.block % 32) = g := by
  unfold warpThread
  have h2 := Nat.div_add_mod g L.block
  have h3 := Nat.div_add_mod (g % L.block) 32
  rw [Nat.mul_comm (g / L.block) L.block, Nat.mul_comm (g % L.block / 32) 32]
  omega

/-- Normalization for a thread's last event. When all 32 lanes of the thread's warp sit at the
same cta_group::1 operation, unrecorded, the owner warp's record of it is ready. Recording it
covers the thread's own event and strictly grows the execution (`pairSize`). -/
theorem warp_entry_counted (hX : Consistent L K A mem0 X) {g pc : Nat} {dst : Option Loc}
    {action : Tmem.Action} (hg : g < L.threads) (hb32 : L.block % 32 = 0)
    (hops : ∀ t : Fin 32, X.get (warpThread L g t.val, (X.tr (warpThread L g t.val)).length - 1) =
      some ⟨pc, .tc (.resource .one dst action.request)⟩)
    (hk : ∃ k, ∀ t : Fin 32,
      X.TcK (warpThread L g t.val, (X.tr (warpThread L g t.val)).length - 1) k)
    (hfree : ∀ t : Fin 32,
      ¬ Covered L X (warpThread L g t.val, (X.tr (warpThread L g t.val)).length - 1))
    (hready : CompletionReady L X [(ownerRecord L X g pc dst action).own])
    (hrun : runRequests {} (X.tmemHistory (g / L.block) ++ [ownerRecord L X g pc dst action]) ≠
      .blocked)
    (hasm : ∀ a ∈ A, a.wf L mem0
      (X.recordEntry (g / L.block) (ownerRecord L X g pc dst action))) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ Covered L Y (g, (X.tr g).length - 1) ∧
      X.size L < Y.size L := by
  have hblk : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h | h
    · have hg' := hg
      simp [Launch.threads, h] at hg'
    · exact h
  have hcta : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hblk).2 hg
  have hwarp : (g % L.block / 32 + 1) * 32 ≤ L.block := by
    have hlt := Nat.mod_lt g hblk
    generalize g % L.block = a at hlt ⊢
    omega
  have hvalid : (ownerRecord L X g pc dst action).Valid L X :=
    ⟨hX.cluster.1, rfl, hcta, hwarp, hops, hk⟩
  have hfresh : ∀ x ∈ X.tmemHistory (g / L.block), x.own ≠ (ownerRecord L X g pc dst action).own :=
    by
    intro x hx hxo
    have hxv := ((hX.tmemPair.1 _).1 x hx).2.2
    have hgrp : x.group = .one := by
      have h1 := hxv.2.2.1 0
      rw [hxo] at h1
      have h2 := hvalid.2.2.2.2.1 0
      rw [h1] at h2
      simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at h2
      exact h2.2.1
    exact hfree 0 ⟨[x.own], .inl ⟨_, x, hx, hgrp, rfl⟩, x.own, List.mem_singleton_self _, 0,
      by rw [hxo]; rfl⟩
  have hR : EntryReady L X (g / L.block) (ownerRecord L X g pc dst action) :=
    ⟨hvalid, fun _ => hready, hfresh, rfl, hrun⟩
  obtain ⟨Y, hY, hle, hsize, hcov⟩ := entry_counted hX hR hasm
  have hlane : (ownerRecord L X g pc dst action).own.event L
      ⟨g % L.block % 32, Nat.mod_lt _ (by decide)⟩ = (g, (X.tr g).length - 1) := by
    show (warpThread L g (g % L.block % 32), (X.tr (warpThread L g (g % L.block % 32))).length - 1)
      = (g, (X.tr g).length - 1)
    rw [warpThread_self]
  exact ⟨Y, hY, hle, hcov rfl _ ⟨_, hlane⟩, hsize⟩

end

end PTX.Step
