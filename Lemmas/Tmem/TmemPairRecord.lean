-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairCompletionGrowth
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Order.VisibilityFrame
public import Lemmas.Tcgen05.TcMmaReadMono
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Tmem.TmemPairOrder
public import Lemmas.Step.SetMaxNReg
public import Lemmas.Order.WaitingClosure
public import Lemmas.TensorStore.TensorReduce
public import Lemmas.Tcgen05.TcFence
public import Lemmas.Snoc.Snoc
public import Lemmas.Snoc.QuietReturnSink

@[expose] public section

/-! Recording allocator operations. `Execution.recordEntry` appends a record to a CTA's
allocator history: for a cta_group::1 request this completes its operation, whose participants
already wait for each other as one warp collective, so the record adds no new waiting
dependency. `Execution.recordPairing` pairs two recorded cta_group::2 requests and completes their
operation; its waiting edges are handled by the progress tool (`Lemmas/Step/TmemPair.lean`). -/

namespace PTX
noncomputable section

namespace Tmem.Pair
variable {L : Launch} {X : Execution} {cta : Nat} {r : Requests}
  {q : WarpRequest × WarpRequest}

theorem le_recordEntry : X.le (X.recordEntry cta r) := by
  refine ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, AsyncCopy.Extends.refl _,
    (Execution.le_refl X).2.2.2.1, (Execution.le_refl X).2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.2.2.1, ⟨fun k => ?_, List.prefix_refl _⟩,
    fun _ _ _ _ _ _ => rfl, fun _ => Finset.Subset.refl _⟩
  by_cases hk : k = cta
  · simp [Execution.recordEntry, hk]
  · simp [Execution.recordEntry, hk]

theorem le_recordPairing : X.le (X.recordPairing q) :=
  ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, AsyncCopy.Extends.refl _,
    (Execution.le_refl X).2.2.2.1, (Execution.le_refl X).2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.1, (Execution.le_refl X).2.2.2.2.2.2.2.2.1,
    (Execution.le_refl X).2.2.2.2.2.2.2.2.2.1,
    ⟨fun _ => List.prefix_refl _, List.prefix_append _ _⟩,
    fun _ _ _ _ _ _ => rfl, fun _ => Finset.Subset.refl _⟩

/-- A record completes at most its own cta_group::1 operation. -/
theorem completed_recordEntry {ws : List WarpRequest} (h : Completed (X.recordEntry cta r) ws) :
    Completed X ws ∨ (r.group = .one ∧ ws = [r.own]) := by
  rcases h with ⟨k, x, hx, hg, rfl⟩ | ⟨q', hq, rfl⟩
  · rcases mem_recordEntry hx with hx | ⟨-, rfl⟩
    · exact .inl (.inl ⟨k, x, hx, hg, rfl⟩)
    · exact .inr ⟨hg, rfl⟩
  · exact .inl (.inr ⟨q', hq, rfl⟩)

/-- A pairing completes exactly its own operation. -/
theorem completed_recordPairing {ws : List WarpRequest} (h : Completed (X.recordPairing q) ws) :
    Completed X ws ∨ ws = [q.1, q.2] := by
  rcases h with ⟨k, x, hx, hg, rfl⟩ | ⟨q', hq, rfl⟩
  · exact .inl (.inl ⟨k, x, hx, hg, rfl⟩)
  · rcases List.mem_append.mp hq with hq | hq
    · exact .inl (.inr ⟨q', hq, rfl⟩)
    · rw [List.mem_singleton.mp hq]
      exact .inr rfl

/-- Recording leaves the order of every object of `DependencyOk` unchanged. -/
theorem objectOrder_recordEntry {o : OrderObject} (ho : o.Enabling) {u v : AsyncCopy.Ref × Bool}
    (h : ObjectOrder L (X.recordEntry cta r) o u v) : ObjectOrder L X o u v := by
  cases o with
  | tmem _ => exact ho.elim
  | mbar _ => exact h
  | ctaBar _ _ => exact h
  | cluster _ => exact h

/-- A pairing leaves the order of every object unchanged: the allocator orders are the
histories. -/
theorem objectOrder_recordPairing {o : OrderObject} {u v : AsyncCopy.Ref × Bool}
    (h : ObjectOrder L (X.recordPairing q) o u v) : ObjectOrder L X o u v := by
  cases o with
  | tmem _ => exact h
  | mbar _ => exact h
  | ctaBar _ _ => exact h
  | cluster _ => exact h

/-- The history of `k` after recording is the old history, followed by `r` for `cta`. -/
theorem recordEntry_history (k : Nat) :
    (X.recordEntry cta r).tmemHistory k =
      if k = cta then X.tmemHistory k ++ [r] else X.tmemHistory k :=
  rfl

/-- **Recording keeps the allocation result rule** when lane 0 of the request is its thread's
last event: its address store is not yet performed. -/
theorem ResultOk.recordEntry (hx : ResultOk L X)
    (hlast : (r.own.event L 0).2 + 1 = (X.tr (r.own.event L 0).1).length) :
    ResultOk L (X.recordEntry cta r) := by
  intro i pc group dst n hi cta' x base hx' hwi hwa pc' a bs hs
  change X.get i = _ at hi
  change X.get _ = _ at hs
  rcases mem_recordEntry hx' with hx' | ⟨-, rfl⟩
  · exact hx i pc group dst n hi cta' x base hx' hwi hwa pc' a bs hs
  · have h1 := len_of_get hs
    rw [← hwi] at h1
    simp only at h1
    omega

/-- A pairing keeps the allocation result rule: it depends on the histories only. -/
theorem ResultOk.recordPairing (hx : ResultOk L X) : ResultOk L (X.recordPairing q) := hx

/-- Recording keeps every old allocator order edge. -/
theorem precedes_recordEntry {cta' : Nat} {i j : EvId} (h : Precedes L X cta' i j) :
    Precedes L (X.recordEntry cta r) cta' i j := by
  obtain ⟨k, l, x, y, hx, hy, hkl, hpx, hpy⟩ := h
  refine ⟨k, l, x, y, ?_, ?_, hkl, hpx, hpy⟩ <;> rw [recordEntry_history] <;>
    split_ifs <;> first
      | assumption
      | rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ‹_›).1]

/-- Recording `r` adds to an allocator order only edges from lanes of earlier records of its
CTA into lanes of `r`. -/
theorem precedes_recordEntry_cases {cta' : Nat} {i j : EvId}
    (h : Precedes L (X.recordEntry cta r) cta' i j) :
    Precedes L X cta' i j ∨ (cta' = cta ∧ Participates L r.own j ∧
      ∃ x ∈ X.tmemHistory cta, Participates L x.own i) := by
  obtain ⟨k, l, x, y, hx, hy, hkl, hpx, hpy⟩ := h
  rw [recordEntry_history] at hx hy
  split_ifs at hx hy with hk
  · subst hk
    have hkx := (List.getElem?_eq_some_iff.mp hx).1
    have hly := (List.getElem?_eq_some_iff.mp hy).1
    simp only [List.length_append, List.length_singleton] at hkx hly
    have hk' : k < (X.tmemHistory cta').length := by omega
    rw [List.getElem?_append_left hk'] at hx
    by_cases hl : l < (X.tmemHistory cta').length
    · rw [List.getElem?_append_left hl] at hy
      exact .inl ⟨k, l, x, y, hx, hy, hkl, hpx, hpy⟩
    · have hl' : l = (X.tmemHistory cta').length := by omega
      subst hl'
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hy
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
      subst hy
      exact .inr ⟨rfl, hpy, x, List.mem_of_getElem? hx, hpx⟩
  · exact .inl ⟨k, l, x, y, hx, hy, hkl, hpx, hpy⟩

private theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- An event that is no lane of `r` is performed after the record exactly when before it. -/
theorem performed_recordEntry_iff {e : EvId} (hne : ¬ Participates L r.own e) :
    Performed L (X.recordEntry cta r) e ↔ Performed L X e := by
  constructor
  · rintro ⟨k, x, hx, hp⟩
    rcases mem_recordEntry hx with hx | ⟨-, rfl⟩
    · exact ⟨k, x, hx, hp⟩
    · exact (hne hp).elim
  · rintro ⟨k, x, hx, hp⟩
    exact ⟨k, x, mem_recordEntry_old hx, hp⟩

/-- An event that is no lane of `r` is covered after the record exactly when before it. -/
theorem covered_recordEntry_iff {e : EvId} (hne : ¬ Participates L r.own e) :
    Covered L (X.recordEntry cta r) e ↔ Covered L X e := by
  constructor
  · rintro ⟨ws, hws, w, hw, hp⟩
    rcases completed_recordEntry hws with hws | ⟨-, rfl⟩
    · exact ⟨ws, hws, w, hw, hp⟩
    · rw [List.mem_singleton.mp hw] at hp
      exact (hne hp).elim
  · exact Covered.mono le_recordEntry

/-- For an event that is no lane of `r`, a release that its allocation reuses is the same release
before and after the record: the appended record is not its allocation and lies after it. -/
theorem reuseRelease_recordEntry_iff {e : EvId} (hne : ¬ Participates L r.own e) (j : Nat) :
    ReuseRelease L (X.recordEntry cta r) e j ↔ ReuseRelease L X e j := by
  unfold ReuseRelease
  rw [recordEntry_history]
  split_ifs with hc
  swap
  · rfl
  set h := X.tmemHistory (e.1 / L.block)
  have hl : ∀ {k}, k < h.length → (h ++ [r])[k]? = h[k]? := fun hk => List.getElem?_append_left hk
  constructor
  · rintro ⟨i, x, d, n, base, b', n', hi, hp, ha, hj, hji, hd, col, c1, c2, c3, c4, hall⟩
    have hil : i < h.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_append, List.length_singleton] at this
      by_contra hge
      have hieq : i = h.length := by omega
      subst hieq
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact hne hp
    refine ⟨i, x, d, n, base, b', n', by rwa [hl hil] at hi, hp, ha,
      by rwa [hl (by omega)] at hj, hji, hd, col, c1, c2, c3, c4, fun k d' b'' n'' hjk hki hk =>
        hall k d' b'' n'' hjk hki (by rwa [hl (by omega)])⟩
  · rintro ⟨i, x, d, n, base, b', n', hi, hp, ha, hj, hji, hd, col, c1, c2, c3, c4, hall⟩
    have hil : i < h.length := (List.getElem?_eq_some_iff.mp hi).1
    refine ⟨i, x, d, n, base, b', n', by rwa [hl hil], hp, ha, by rwa [hl (by omega)], hji, hd,
      col, c1, c2, c3, c4, fun k d' b'' n'' hjk hki hk =>
        hall k d' b'' n'' hjk hki (by rwa [hl (by omega)] at hk)⟩

/-- **Recording `r` changes the needs of no event that is no lane of `r`.** -/
theorem needs_recordEntry {e : EvId} (hne : ¬ Participates L r.own e) :
    Needs L (X.recordEntry cta r) e = Needs L X e := by
  unfold Needs
  change (match X.get e with
    | none => []
    | some ev => KindNeeds L (X.recordEntry cta r) ev.kind e) = _
  cases X.get e with
  | none => rfl
  | some ev =>
    simp only
    cases ev.kind
    all_goals try rfl
    cases ‹TcKind›
    all_goals try rfl
    rename_i group dst request
    have hreuse : ((List.range ((X.recordEntry cta r).tmemHistory (e.1 / L.block)).length).flatMap
        fun j => needsIf (ReuseRelease L (X.recordEntry cta r) e j)
          ((List.finRange 32).map fun l => Need.node fun x =>
            ∃ d, ((X.recordEntry cta r).tmemHistory (e.1 / L.block))[j]? = some d ∧
              x = .thread (d.own.event L l))) =
        (List.range (X.tmemHistory (e.1 / L.block)).length).flatMap
        fun j => needsIf (ReuseRelease L X e j)
          ((List.finRange 32).map fun l => Need.node fun x =>
            ∃ d, (X.tmemHistory (e.1 / L.block))[j]? = some d ∧
              x = .thread (d.own.event L l)) := by
      have hif : ∀ j (a b : List Need), a = b →
          needsIf (ReuseRelease L (X.recordEntry cta r) e j) a = needsIf (ReuseRelease L X e j) b :=
        fun j a b hab => @if_congr _ _ _ (Classical.propDecidable _) (Classical.propDecidable _) _ _
          _ _ (reuseRelease_recordEntry_iff hne j) hab rfl
      rw [recordEntry_history]
      split_ifs with hc
      swap
      · exact flatMap_congr_mem fun j _ => hif j _ _ rfl
      have hn : ¬ ReuseRelease L X e (X.tmemHistory (e.1 / L.block)).length := by
        rintro ⟨i, x, d, n, base, b', n', hi, -, -, hj, -⟩
        simp at hj
      have hlast : needsIf (ReuseRelease L (X.recordEntry cta r) e
          (X.tmemHistory (e.1 / L.block)).length) ((List.finRange 32).map fun l => Need.node
            fun x => ∃ d, (X.tmemHistory (e.1 / L.block) ++ [r])[
              (X.tmemHistory (e.1 / L.block)).length]? = some d ∧
              x = .thread (d.own.event L l)) = [] := by
        unfold needsIf
        split_ifs with h
        · exact (hn ((reuseRelease_recordEntry_iff hne _).mp h)).elim
        · rfl
      rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
      simp only [List.flatMap_cons, List.flatMap_nil, hlast, List.append_nil]
      refine flatMap_congr_mem fun j hj => hif j _ _ ?_
      have hj' : j < (X.tmemHistory (e.1 / L.block)).length := List.mem_range.mp hj
      simp only [List.getElem?_append_left hj']
    simp only [KindNeeds, resourceNeeds, performed_recordEntry_iff hne,
      covered_recordEntry_iff hne, hreuse]
    rfl

/-- The return of a lane of `r`: a node of the sink frame of the record. -/
def EntryReturn (L : Launch) (r : Requests) (n : AsyncCopy.Ref × Bool) : Prop :=
  ∃ l, n = (.thread (r.own.event L l), true)

/-- A node outside `EntryReturn` is no return of a lane of `r`. -/
theorem not_participates_of_not_entryReturn {j : EvId}
    (h : ¬ EntryReturn L r (.thread j, true)) : ¬ Participates L r.own j :=
  fun ⟨l, hl⟩ => h ⟨l, by rw [hl]⟩

/-- A `Waits` edge of the record from a return of a lane of `r` is one of `X`: the record is the
last of its history, so no allocator order leaves its lanes. -/
theorem waits_recordEntry_from_lane
    (hfresh : ∀ x ∈ X.tmemHistory cta, ∀ l l' : Fin 32, x.own.event L l ≠ r.own.event L l')
    {l : Fin 32} {v : AsyncCopy.Ref × Bool}
    (h : Waits L (X.recordEntry cta r) (.thread (r.own.event L l), true) v) :
    Waits L X (.thread (r.own.event L l), true) v := by
  obtain ⟨f, b'⟩ := v
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h |
    ⟨hb, hb', i, j, he, hf, cta', hp⟩ | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))
  · exact absurd h.1 (by simp)
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h))))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))
  · rcases precedes_recordEntry_cases hp with hp | ⟨rfl, -, x, hx, l', hl'⟩
    · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
        (.inl ⟨hb, hb', i, j, he, hf, cta', hp⟩))))))))))))
    · cases he
      exact (hfresh x hx l' l hl').elim
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inl h)))))))))))))
  · exact absurd h.1 (by simp)

/-- A record adds no edge except to the allocator orders and the witness edges into the returns
of its lanes, which are sinks: each lane is its thread's last event and has no allocator order
edge. -/
theorem sinkFrame_recordEntry {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hv : r.Valid L X)
    (hfresh : ∀ x ∈ X.tmemHistory cta, ∀ l l' : Fin 32, x.own.event L l ≠ r.own.event L l')
    (hlast : ∀ l : Fin 32, (r.own.event L l).2 + 1 = (X.tr (r.own.event L l).1).length)
    (hord : ∀ (l : Fin 32) cta' j, ¬ Precedes L X cta' (r.own.event L l) j) :
    SinkFrame.Base L K A X (X.recordEntry cta r) (EntryReturn L r) := by
  have hsink : ∀ u v, EntryReturn L r u → ¬ Waits L (X.recordEntry cta r) u v := by
    rintro u v ⟨l, rfl⟩ h
    exact quiet_return_sink_of_effects hX.effectValidity hX.cluster (hv.2.2.2.2.1 l) rfl
      (hlast l) (hord l) v (waits_recordEntry_from_lane hfresh h)
  exact {
    closed := ⟨fun _ => 0, fun u v h hu => (hsink u v hu h).elim⟩
    cause := fun _ _ _ _ h => .single h
    observed := fun _ _ _ _ h => h
    object := fun _ ho _ _ _ _ h => objectOrder_recordEntry ho h
    objectSync := fun o ho u v _ _ h => by
      cases o with
      | tmem _ => exact ho.elim
      | mbar _ => exact h
      | ctaBar _ _ => exact h
      | cluster _ => exact h
    dep := fun u v _ hv' h => by
      obtain ⟨e, b⟩ := u
      obtain ⟨f, b'⟩ := v
      rcases h with h | h | ⟨rfl, rfl, j, rfl, hw⟩ | h
      · exact .single (.inl h)
      · exact .single (.inr (.inl h))
      · have hne := not_participates_of_not_entryReturn hv'
        refine .single (.inr (.inr (.inl ⟨rfl, rfl, j, rfl, ?_⟩)))
        unfold Witness at hw ⊢
        rwa [needs_recordEntry hne] at hw
      · exact .single (.inr (.inr (.inr h)))
    issue := fun _ _ _ _ _ ⟨_, h⟩ => by cases congrArg Prod.snd h
    asyncSelf := fun m i p y hb => (hX.asyncObject m i p y hb).1
    asyncObserved := fun _ _ _ _ _ _ h => h
    initFence := hX.initFence
    get := fun _ _ => rfl }

/-- `r` can be performed after every record of CTA `cta`'s history: no lane of `r` is, or
causally precedes, a lane of a record. This is the premise under which appending `r` keeps
OBJ-TMEM-ORDER (`objectCoherent_recordEntry`). -/
def AfterHistory (L : Launch) (X : Execution) (cta : Nat) (r : Requests) : Prop :=
  ∀ x ∈ X.tmemHistory cta, ∀ i j, Participates L x.own i → Participates L r.own j →
    ¬ Relation.ReflTransGen (stageCausality L X) (.thread j, true) (.thread i, true)

/-- Causality together with the order of the allocator of CTA `cta`: the relation whose cycles
MEM-OBJECT-ORDER-CAUSALITY excludes for that object. -/
def TmemWith (L : Launch) (X : Execution) (cta : Nat) :
    AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop :=
  fun a c => stageCausality L X a c ∨ SyncObjectOrder L X (.tmem cta) a c

/-- OBJ-TMEM-ORDER for an appended record: the allocator orders stay coherent with
causality when `r` can be performed after every record of its CTA's history. -/
theorem objectCoherent_recordEntry (hX : ObjectCoherent L X) (hfresh : AfterHistory L X cta r)
    (cta' : Nat) :
    ∀ n, ¬ Relation.TransGen (TmemWith L (X.recordEntry cta r) cta') n n := by
  let Y := X.recordEntry cta r
  -- New edges: from an old lane of the CTA's history into a lane of `r`.
  let New : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop := fun u t =>
    ∃ i j, u = (.thread i, true) ∧ t = (.thread j, true) ∧ cta' = cta ∧
      Participates L r.own j ∧ ∃ x ∈ X.tmemHistory cta, Participates L x.own i
  have edge : ∀ a c, TmemWith L Y cta' a c →
      TmemWith L X cta' a c ∨ New a c := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ (h | ⟨rfl, rfl, i, j, rfl, rfl, hp⟩)
    · exact .inl (.inl h)
    · rcases precedes_recordEntry_cases hp with hp | ⟨hk, hr, x, hx, hpx⟩
      · exact .inl (.inr ⟨rfl, rfl, i, j, rfl, rfl, hp⟩)
      · exact .inr ⟨i, j, rfl, rfl, hk, hr, x, hx, hpx⟩
  have old : ∀ a c, TmemWith L X cta' a c → TmemWith L Y cta' a c := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ (h | ⟨rfl, rfl, i, j, rfl, rfl, hp⟩)
    · exact .inl h
    · exact .inr ⟨rfl, rfl, i, j, rfl, rfl, precedes_recordEntry hp⟩
  -- From a lane of `r`, every path is causal and reaches no old lane of the CTA's history.
  have stay : ∀ j c, Participates L r.own j → cta' = cta →
      Relation.ReflTransGen (TmemWith L Y cta') (.thread j, true) c →
      Relation.ReflTransGen (stageCausality L X) (.thread j, true) c ∧
        ∀ i, c = (.thread i, true) → ∀ x ∈ X.tmemHistory cta, ¬ Participates L x.own i := by
    intro j c hj hk hpath
    induction hpath with
    | refl =>
      refine ⟨.refl, fun i hi x hx hpx => ?_⟩
      cases hi
      exact hfresh x hx j j hpx hj .refl
    | @tail b c _ hbc ih =>
      obtain ⟨hcause, hnot⟩ := ih
      obtain ⟨b1, b2⟩ := b
      obtain ⟨c1, c2⟩ := c
      rcases edge _ _ hbc with (hbc | ⟨hb, hb', i, i', rfl, rfl, hp⟩) |
          ⟨i, i', hbi, -, -, -, x, hx, hpx⟩
      · refine ⟨hcause.tail hbc, fun i hi x hx hpx => ?_⟩
        cases hi
        exact hfresh x hx i j hpx hj (hcause.tail hbc)
      · obtain ⟨k, l, x, y, hx, -, -, hpx, -⟩ := hp
        subst hk hb
        exact (hnot i rfl x (List.mem_of_getElem? hx) hpx).elim
      · exact (hnot i hbi x hx hpx).elim
  -- A path of `Y` is a path of `X` or passes a new edge.
  have split : ∀ a c, Relation.TransGen (TmemWith L Y cta') a c →
      Relation.TransGen (TmemWith L X cta') a c ∨
        ∃ u t, New u t ∧ Relation.ReflTransGen (TmemWith L Y cta') a u ∧
          Relation.ReflTransGen (TmemWith L Y cta') t c := by
    intro a c h
    induction h with
    | single h =>
      rcases edge _ _ h with h | h
      · exact .inl (.single h)
      · exact .inr ⟨_, _, h, .refl, .refl⟩
    | tail _ hbc ih =>
      rcases ih with ih | ⟨u, t, hn, hau, htb⟩
      · rcases edge _ _ hbc with h | h
        · exact .inl (ih.tail h)
        · exact .inr ⟨_, _, h, (Relation.TransGen.mono old _ _ ih).to_reflTransGen, .refl⟩
      · exact .inr ⟨u, t, hn, hau, htb.tail hbc⟩
  intro n hn
  rcases split n n hn with h | ⟨u, t, ⟨i, j, rfl, rfl, hk, hr, x, hx, hpx⟩, hnu, htn⟩
  · exact hX _ n h
  · exact (stay j _ hr hk (htn.trans hnu)).2 i rfl x hx hpx

/-- Recording a request that can be performed after its CTA's history keeps the
execution-order axioms, given a base frame for the other relations. -/
theorem orderOk_recordEntry {K : Kernel} {A : List Assumption} {mem0 : Mem0} {S}
    (hX : Consistent L K A mem0 X) (hafter : AfterHistory L X cta r)
    (hf : SinkFrame.Base L K A X (X.recordEntry cta r) S) :
    OrderOk L K A (X.recordEntry cta r) :=
  hf.orderOk hX.orderOk (fun cta' => objectCoherent_recordEntry hX.object hafter cta')

/-- A record that covers no Tensor Memory cell and is in no pairing adds no read evidence: old
loads keep their read constraints. -/
theorem readOk_recordEntry {A : List Assumption} (hr : TcMma.ReadOk L A X)
    (hte : AsyncCopy.TcEffectsOk X)
    (hnc : ∀ owner e col, ¬ Covers L (X.recordEntry cta r) r owner e col)
    (hnp : ∀ q ∈ X.tmemPairing, q.1 ≠ r.own ∧ q.2 ≠ r.own) :
    TcMma.ReadOk L A (X.recordEntry cta r) := by
  refine (TcMma.ReadPreserved.readOk ⟨le_recordEntry, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ h => h, fun k r' hr' => ?_, fun _ => Iff.rfl, fun _ hq => .inl hq⟩ hr hte) ?_
  · rcases mem_recordEntry hr' with hr' | ⟨-, rfl⟩
    · exact .inl hr'
    · exact .inr ⟨hnc, hnp⟩
  · intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
    have := len_of_get (X := X) hl
    omega

/-- No lane event of a pairing's requests happens before an event, if one of them is the request
of an allocation record. -/
def PairingQuiet (L : Launch) (X : Execution) (q : WarpRequest × WarpRequest) : Prop :=
  ∀ cta r, r ∈ X.tmemHistory cta → (q.1 = r.own ∨ q.2 = r.own) →
    (∃ n base, r.action = .alloc n base) →
    ∀ lane e, ¬ baseCausality L X (q.1.event L lane) e ∧ ¬ baseCausality L X (q.2.event L lane) e

/-- A pairing adds no read evidence: the allocations it covers are recorded already, and a
pairing of allocations publishes nothing to old events (`PairingQuiet`). -/
theorem readOk_recordPairing {A : List Assumption} (hr : TcMma.ReadOk L A X)
    (hte : AsyncCopy.TcEffectsOk X) (hq : PairingQuiet L X q) :
    TcMma.ReadOk L A (X.recordPairing q) := by
  refine (TcMma.ReadPreserved.readOk ⟨le_recordPairing, fun _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ h => h, fun _ _ hr' => .inl hr', fun _ => Iff.rfl, fun q' hq' => ?_⟩ hr hte) ?_
  · rcases List.mem_append.mp hq' with hq' | hq'
    · exact .inl hq'
    · rw [List.mem_singleton.mp hq']
      exact .inr hq
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  have := len_of_get (X := X) hl
  omega

/-- Resource bookkeeping leaves byte visibility unchanged. -/
theorem modelCausality_recordEntry {l : Loc} {a b : AsyncCopy.Ref} :
    modelCausality L (X.recordEntry cta r) l a b ↔ modelCausality L X l a b := by
  cases a <;> cases b <;> first
    | rfl
    | exact and_congr_right fun _ =>
        AsyncChain.congr (L := L) (X := X.recordEntry cta r) (Y := X) (fun _ _ => Iff.rfl)
          (fun _ p => by cases p <;> rfl)

theorem modelCausality_recordPairing {l : Loc} {a b : AsyncCopy.Ref} :
    modelCausality L (X.recordPairing q) l a b ↔ modelCausality L X l a b := by
  cases a <;> cases b <;> first
    | rfl
    | exact and_congr_right fun _ =>
        AsyncChain.congr (L := L) (X := X.recordPairing q) (Y := X) (fun _ _ => Iff.rfl)
          (fun _ p => by cases p <;> rfl)

/-- Recording a valid record of CTA `cta` keeps the provenance and replay of every history. -/
theorem HistoriesOk.recordEntry (hh : HistoriesOk L X) (hv : r.Valid L X)
    (hkey : r.own.cta = cta) (hrun : runRequests {} (X.tmemHistory cta ++ [r]) ≠ .blocked) :
    HistoriesOk L (X.recordEntry cta r) := by
  obtain ⟨hhist, hpair, hdist⟩ := hh
  refine ⟨fun k => ?_, fun q' hq => ?_, hdist⟩
  · obtain ⟨hval, hk, hrn⟩ := hhist k
    rw [recordEntry_history]
    split_ifs with hkk
    · subst hkk
      refine ⟨fun x hx => ?_, fun x hx => ?_, hrun⟩
      · rcases List.mem_append.mp hx with hx | hx
        · exact (hval x hx).mono le_recordEntry
        · rw [List.mem_singleton.mp hx]; exact hv.mono le_recordEntry
      · rcases List.mem_append.mp hx with hx | hx
        · exact hk x hx
        · rw [List.mem_singleton.mp hx]; exact hkey
    · exact ⟨fun x hx => (hval x hx).mono le_recordEntry, hk, hrn⟩
  · obtain ⟨hpv, ⟨a, ha, ha'⟩, b, hb, hb'⟩ := hpair q' hq
    exact ⟨hpv.mono le_recordEntry, ⟨a, mem_recordEntry_old ha, ha'⟩, b,
      mem_recordEntry_old hb, hb'⟩

/-- Pairing two recorded cta_group::2 requests, neither already paired, keeps the provenance of
every history and pairing. -/
theorem HistoriesOk.recordPairing (hh : HistoriesOk L X) (hq : PairValid L X q)
    (h1 : ∃ r ∈ X.tmemHistory q.1.cta, r.own = q.1 ∧ r.group = .two)
    (h2 : ∃ r ∈ X.tmemHistory q.2.cta, r.own = q.2 ∧ r.group = .two)
    (hfresh : ∀ q' ∈ X.tmemPairing, q'.1.event L 0 ≠ q.1.event L 0 ∧
      q'.2.event L 0 ≠ q.2.event L 0) :
    HistoriesOk L (X.recordPairing q) := by
  obtain ⟨hhist, hpair, hdist⟩ := hh
  refine ⟨fun k => ?_, fun q' hq' => ?_, ?_⟩
  · obtain ⟨hval, hk, hrn⟩ := hhist k
    exact ⟨fun x hx => (hval x hx).mono le_recordPairing, hk, hrn⟩
  · rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨hpv, ha, hb⟩ := hpair q' hq'
      exact ⟨hpv.mono le_recordPairing, ha, hb⟩
    · rw [List.mem_singleton.mp hq']
      exact ⟨hq.mono le_recordPairing, h1, h2⟩
  · exact List.pairwise_append.mpr ⟨hdist, List.pairwise_singleton _ _,
      fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact hfresh a ha⟩

/-- Every returned allocation-management event is ready (`DependencyOk.ready`). -/
theorem _root_.PTX.Consistent.tmemPairBlocking {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) : Blocking L X := by
  intro i pc group dst request he hl
  refine hX.dependency.ready i ?_
  unfold Returned
  rw [he]
  exact hl

/-- An allocation-management event that is its thread's last event has not returned. -/
theorem not_returned_of_last {i : EvId} {pc : Nat} {group : CtaGroup} {dst : Option Loc}
    {request : Request} (he : X.get i = some ⟨pc, .tc (.resource group dst request)⟩)
    (hl : i.2 + 1 = (X.tr i.1).length) : ¬ Returned X i := by
  unfold Returned
  rw [he]
  simp only [Kind.resume, TcKind.resume]
  omega

/-- Recording a valid record keeps an execution consistent, provided it can be performed after
its CTA's history (`AfterHistory`), its lanes are their threads' last events, in no record of the
history and without an allocator order edge, the history replay can perform it, the result rule
still holds afterwards and, for a cta_group::1 record, its operation is ready. -/
theorem consistent_recordEntry {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hv : r.Valid L X)
    (hafter : AfterHistory L X cta r) (hkey : r.own.cta = cta)
    (hfresh : ∀ x ∈ X.tmemHistory cta, ∀ l l' : Fin 32, x.own.event L l ≠ r.own.event L l')
    (hlast : ∀ l : Fin 32, (r.own.event L l).2 + 1 = (X.tr (r.own.event L l).1).length)
    (hord : ∀ (l : Fin 32) cta' j, ¬ Precedes L X cta' (r.own.event L l) j)
    (hrun : runRequests {} (X.tmemHistory cta ++ [r]) ≠ .blocked)
    (hres : ResultOk L (X.recordEntry cta r))
    (hread : TcMma.ReadOk L A (X.recordEntry cta r))
    (hready : r.group = .one → CompletionReady L X [r.own])
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordEntry cta r)) :
    Consistent L K A mem0 (X.recordEntry cta r) := by
  have horder := orderOk_recordEntry hX hafter (sinkFrame_recordEntry hX hv hfresh hlast hord)
  exact {
    thr := hX.thr
    outside := hX.outside
    rf := hX.rf
    ctaBar := hX.ctaBar
    cluster := hX.cluster
    dependency := {
      ready := fun e hr => by
        have hne : ¬ Participates L r.own e := by
          rintro ⟨l, rfl⟩
          exact not_returned_of_last (hv.2.2.2.2.1 l) (hlast l) hr
        intro n hn
        rw [needs_recordEntry hne] at hn
        exact hX.dependency.ready e hr n hn
      acyclic := horder.depAcyclic }
    shfl := hX.shfl
    vote := hX.vote
    warpValue := hX.warpValue
    matrix := hX.matrix
    elect := hX.elect
    warpBar := hX.warpBar
    observation := horder.observation
    object := horder.object
    asyncObject := horder.asyncObject
    initFence := horder.initFence
    noFuture := hX.noFuture.of_frame (fun _ _ _ h => h) rfl
      (fun _ _ _ h => ByteCausality.of_same_context (X := X) (Y := X.recordEntry cta r) rfl rfl
        (fun he => modelCausality_recordEntry.mp he) (fun he => he) h)
    hidden := hX.hidden.of_frame (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
      (fun _ _ _ h => ByteCausality.of_same_context (X := X) (Y := X.recordEntry cta r) rfl rfl
        (fun he => modelCausality_recordEntry.mp he) (fun he => he) h)
    tma := hX.tma
    clc := hX.clc
    tensor := hX.tensor
    store := hX.store
    reduce := ⟨hX.reduce.1, hX.reduce.2⟩
    atomic := ⟨hX.atomic.1, hX.atomic.2⟩
    fenceSc := ⟨hX.fenceSc.1, hX.fenceSc.2, hX.fenceSc.3⟩
    tmemPair := hX.tmemPair.recordEntry hv hkey hrun
    tmemPairCompletion := completionClosed_recordEntry hX.tmemPairCompletion hready
    tmemPairResult := hres
    tcCommit := hX.tcCommit
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
    tcRead := hread
    asm := hasm }

/-- A pairing keeps the readiness of every event: it adds a complete operation and the pairing
needs only grow. -/
theorem ready_recordPairing {e : EvId} (hr : Ready L X e) : Ready L (X.recordPairing q) e := by
  intro n hn
  unfold Ready Needs at hr
  change n ∈ (match X.get e with
    | none => []
    | some ev => KindNeeds L (X.recordPairing q) ev.kind e) at hn
  cases hg : X.get e with
  | none => rw [hg] at hn; cases hn
  | some ev =>
    rw [hg] at hn hr
    simp only at hn hr
    cases hk : ev.kind
    all_goals rw [hk] at hn hr
    all_goals try exact hr n hn
    cases ‹TcKind›
    all_goals try exact hr n hn
    rename_i group dst request
    simp only [KindNeeds, resourceNeeds, List.mem_append, List.mem_cons] at hn
    rcases hn with (hn | rfl | hn) | hresult
    · change n ∈ tcNeeds L X e at hn
      exact hr n (by simp [KindNeeds, resourceNeeds, hn])
    · exact hr (.cond (Performed L X e)) (by simp [KindNeeds, resourceNeeds])
    · unfold needsIf at hn
      split_ifs at hn with hm
      swap
      · cases hn
      have hm' : MustWait X e := hm
      simp only [List.mem_cons, List.mem_append] at hn
      rcases hn with (rfl | hn) | hn
      · exact Covered.mono le_recordPairing
          (hr (.cond (Covered L X e)) (by simp [KindNeeds, resourceNeeds, needsIf, hm']))
      · cases group with
        | one => cases hn
        | two =>
          simp only [List.mem_map] at hn
          obtain ⟨l, -, rfl⟩ := hn
          obtain ⟨x, hx, q', hq', hp⟩ := hr (.node fun x =>
              ∃ q ∈ X.tmemPairing, (Participates L q.1 e ∧ x = .thread (q.2.event L l)) ∨
                (Participates L q.2 e ∧ x = .thread (q.1.event L l)))
            (by simp [KindNeeds, resourceNeeds, needsIf, hm'])
          exact ⟨x, hx, q', List.mem_append_left _ hq', hp⟩
      · refine hr n ?_
        simp only [KindNeeds, resourceNeeds, needsIf, hm', ↓reduceIte, List.mem_append,
          List.mem_cons]
        exact Or.inl (Or.inr (Or.inr (Or.inr hn)))
    · exact hr n (List.mem_append_right _ hresult)

/-- Pairing two recorded cta_group::2 requests keeps an execution consistent, given the
execution-order axioms for the waiting edges of the completed operation and its readiness. -/
theorem consistent_recordPairing {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (horder : OrderOk L K A (X.recordPairing q))
    (hpairs : HistoriesOk L (X.recordPairing q)) (hready : CompletionReady L X [q.1, q.2])
    (hquiet : PairingQuiet L X q) (hasm : ∀ a ∈ A, a.wf L mem0 (X.recordPairing q)) :
    Consistent L K A mem0 (X.recordPairing q) where
  thr := hX.thr
  outside := hX.outside
  rf := hX.rf
  ctaBar := hX.ctaBar
  cluster := hX.cluster
  dependency := ⟨fun e hr => ready_recordPairing (hX.dependency.ready e hr), horder.depAcyclic⟩
  shfl := hX.shfl
  vote := hX.vote
  warpValue := hX.warpValue
  matrix := hX.matrix
  elect := hX.elect
  warpBar := hX.warpBar
  observation := horder.observation
  asyncObject := horder.asyncObject
  object := horder.object
  initFence := horder.initFence
  noFuture := hX.noFuture.of_frame (fun _ _ _ h => h) rfl
    (fun _ _ _ h => ByteCausality.of_same_context (X := X) (Y := X.recordPairing q) rfl rfl
      (fun he => modelCausality_recordPairing.mp he) (fun he => he) h)
  hidden := hX.hidden.of_frame (fun _ _ _ h => h) (fun _ _ _ h => h) rfl
    (fun _ _ _ h => ByteCausality.of_same_context (X := X) (Y := X.recordPairing q) rfl rfl
      (fun he => modelCausality_recordPairing.mp he) (fun he => he) h)
  tma := hX.tma
  clc := hX.clc
  tensor := hX.tensor
  store := hX.store
  reduce := ⟨hX.reduce.1, hX.reduce.2⟩
  atomic := ⟨hX.atomic.1, hX.atomic.2⟩
  fenceSc := ⟨hX.fenceSc.1, hX.fenceSc.2, hX.fenceSc.3⟩
  tmemPair := hpairs
  tmemPairResult := hX.tmemPairResult.recordPairing
  tcCommit := hX.tcCommit
  tmemPairCompletion := completionClosed_recordPairing hX.tmemPairCompletion hready
  mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
  tcRead := readOk_recordPairing hX.tcRead hX.tma.2.1 hquiet
  asm := hasm

end Tmem.Pair
end
end PTX
