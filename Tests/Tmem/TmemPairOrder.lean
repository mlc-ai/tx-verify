-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairOrder
public import Lemmas.Tmem.TmemPairRecord
public import Mathlib.Tactic.IntervalCases
public import Lemmas.Order.WaitOrderObject

namespace PTX.Tests.TmemPairOrder
open Tmem.Pair
noncomputable section

/-! Litmus tests for OBJ-TMEM-ORDER (EXT-TMEM-ALLOC-ORDER): the history of a CTA's
Tensor Memory allocator contains causality order between its requests.

(a) Warp 0 allocates 512 columns and frees them, `bar.sync`, then warp 1 allocates 256 columns and
frees them. Causality orders the requests, so every coherent history of the four records is the
causal one, which replays without a fault (`synced_safe`); the increasing order 256-before-512
faults but is not coherent (`synced_increasing`). (b) The same requests without the barrier:
causality does not order the warps, so the increasing order is a valid, coherent history and it
faults (`unsynced_increasing`). (c) One warp's program order and the uniqueness of a request are
still enforced (`reversed_incoherent`, `repeated_incoherent`). (d) Warp 0 allocates 32 columns at
column 0 and frees them, `bar.sync`, then warp 1 allocates 32 columns at column 32 and frees them:
disjoint columns, so any order of the records replays without blocking. The state in which warp 0
has passed its deallocation while only the two allocations are recorded is excluded: a lane that
returned from a deallocation has it performed (DEP-TMEM-ALLOC-WAIT, `stuck_not_blocking`), although
the history replays (`stuck_histories`) and agrees with causality (`stuck_coherent`). The history
with the deallocation performed at its return satisfies the resource rules (`repaired_*`), the
remaining deallocation of warp 1 can be performed (`repaired_entry`), and the execution with all
four records is drained and releases every allocation (`complete_*`). -/

private def L : Launch := { grid := 1, block := 64, params := fun _ => none }

/-- The group-1 request of warp `w` of CTA 0 whose lanes are at trace index `i`. -/
private def req (w i : Nat) (a : Tmem.Action) : Requests :=
  ⟨⟨0, w, fun _ => i, 10 * w + i, match a with | .alloc .. => some ⟨.shared, 0, 0⟩ | _ => none,
    a.request⟩, .one, a⟩

private def ev (r : Requests) : Event := ⟨r.own.pc, .tc (.resource .one r.own.dst r.own.request)⟩

private def barEv : Event := ⟨100, .bar 0 none⟩

/-- The arrival of warp `w` whose lanes are at trace index `i`. -/
private def arrivals (w i : Nat) : List (Nat × EvId) :=
  (List.range 32).map fun l => (w * 32 + l, (w * 32 + l, i))

/-! ## (a) Ordered by a CTA barrier -/

private def a0 : Requests := req 0 0 (.alloc 512 0)
private def d0 : Requests := req 0 1 (.dealloc 0 512)
private def a1 : Requests := req 1 1 (.alloc 256 0)
private def d1 : Requests := req 1 2 (.dealloc 0 256)

/-- Warp 0: alloc 512, dealloc, `bar.sync 0`; warp 1: `bar.sync 0`, alloc 256, dealloc. -/
private def synced (h : List Requests) : Execution := {
  tr := fun g => if g < 32 then [ev a0, ev d0, barEv]
    else if g < 64 then [barEv, ev a1, ev d1] else []
  rf := fun _ _ => none
  barriers := fun c => if c = 0 then
    [.arrival 0 0 none (arrivals 0 2), .arrival 0 1 none (arrivals 1 0)] else []
  tmemHistory := fun k => if k = 0 then h else [] }

private theorem synced_barK0 (h : List Requests) (l : Fin 32) :
    CtaBarK L (synced h) (l.val, 2) 0 := by
  have hl := l.isLt
  refine ⟨by simp [Launch.threads, L]; omega, ⟨none, 100, ?_⟩, ?_⟩
  · simp [Execution.IsBarrier, Execution.get, synced, hl, barEv]
  · show CtaBarrier.GenerationOf 64 ((synced h).barriers (l.val / 64)) (l.val, 2) 0 0
    rw [Nat.div_eq_of_lt (by omega)]
    refine ⟨0, {}, 0, none, arrivals 0 2, l.val, rfl, rfl, ?_, rfl, _, rfl⟩
    simp only [arrivals, List.mem_map, List.mem_range]
    exact ⟨l.val, hl, by simp⟩

private theorem synced_barK1 (h : List Requests) (l : Fin 32) :
    CtaBarK L (synced h) (32 + l.val, 0) 0 := by
  have hl := l.isLt
  refine ⟨by simp [Launch.threads, L]; omega, ⟨none, 100, ?_⟩, ?_⟩
  · have h1 : ¬ 32 + l.val < 32 := by omega
    have h2 : 32 + l.val < 64 := by omega
    simp [Execution.IsBarrier, Execution.get, synced, h1, h2, barEv]
  · show CtaBarrier.GenerationOf 64 ((synced h).barriers ((32 + l.val) / 64)) (32 + l.val, 0) 0 0
    rw [Nat.div_eq_of_lt (by omega)]
    refine ⟨1, _, 1, none, arrivals 1 0, 32 + l.val, rfl, rfl, ?_, rfl, _, rfl⟩
    simp only [arrivals, List.mem_map, List.mem_range]
    exact ⟨l.val, hl, by simp⟩

/-- `bar.sync`: an instruction of warp 0 before the barrier happens before an instruction of
warp 1 after it. -/
private theorem synced_baseCausality (h : List Requests) (l l' : Fin 32) {i j : Nat} (hi : i < 2)
    (hj : 0 < j) (hj3 : j < 3) : baseCausality L (synced h) (l.val, i) (32 + l'.val, j) := by
  have hl := l.isLt
  have hl' := l'.isLt
  refine .single (.inr (.inl ⟨⟨by simp [Launch.threads, L]; omega,
    by simp [Launch.threads, L]; omega, by simp [L]; omega⟩, 0, 2, 0,
    (let hk := synced_barK0 h l; ⟨hk.1, (let ⟨c, pc, h⟩ := hk.2.1; ⟨c, pc, _, h⟩), hk.2.2⟩),
    synced_barK1 h l', hi, hj, ?_⟩))
  have h1 : ¬ 32 + l'.val < 32 := by omega
  have h2 : 32 + l'.val < 64 := by omega
  simp [synced, h1, h2, hj3]

/-- The four requests, ranked in their causal order. -/
private def rank (r : Requests) : Nat :=
  2 * r.own.warp + match r.action with | .alloc .. => 0 | _ => 1

private theorem lane_event {w i : Nat} {a : Tmem.Action} {e : EvId}
    (hp : Participates L (req w i a).own e) : ∃ l : Fin 32, e = (w * 32 + l.val, i) := by
  obtain ⟨l, rfl⟩ := hp
  exact ⟨l, by simp [WarpRequest.event, req, L]⟩

private theorem synced_get (h : List Requests) {g : Nat} {i : Nat} (hg : g < 64) (hi : i < 3) :
    ∃ ev, (synced h).get (g, i) = some ev := by
  by_cases h1 : g < 32
  · simp only [Execution.get, synced, h1, ite_true]
    exact ⟨_, List.getElem?_eq_getElem (by simpa using hi)⟩
  · simp only [Execution.get, synced, h1, hg, ite_false, ite_true]
    exact ⟨_, List.getElem?_eq_getElem (by simpa using hi)⟩

private theorem synced_acc (h : List Requests) {g : Nat} {i : Nat} (hg : g < 64) (hi : i < 3) :
    ((synced h).get (g, i)).bind Event.acc = none := by
  by_cases h1 : g < 32
  · simp only [Execution.get, synced, h1, ite_true]
    interval_cases i <;> simp [Event.acc, ev, barEv]
  · simp only [Execution.get, synced, h1, hg, ite_false, ite_true]
    interval_cases i <;> simp [Event.acc, ev, barEv]

/-- In a coherent history, the four requests appear in their causal order. -/
private theorem synced_rank_lt {h : List Requests} (hco : ObjectCoherent L (synced h))
    {k l : Nat} {x y : Requests} (hx : h[k]? = some x) (hy : h[l]? = some y) (hkl : k < l)
    (mx : x ∈ [a0, d0, a1, d1]) (my : y ∈ [a0, d0, a1, d1]) : rank x < rank y := by
  have hx' : (synced h).tmemHistory 0 = h := rfl
  rw [← hx'] at hx hy
  -- the lane-0 events of the two records
  have lane (r : Requests) (hr : r ∈ [a0, d0, a1, d1]) :
      Participates L r.own (r.own.warp * 32, r.own.indices 0) ∧ r.own.indices 0 < 3 ∧
        r.own.warp < 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact ⟨⟨0, by simp [WarpRequest.event, a0, d0, a1, d1, req, L]⟩, by decide,
        by decide⟩
  obtain ⟨px, ix, wx⟩ := lane x mx
  obtain ⟨py, iy, wy⟩ := lane y my
  by_cases hw : x.own.warp = y.own.warp
  · have hlt := hco.lane_lt hx hy hkl px py (by simp [hw]) (synced_get h (by
      omega) ix) (synced_acc h (by omega) ix)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mx my
    rcases mx with rfl | rfl | rfl | rfl <;> rcases my with rfl | rfl | rfl | rfl <;>
      simp_all [a0, d0, a1, d1, req, rank]
  · by_contra hn
    -- `y` is a warp-0 request and `x` a warp-1 request: `y` causally precedes `x`.
    have hxw : x.own.warp = 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mx my
      rcases mx with rfl | rfl | rfl | rfl <;> rcases my with rfl | rfl | rfl | rfl <;>
        simp_all [a0, d0, a1, d1, req, rank]
    have hyw : y.own.warp = 0 := by omega
    have hp : Precedes L (synced h) 0 (x.own.warp * 32, x.own.indices 0)
        (y.own.warp * 32, y.own.indices 0) :=
      ⟨k, l, x, y, hx, hy, hkl, px, py⟩
    have hyi : y.own.indices 0 < 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at my
      rcases my with rfl | rfl | rfl | rfl <;> simp_all [a0, d0, a1, d1, req]
    have hxi : 0 < x.own.indices 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mx
      rcases mx with rfl | rfl | rfl | rfl <;> simp_all [a0, d0, a1, d1, req]
    have hhb := synced_baseCausality h 0 0 hyi hxi ix
    simp only [Fin.val_zero, Nat.add_zero] at hhb
    rw [hxw, hyw] at hp
    simp only [Nat.zero_mul, Nat.one_mul] at hp
    obtain ⟨ev, hev⟩ := synced_get h (g := 32) (by decide) ix
    have c1 : stageCausality L (synced h) (.thread (0, y.own.indices 0), true)
        (.thread (32, x.own.indices 0), false) := .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, hhb⟩)
    have c2 : stageCausality L (synced h) (.thread (32, x.own.indices 0), false)
        (.thread (32, x.own.indices 0), true) := .inl (.inl ⟨rfl, rfl, rfl, ev, hev⟩)
    exact hco.not_precedes hp (.tail (.single c1) c2)

/-- The causal order of the four requests replays without a fault. -/
private theorem causal_replay : runRequests {} [a0, d0, a1, d1] =
    .done { previousColumns := some 256, nextLifetime := 2 } := by
  decide

/-- (a) Every coherent history of the four requests is the causal order, which replays without
a fault: no column increase is reported. -/
theorem synced_safe (h : List Requests) (hperm : h.Perm [a0, d0, a1, d1])
    (hco : ObjectCoherent L (synced h)) : ¬ ResourceUnsafe L (synced h) := by
  have hmem : ∀ x ∈ h, x ∈ [a0, d0, a1, d1] := fun x hx => hperm.subset hx
  have hsorted : h.Pairwise (fun x y => rank x < rank y) := by
    rw [List.pairwise_iff_getElem]
    intro k l hk hl hkl
    exact synced_rank_lt hco (List.getElem?_eq_getElem hk) (List.getElem?_eq_getElem hl) hkl
      (hmem _ (List.getElem_mem hk)) (hmem _ (List.getElem_mem hl))
  have hcausal : [a0, d0, a1, d1].Pairwise (fun x y => rank x < rank y) := by
    simp [a0, d0, a1, d1, req, rank]
  have heq : h = [a0, d0, a1, d1] :=
    hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => absurd (h1.trans h2) (Nat.lt_irrefl _)) hsorted
      hcausal
  rintro ⟨key, ⟨reason, hf⟩ | ⟨k, l, d, a, hd, -, -, hg, -⟩⟩
  · by_cases hk : key = 0
    · subst hk heq
      change runRequests {} [a0, d0, a1, d1] = _ at hf
      rw [causal_replay] at hf
      cases hf
    · have hnil : (synced h).tmemHistory key = [] := by simp [synced, hk]
      rw [hnil] at hf
      cases hf
  -- cta_group::1 deallocations are not pending (EXT-TMEM-ALLOC-ORDER)
  · have hd' := List.mem_of_getElem? hd
    by_cases hk : key = 0
    · subst hk heq
      change d ∈ [a0, d0, a1, d1] at hd'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with rfl | rfl | rfl | rfl <;> cases hg
    · simp [synced, hk] at hd'

/-- (a) The increasing order 256-before-512 faults, but it reverses causality. -/
theorem synced_increasing :
    ResourceUnsafe L (synced [a1, d1, a0, d0]) ∧ ¬ ObjectCoherent L (synced [a1, d1, a0, d0]) := by
  refine ⟨⟨0, .inl ⟨.increasingRequest, by decide⟩⟩, fun hco => ?_⟩
  have := synced_rank_lt hco (k := 0) (l := 2) (x := a1) (y := a0) rfl rfl (by decide)
    (by simp) (by simp)
  simp [a0, a1, req, rank] at this

/-! ## (b) Not ordered by causality -/

private def b1 : Requests := req 1 0 (.alloc 256 0)
private def e1 : Requests := req 1 1 (.dealloc 0 256)

/-- Warp 0: alloc 512, dealloc; warp 1: alloc 256, dealloc; no synchronization. -/
private def unsynced (h : List Requests) : Execution := {
  tr := fun g => if g < 32 then [ev a0, ev d0] else if g < 64 then [ev b1, ev e1] else []
  rf := fun _ _ => none
  tmemHistory := fun k => if k = 0 then h else [] }

private theorem unsynced_kind {h : List Requests} {e : EvId} {pc : Nat} {k : Kind}
    (he : (unsynced h).get e = some ⟨pc, k⟩) : ∃ g d a, k = .tc (.resource g d a) := by
  obtain ⟨g, i⟩ := e
  simp only [Execution.get, unsynced] at he
  split_ifs at he
  all_goals
    rcases i with _ | _ | i <;> simp [ev, a0, d0, b1, e1, req] at he <;>
      exact ⟨_, _, _, he.2.symm⟩

private theorem unsynced_async {h : List Requests} (i : EvId) (p : AsyncCopy.Part) :
    ¬ (unsynced h).AsyncPresent i p := by
  cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, unsynced]

/-- Without synchronization, causality is program order. -/
private theorem unsynced_baseCausality {h : List Requests} {e f : EvId}
    (hh : baseCausality L (unsynced h) e f) :
    e.1 = f.1 ∧ e.2 < f.2 := by
  have notKind {e : EvId} {pc : Nat} {k : Kind} (he : (unsynced h).get e = some ⟨pc, k⟩)
      (hk : ∀ g d a, k ≠ .tc (.resource g d a)) : False := by
    obtain ⟨g, d, a, rfl⟩ := unsynced_kind he
    exact hk g d a rfl
  have base : ∀ {e f : EvId}, (po (unsynced h) e f ∨ CtaBarSync L (unsynced h) e f ∨
      MSync L (unsynced h) e f ∨ ClusterSync L (unsynced h) e f ∨
      WarpBarSync L (unsynced h) e f ∨ synchronizesWith L (unsynced h) e f ∨
      FenceSync L (unsynced h) e f) → e.1 = f.1 ∧ e.2 < f.2 := by
    intro e f h
    rcases h with h | ⟨_, _, _, _, _, ⟨_, ⟨_, _, hb⟩, _⟩, _⟩ |
        ⟨_, _, _, _, _, _, ⟨⟨_, _, hw⟩, _⟩, _⟩ | ⟨_, _, _, ⟨_, ⟨k, _, _, _, _, _, _, hk, _⟩, _⟩,
          _⟩ |
        ⟨_, _, ⟨_, _, _, ⟨_, hb⟩, _⟩, _⟩ | ⟨_, _, _, _, ⟨_, hb⟩ | ⟨_, _, hb⟩, _⟩ | h
    · exact ⟨h.1, h.2.1⟩
    · exact (notKind hb (by simp)).elim
    · exact (notKind hw (by simp)).elim
    · simp [unsynced] at hk
    · exact (notKind hb (by simp)).elim
    · exact (notKind hb (by simp)).elim
    · exact (notKind hb (by simp)).elim
    · exact (not_fenceSync_of_noFence (fun _ _ _ ⟨_, hb⟩ => notKind hb (by simp)) _ _ h).elim
  unfold PTX.baseCausality at hh
  induction hh with
  | single h => exact base h
  | tail _ h ih =>
    have := base h
    exact ⟨ih.1.trans this.1, by omega⟩

/-- The position of a thread's node in the history `[b1, e1, a0, d0]`. -/
private def pos : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * (e.2 + if e.1 < 32 then 2 else 0) + b.toNat
  | (.async _ _, _) => 0

private theorem unsynced_cause {h : List Requests} {a c : AsyncCopy.Ref × Bool}
    (hc : stageCausality L (unsynced h) a
        c) : ∃ e f, a.1 = .thread e ∧ c.1 = .thread f ∧ e.1 = f.1 ∧
      2 * e.2 + a.2.toNat < 2 * f.2 + c.2.toNat := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases hc with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨rfl, rfl, i, j, rfl, rfl, hc⟩ |
      ⟨-, -, -, -, i, p, w, ws, -, -, ⟨n, m, -, ⟨pc, parity, hget⟩, -⟩, -, -⟩
  · cases e with
    | thread e => exact ⟨e, e, rfl, rfl, rfl, by simp⟩
    | async i p => exact (unsynced_async i p hp).elim
  · unfold StageEdge at hs
    split at hs <;> simp_all [unsynced_async]
  · have := unsynced_baseCausality hc
    exact ⟨i, j, rfl, rfl, this.1, by simp; omega⟩
  · obtain ⟨g, d, a, hk⟩ := unsynced_kind hget
    cases hk

/-- (b) Without the barrier the increasing order is coherent: causality does not order the
two warps' requests. -/
theorem unsynced_coherent : ObjectCoherent L (unsynced [b1, e1, a0, d0]) := fun o =>
  acyclic_of_rank pos fun a c h => by
    rcases h with h | h
    · obtain ⟨e, f, ha, hc, h1, h2⟩ := unsynced_cause h
      obtain ⟨a, b⟩ := a
      obtain ⟨c, b'⟩ := c
      simp only at ha hc h2
      subst ha hc
      simp only [pos, h1]
      omega
    · obtain ⟨e, b⟩ := a
      obtain ⟨f, b'⟩ := c
      cases o with
      | mbar m =>
        obtain ⟨⟨-, -, a, b, ra, rb, ha, -⟩, -⟩ := h
        simp [unsynced] at ha
      | ctaBar c id =>
        obtain ⟨-, -, -, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [unsynced] at hr
      | cluster c =>
        obtain ⟨-, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [unsynced] at hr
      | tmem key =>
        obtain ⟨rfl, rfl, i, j, rfl, rfl, k, l, x, y, hx, hy, hkl, hi, hj⟩ := h
        by_cases hk0 : key = 0
        · subst hk0
          change [b1, e1, a0, d0][k]? = some x at hx
          change [b1, e1, a0, d0][l]? = some y at hy
          have hpos : ∀ n r e, [b1, e1, a0, d0][n]? = some r → Participates L (Requests.own r) e →
              pos (.thread e, true) = 2 * n + 1 := by
            intro n r e hn hp
            have hlt := (List.getElem?_eq_some_iff.mp hn).1
            simp only [List.length_cons, List.length_nil] at hlt
            interval_cases n
            all_goals
              simp at hn
              subst hn
              obtain ⟨l, rfl⟩ := lane_event hp
              have hl := l.isLt
              simp [pos]
          rw [hpos k x i hx hi, hpos l y j hy hj]
          omega
        · simp [unsynced, hk0] at hx

/-- (b) The increasing order is a history of valid records and its replay faults. -/
theorem unsynced_increasing : HistoriesOk L (unsynced [b1, e1, a0, d0]) ∧
    ResourceUnsafe L (unsynced [b1, e1, a0, d0]) := by
  refine ⟨⟨fun key => ?_, (fun q hq => by cases hq), List.Pairwise.nil⟩,
    ⟨0, .inl ⟨.increasingRequest, by decide⟩⟩⟩
  by_cases hk : key = 0
  · subst hk
    refine ⟨fun r hr => ?_, fun r hr => ?_, by decide⟩
    · change r ∈ [b1, e1, a0, d0] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      all_goals refine ⟨by decide, rfl, by decide, by decide,
        fun lane => by fin_cases lane <;> rfl, ?_⟩
      · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
      · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
      · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
      · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
    · change r ∈ [b1, e1, a0, d0] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · have hnil : (unsynced [b1, e1, a0, d0]).tmemHistory key = [] := by simp [unsynced, hk]
    refine ⟨?_, ?_, ?_⟩ <;> rw [hnil]
    · simp [RequestHistory]
    · simp
    · simp [runRequests]

/-! ## (c) Program order of one warp and uniqueness -/

/-- Reversing one warp's program order is excluded. -/
theorem reversed_incoherent : ¬ ObjectCoherent L (unsynced [d0, a0]) := by
  intro hco
  have := hco.lane_lt (cta := 0) (k := 0) (l := 1) (x := d0) (y := a0) rfl rfl (by decide)
    (e := (0, 1)) (f := (0, 0)) ⟨0, by simp [WarpRequest.event, d0, req, L]⟩
    ⟨0, by simp [WarpRequest.event, a0, req, L]⟩ rfl
    ⟨_, rfl⟩ rfl
  simp at this

/-- Recording one request twice is excluded. -/
theorem repeated_incoherent : ¬ ObjectCoherent L (unsynced [a0, a0]) := by
  intro hco
  have := hco.lane_lt (cta := 0) (k := 0) (l := 1) (x := a0) (y := a0) rfl rfl (by decide)
    (e := (0, 0)) (f := (0, 0)) ⟨0, by simp [WarpRequest.event, a0, req, L]⟩
    ⟨0, by simp [WarpRequest.event, a0, req, L]⟩ rfl
    ⟨_, rfl⟩ rfl
  simp at this

/-! ## (d) A deallocation is performed by its return -/

private def c0 : Requests := req 0 0 (.alloc 32 0)
private def f0 : Requests := req 0 1 (.dealloc 0 32)
private def c1 : Requests := req 1 1 (.alloc 32 32)
private def f1 : Requests := req 1 2 (.dealloc 32 32)

/-- Warp 0: alloc 32 at column 0, dealloc, `bar.sync 0`; warp 1: `bar.sync 0`, alloc 32 at
column 32, dealloc. -/
private def disjoint (h : List Requests) : Execution := {
  tr := fun g => if g < 32 then [ev c0, ev f0, barEv]
    else if g < 64 then [barEv, ev c1, ev f1] else []
  rf := fun _ _ => none
  barriers := fun c => if c = 0 then
    [.arrival 0 0 none (arrivals 0 2), .arrival 0 1 none (arrivals 1 0)] else []
  tmemHistory := fun k => if k = 0 then h else [] }

private theorem disjoint_get_eq (h : List Requests) {g i : Nat} : (disjoint h).get (g, i) =
    (if g < 32 then [ev c0, ev f0, barEv] else if g < 64 then [barEv, ev c1, ev f1]
      else [])[i]? := by
  simp [Execution.get, disjoint]

/-- The resource events: allocations at `(g,0)`/`(g,1)`, deallocations at `(g,1)`/`(g,2)`. -/
private theorem disjoint_resource {h : List Requests} {i : EvId} {pc : Nat} {group : CtaGroup}
    {dst : Option Loc} {request : Tmem.Request}
    (he : (disjoint h).get i = some ⟨pc, .tc (.resource group dst request)⟩) :
    group = .one ∧ ((i.1 < 32 ∧ i.2 = 0 ∧ request = .alloc 32) ∨
      (i.1 < 32 ∧ i.2 = 1 ∧ request = .dealloc 0 32) ∨
      (32 ≤ i.1 ∧ i.1 < 64 ∧ i.2 = 1 ∧ request = .alloc 32) ∨
      (32 ≤ i.1 ∧ i.1 < 64 ∧ i.2 = 2 ∧ request = .dealloc 32 32)) := by
  obtain ⟨g, k⟩ := i
  rw [disjoint_get_eq] at he
  split_ifs at he with h1 h2
  · rcases k with _ | _ | _ | k <;> simp [ev, barEv, c0, f0, req] at he
    · exact ⟨he.2.1.symm, .inl ⟨h1, rfl, he.2.2.2.symm⟩⟩
    · exact ⟨he.2.1.symm, .inr (.inl ⟨h1, rfl, he.2.2.2.symm⟩)⟩
  · rcases k with _ | _ | _ | k <;> simp [ev, barEv, c1, f1, req] at he
    · exact ⟨he.2.1.symm, .inr (.inr (.inl ⟨by omega, h2, rfl, he.2.2.2.symm⟩))⟩
    · exact ⟨he.2.1.symm, .inr (.inr (.inr ⟨by omega, h2, rfl, he.2.2.2.symm⟩))⟩
  · simp at he

private theorem disjoint_valid0 {r : Requests} (hr : r ∈ [c0, f0, c1, f1]) :
    r.Valid L (disjoint []) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide, rfl, by decide, by decide,
    fun lane => by fin_cases lane <;> rfl, ?_⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩

/-- The four requests are actual warp requests. -/
private theorem disjoint_valid (h : List Requests) {r : Requests} (hr : r ∈ [c0, f0, c1, f1]) :
    r.Valid L (disjoint h) := by
  obtain ⟨h1, h2, h3⟩ := disjoint_valid0 hr
  exact ⟨h1, h2, (completion_valid_trace_iff rfl _ _).mp h3⟩

/-- OBJ-TMEM-ORIGIN for a history of some of the four requests whose replay does not
block. -/
private theorem disjoint_histories {h : List Requests} (hs : ∀ r ∈ h, r ∈ [c0, f0, c1, f1])
    (hrun : runRequests {} h ≠ .blocked) : HistoriesOk L (disjoint h) := by
  refine ⟨fun key => ?_, (fun q hq => by cases hq), List.Pairwise.nil⟩
  by_cases hk : key = 0
  · subst hk
    refine ⟨fun r hr => disjoint_valid h (hs r hr), fun r hr => ?_, hrun⟩
    have := hs r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  · have hnil : (disjoint h).tmemHistory key = [] := by simp [disjoint, hk]
    refine ⟨?_, ?_, ?_⟩ <;> rw [hnil]
    · simp [RequestHistory]
    · simp
    · simp [runRequests]

private theorem disjoint_kind {h : List Requests} {e : EvId} {pc : Nat} {k : Kind}
    (he : (disjoint h).get e = some ⟨pc, k⟩) :
    (∃ g d a, k = .tc (.resource g d a)) ∨ k = .bar 0 none := by
  obtain ⟨g, i⟩ := e
  rw [disjoint_get_eq] at he
  split_ifs at he
  all_goals
    rcases i with _ | _ | _ | i <;> simp [ev, barEv, c0, f0, c1, f1, req] at he
  all_goals first
    | exact .inl ⟨_, _, _, he.2.symm⟩
    | exact .inr he.2.symm

private theorem disjoint_bar {h : List Requests} {e : EvId} {id : Nat} {count : Option Nat}
    {pc : Nat} (hb : (disjoint h).IsBarrier e id count pc) :
    (e.1 < 32 ∧ e.2 = 2) ∨ (32 ≤ e.1 ∧ e.1 < 64 ∧ e.2 = 0) := by
  obtain ⟨g, i⟩ := e
  unfold Execution.IsBarrier at hb
  rw [disjoint_get_eq] at hb
  split_ifs at hb with h1 h2
  · rcases i with _ | _ | _ | i <;> simp [ev, barEv, c0, f0, req] at hb
    exact .inl ⟨h1, rfl⟩
  · rcases i with _ | _ | _ | i <;> simp [ev, barEv, c1, f1, req] at hb
    exact .inr ⟨by omega, h2, rfl⟩
  · simp at hb

private theorem disjoint_async (h : List Requests) (i : EvId) (p : AsyncCopy.Part) :
    ¬ (disjoint h).AsyncPresent i p := by
  cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, disjoint]

/-- The position of an event in the causal order: warp 1's events follow the barrier. -/
private def drk (e : EvId) : Nat := e.2 + if e.1 < 32 then 0 else 3

private theorem disjoint_len {h : List Requests} {g : Nat} (hg : g < 64) :
    ((disjoint h).tr g).length = 3 := by
  simp only [disjoint]; split_ifs <;> simp

private theorem disjoint_baseCausality {h : List Requests} {e f : EvId}
    (hh : baseCausality L (disjoint h) e f) :
    drk e < drk f := by
  have notKind {e : EvId} {pc : Nat} {k : Kind} (he : (disjoint h).get e = some ⟨pc, k⟩)
      (hk : ∀ g d a, k ≠ .tc (.resource g d a)) (hb : k ≠ .bar 0 none) : False := by
    rcases disjoint_kind he with ⟨g, d, a, rfl⟩ | rfl
    · exact hk g d a rfl
    · exact hb rfl
  have base : ∀ {e f : EvId}, (po (disjoint h) e f ∨ CtaBarSync L (disjoint h) e f ∨
      MSync L (disjoint h) e f ∨ ClusterSync L (disjoint h) e f ∨
      WarpBarSync L (disjoint h) e f ∨ synchronizesWith L (disjoint h) e f ∨
      FenceSync L (disjoint h) e f) → drk e < drk f := by
    intro e f h
    rcases h with h |
        ⟨-, key, i, j, ⟨-, ⟨c1, p1, m1, hbi⟩, -⟩, ⟨-, ⟨c2, p2, hbj⟩, -⟩, hei, hjf, hfl⟩ |
        ⟨_, _, _, _, _, _, ⟨⟨_, _, hw⟩, _⟩, _⟩ | ⟨_, _, _, ⟨_, ⟨k, _, _, _, _, _, _, hk, _⟩, _⟩,
          _⟩ |
        ⟨_, _, ⟨_, _, _, ⟨_, hb⟩, _⟩, _⟩ | ⟨_, _, _, _, ⟨_, hb⟩ | ⟨_, _, hb⟩, _⟩ | h
    · unfold drk; rw [h.1]; have := h.2.1; omega
    · have hi := disjoint_bar (count := c1) (pc := p1) (by cases m1 <;> first | exact hbi |
        (exfalso; exact notKind hbi (by simp) (by simp)))
      have hj := disjoint_bar hbj
      simp only at hi hj
      have hf64 : f.1 < 64 := by omega
      rw [disjoint_len hf64] at hfl
      unfold drk
      split_ifs <;> omega
    · exact (notKind hw (by simp) (by simp)).elim
    · simp [disjoint] at hk
    · exact (notKind hb (by simp) (by simp)).elim
    · exact (notKind hb (by simp) (by simp)).elim
    · exact (notKind hb (by simp) (by simp)).elim
    · exact (not_fenceSync_of_noFence
        (fun _ _ _ ⟨_, hb⟩ => notKind hb (by simp) (by simp)) _ _ h).elim
  unfold PTX.baseCausality at hh
  induction hh with
  | single h => exact base h
  | tail _ h ih => exact ih.trans (base h)

private def dpos : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * drk e + b.toNat
  | (.async _ _, _) => 0

private theorem disjoint_cause {h : List Requests} {a c : AsyncCopy.Ref × Bool}
    (hc : stageCausality L (disjoint h) a c) : dpos a < dpos c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases hc with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, hs⟩) | ⟨rfl, rfl, i, j, rfl, rfl, hc⟩ |
      ⟨-, -, -, -, i, p, w, ws, -, -, ⟨n, m, -, ⟨pc, parity, hget⟩, -⟩, -, -⟩
  · cases e with
    | thread e => simp [dpos]
    | async i p => exact (disjoint_async h i p hp).elim
  · unfold StageEdge at hs
    split at hs <;> simp_all [disjoint_async]
  · have := disjoint_baseCausality hc
    simp [dpos]; omega
  · rcases disjoint_kind hget with ⟨g, d, a, hk⟩ | hk <;> cases hk

/-- The rank of a request in the causal order. -/
private def drank (r : Requests) : Nat := r.own.indices 0 + 3 * r.own.warp

/-- OBJ-TMEM-ORDER for a history of the four requests in causal order. -/
private theorem disjoint_coherent {h : List Requests} (hs : ∀ r ∈ h, r ∈ [c0, f0, c1, f1])
    (hsorted : h.Pairwise fun x y => drank x < drank y) : ObjectCoherent L (disjoint h) := fun o =>
  acyclic_of_rank dpos fun a c hac => by
    rcases hac with hac | hac
    · exact disjoint_cause hac
    · obtain ⟨e, b⟩ := a
      obtain ⟨f, b'⟩ := c
      cases o with
      | mbar m =>
        obtain ⟨⟨-, -, a, b, ra, rb, ha, -⟩, -⟩ := hac
        simp [disjoint] at ha
      | ctaBar c id =>
        obtain ⟨rfl, rfl, i, j, rfl, rfl, -, -, k, l, r, q, hr, hq, hkl, -, -, hi, hj⟩ := hac
        by_cases hc : c = 0
        · subst hc
          simp only [disjoint, ite_true] at hr hq
          have hl : l < 2 := (List.getElem?_eq_some_iff.mp hq).1
          interval_cases l
          · omega
          · interval_cases k
            simp at hr hq
            subst hr hq
            simp [CtaBarrier.Record.refs, arrivals] at hi hj
            obtain ⟨x, hx, rfl⟩ := hi
            obtain ⟨y, hy, rfl⟩ := hj
            simp only [dpos, drk, Bool.toNat_false]
            split_ifs <;> omega
        · simp [disjoint, hc] at hr
      | cluster c =>
        obtain ⟨-, -, -, -, -, -, k, -, r, -, hr, -⟩ := hac
        simp [disjoint] at hr
      | tmem key =>
        obtain ⟨rfl, rfl, i, j, rfl, rfl, k, l, x, y, hx, hy, hkl, hi, hj⟩ := hac
        by_cases hk0 : key = 0
        · subst hk0
          change h[k]? = some x at hx
          change h[l]? = some y at hy
          have hxy : drank x < drank y := by
            obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hx
            obtain ⟨hl', rfl⟩ := List.getElem?_eq_some_iff.mp hy
            exact List.pairwise_iff_getElem.mp hsorted k l hk' hl' hkl
          have hlane : ∀ r e, r ∈ [c0, f0, c1, f1] → Participates L r.own e →
              dpos (.thread e, true) = 2 * drank r + 1 := by
            intro r e hr hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            all_goals
              obtain ⟨l, rfl⟩ := lane_event hp
              have := l.isLt
              simp [dpos, drk, drank, c0, f0, c1, f1, req]
          rw [hlane x i (hs x (List.mem_of_getElem? hx)) hi,
            hlane y j (hs y (List.mem_of_getElem? hy)) hj]
          omega
        · simp [disjoint, hk0] at hx

/-- The stuck state: both allocations are recorded, warp 0's deallocation is not. Its history
replays without blocking. -/
theorem stuck_histories : HistoriesOk L (disjoint [c0, c1]) :=
  disjoint_histories (by simp) (by decide)

/-- The stuck state's history agrees with causality. -/
theorem stuck_coherent : ObjectCoherent L (disjoint [c0, c1]) :=
  disjoint_coherent (by simp) (by simp [drank, c0, c1, req])

/-- **Excluded**: warp 0 has returned from its deallocation, which its CTA's allocator has not
performed. -/
theorem stuck_not_blocking : ¬ Tmem.Pair.Blocking L (disjoint [c0, c1]) := by
  intro hb
  obtain ⟨cta, x, hx, l, hl⟩ := hb.performed (i := (0, 1)) (pc := 1) (group := .one)
    (dst := none) (request := .dealloc 0 32) rfl (by decide)
  by_cases hc : cta = 0
  · subst hc
    change x ∈ [c0, c1] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    have h2 := congrArg Prod.snd hl
    have h1 := congrArg Prod.fst hl
    rcases hx with rfl | rfl <;> simp [WarpRequest.event, c0, c1, req, L] at h1 h2
  · simp [disjoint, hc] at hx

/-- So the stuck state is no consistent execution. -/
theorem stuck_not_consistent {K : Kernel} {A : List Assumption} {mem0 : Mem0} :
    ¬ Consistent L K A mem0 (disjoint [c0, c1]) :=
  fun hX => stuck_not_blocking hX.tmemPairBlocking

/-- Every lane event of a recorded cta_group::1 request is covered. -/
private theorem disjoint_covered {h : List Requests} {r : Requests} (hr : r ∈ h)
    (hg : r.group = .one) {e : EvId} (he : Participates L r.own e) : Covered L (disjoint h) e :=
  ⟨[r.own], .inl ⟨0, r, by simpa [disjoint] using hr, hg, rfl⟩, r.own, List.mem_singleton_self _,
    he⟩

/-- The lanes of the four requests. -/
private theorem participates_of {i : EvId} {r : Requests} (hr : r ∈ [c0, f0, c1, f1])
    (hi : i.1 = r.own.warp * 32 + i.1 % 32) (hw : i.1 < 64) (hix : i.2 = r.own.indices 0) :
    Participates L r.own i := by
  refine ⟨⟨i.1 % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    simp only [WarpRequest.event, c0, f0, c1, f1, req, L] at hi hix ⊢ <;>
    ext <;> simp <;> omega

/-- The recorded resource operations suffice for the allocation-management part of return. -/
private def DisjointReturnReady (h : List Requests) : Prop :=
  ∀ i pc group dst request, (disjoint h).get i = some ⟨pc, .tc (.resource group dst request)⟩ →
    i.2 + 1 < ((disjoint h).tr i.1).length → ReturnReady L (disjoint h) i

private theorem disjoint_returnReady {h : List Requests}
    (h0 : c0 ∈ h) (h1 : f0 ∈ h) (h2 : c1 ∈ h) : DisjointReturnReady h := by
  rintro ⟨g, k⟩ pc group dst request he hl
  obtain ⟨rfl, hcase⟩ := disjoint_resource he
  have hgl : g < 64 := by
    have := len_of_get he
    by_contra hn
    simp [disjoint, show ¬ g < 32 by omega, show ¬ g < 64 by omega] at this
  have hcov : ∀ r ∈ h, r ∈ [c0, f0, c1, f1] → (g = r.own.warp * 32 + g % 32) →
      k = r.own.indices 0 → ReturnReady L (disjoint h) (g, k) := by
    intro r hr hr4 hg hk
    have hgr : r.group = .one := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr4
      rcases hr4 with rfl | rfl | rfl | rfl <;> rfl
    have hp := participates_of (i := (g, k)) hr4 hg hgl hk
    exact ⟨⟨0, r, by simpa [disjoint] using hr, hp⟩, fun _ => disjoint_covered hr hgr hp⟩
  rcases hcase with ⟨hg, rfl, rfl⟩ | ⟨hg, rfl, rfl⟩ | ⟨hg, hg', rfl, rfl⟩ | ⟨hg, hg', rfl, rfl⟩
  · exact hcov c0 h0 (by simp) (by simp [c0, req]; omega) rfl
  · exact hcov f0 h1 (by simp) (by simp [f0, req]; omega) rfl
  · exact hcov c1 h2 (by simp) (by simp [c1, req]; omega) rfl
  · simp [disjoint_len (h := h) hg'] at hl

/-- These traces lack the representative store, so the returned allocation is unready. -/
private theorem disjoint_missing_publication {h : List Requests} :
    ¬ Tmem.Pair.Blocking L (disjoint h) := by
  intro hblocking
  have he : (disjoint h).get (1, 0) =
      some ⟨0, .tc (.resource .one (some ⟨.shared, 0, 0⟩) (.alloc 32))⟩ := rfl
  obtain ⟨who, _, hf⟩ := hblocking (1, 0) _ _ _ _ he (show 1 < 3 by decide) _
    (allocResult_witnessed L (disjoint h) (1, 0) he (by decide))
  obtain ⟨⟨g, k⟩, site, dst, bytes, _, hstore⟩ := AllocResultFill.written L hf
  rw [disjoint_get_eq] at hstore
  split_ifs at hstore
  all_goals rcases k with _ | _ | _ | k <;> simp [ev, barEv] at hstore

/-- The earlier requests of each warp, among the four. -/
private theorem disjoint_before {h : List Requests} {w : WarpRequest} {group : CtaGroup}
    (hv : w.Valid L (disjoint h) group) {r : Requests} (hr : r ∈ [c0, f0, c1, f1])
    (hb : w.Before r.own) : (r = f0 ∧ w = c0.own) ∨ (r = f1 ∧ w = c1.own) := by
  have hlt := hb.2.2 0
  have hc0 : w.cta = 0 := by
    have := hb.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simpa [c0, f0, c1, f1, req] using this
  have hev : w.event L 0 = (w.warp * 32, w.indices 0) := by
    simp [WarpRequest.event, L, hc0]
  have hget := hv.2.2.1 0
  rw [hev] at hget
  obtain ⟨-, hcase⟩ := disjoint_resource hget
  simp only at hcase
  have hext : ∀ r' ∈ [c0, f0, c1, f1], w.event L 0 = r'.own.event L 0 → w = r'.own :=
    fun r' hr' he => hv.ext (disjoint_valid h hr').2.2 he
  have hw := hb.2.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simp [c0, req] at hlt
  · simp only [f0, req] at hlt hw
    refine .inl ⟨rfl, hext c0 (by simp) ?_⟩
    rw [hev, hw]
    simp [WarpRequest.event, c0, req, L]
    omega
  · simp only [c1, req] at hlt hw
    rw [hw] at hcase
    omega
  · simp only [f1, req] at hlt hw
    refine .inr ⟨rfl, hext c1 (by simp) ?_⟩
    rw [hev, hw]
    rw [hw] at hcase
    simp [WarpRequest.event, c1, req, L]
    omega

/-- OBJ-TMEM-COMPLETION-PREFIX when a recorded deallocation's allocation is recorded. -/
private theorem disjoint_closed {h : List Requests} (hs : ∀ r ∈ h, r ∈ [c0, f0, c1, f1])
    (hf0 : f0 ∈ h → c0 ∈ h) (hf1 : f1 ∈ h → c1 ∈ h) : CompletionClosed L (disjoint h) := by
  rintro ws (⟨cta, r, hr, -, rfl⟩ | ⟨q, hq, -⟩) w hw w' group hv hb i hp
  · by_cases hc : cta = 0
    · subst hc
      change r ∈ h at hr
      rw [List.mem_singleton.mp hw] at hb
      rcases disjoint_before hv (hs r hr) hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact disjoint_covered (hf0 hr) rfl hp
      · exact disjoint_covered (hf1 hr) rfl hp
    · simp [disjoint, hc] at hr
  · cases hq

/-- The repaired history: warp 0's deallocation is performed by its return. -/
theorem repaired_histories : HistoriesOk L (disjoint [c0, f0, c1]) :=
  disjoint_histories (by simp) (by decide)

theorem repaired_coherent : ObjectCoherent L (disjoint [c0, f0, c1]) :=
  disjoint_coherent (by simp) (by simp [drank, c0, f0, c1, req])

theorem repaired_returnReady : DisjointReturnReady [c0, f0, c1] :=
  disjoint_returnReady (by simp) (by simp) (by simp)

theorem repaired_missing_publication : ¬ Tmem.Pair.Blocking L (disjoint [c0, f0, c1]) :=
  disjoint_missing_publication

theorem repaired_closed : CompletionClosed L (disjoint [c0, f0, c1]) :=
  disjoint_closed (by simp) (by simp) (by simp [f1, c0, f0, c1, req])

/-- From the repaired history, warp 1's deallocation can be performed: its earlier allocation is
complete, it is not yet recorded, and the replay accepts it. -/
theorem repaired_entry : CompletionReady L (disjoint [c0, f0, c1]) [f1.own] ∧
    (∀ x ∈ (disjoint [c0, f0, c1]).tmemHistory 0, x.own ≠ f1.own) ∧
    runRequests {} ((disjoint [c0, f0, c1]).tmemHistory 0 ++ [f1]) ≠ .blocked := by
  refine ⟨fun w hw w' group hv hb i hp => ?_, fun x hx hxo => ?_, by decide⟩
  · rw [List.mem_singleton.mp hw] at hb
    rcases disjoint_before hv (r := f1) (by simp) hb with ⟨h1, -⟩ | ⟨-, rfl⟩
    · simp [f0, f1, req] at h1
    · exact disjoint_covered (by simp) rfl hp
  · change x ∈ [c0, f0, c1] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [c0, f0, c1, f1, req] at hxo

/-- With all four records the resource history rules hold. -/
theorem complete_rules : HistoriesOk L (disjoint [c0, f0, c1, f1]) ∧
    ObjectCoherent L (disjoint [c0, f0, c1, f1]) ∧
    DisjointReturnReady [c0, f0, c1, f1] ∧
    CompletionClosed L (disjoint [c0, f0, c1, f1]) :=
  ⟨disjoint_histories (by simp) (by decide),
    disjoint_coherent (by simp) (by simp [drank, c0, f0, c1, f1, req]),
    disjoint_returnReady (by simp) (by simp) (by simp),
    disjoint_closed (by simp) (by simp) (by simp)⟩

/-- With all four records every operation is complete and every allocation is released. -/
theorem complete_drained : Drained L (disjoint [c0, f0, c1, f1]) ∧
    Released (disjoint [c0, f0, c1, f1]) := by
  refine ⟨fun i pc group dst request he => ?_, fun cta st hst => ?_⟩
  · obtain ⟨-, hcase⟩ := disjoint_resource he
    rcases hcase with ⟨hg, hk, -⟩ | ⟨hg, hk, -⟩ | ⟨hg, hg', hk, -⟩ | ⟨hg, hg', hk, -⟩
    · exact disjoint_covered (r := c0) (by simp) rfl
        (participates_of (by simp) (by simp [c0, req]; omega) (by omega) (by simp [hk, c0, req]))
    · exact disjoint_covered (r := f0) (by simp) rfl
        (participates_of (by simp) (by simp [f0, req]; omega) (by omega) (by simp [hk, f0, req]))
    · exact disjoint_covered (r := c1) (by simp) rfl
        (participates_of (by simp) (by simp [c1, req]; omega) (by omega) (by simp [hk, c1, req]))
    · exact disjoint_covered (r := f1) (by simp) rfl
        (participates_of (by simp) (by simp [f1, req]; omega) (by omega) (by simp [hk, f1, req]))
  · by_cases hc : cta = 0
    · subst hc
      change runRequests {} [c0, f0, c1, f1] = _ at hst
      have : runRequests {} [c0, f0, c1, f1] =
          .done { previousColumns := some 32, nextLifetime := 2 } := by decide
      rw [this] at hst
      cases hst
      rfl
    · simp only [disjoint, hc, ite_false, runRequests] at hst
      cases hst
      rfl

end
end PTX.Tests.TmemPairOrder
