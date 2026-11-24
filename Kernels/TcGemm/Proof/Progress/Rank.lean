-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TcGemm.Proof.NoBarArrive
public import Kernels.TcGemm.Proof.MemoryFacts
public import Lemmas.Kernel.Next
public import Lemmas.Kernel.MbarBulk

@[expose] public section

/-! # `tc_gemm` progress: ranks and the last event of a thread

A pending thread ranks by the virtual time of its machine's state after its last event
(`timeOf`, `Site.time`): it increases along the program, and a stopped machine has time 0. An
uncovered allocator operation ranks above every thread (`rank`); the other asynchronous
obligations are closed outright.

The last event of a launched thread with events, in an execution without undefined behaviour,
was fired from a followed state, whose successor along it is the state after it (`last_info`).
Only a first or second barrier, an allocation, a load from Tensor Memory, its wait and the
deallocation can block their thread (`Site.blocks`); after any other event the thread is
released (`released_of_quiet`, `quiet_of_site`). A thread whose time exceeds a threshold
crossed it at one event (`crossing`): the first barrier past time 9, the commit past 13 (for
thread 0), the load past 16, its wait past 17, the second barrier past 27 and warp 0's
deallocation past 29 (`cross_9`, …, `cross_29`). -/

namespace PTX.Kernels.TcGemm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The virtual time of a site, increasing along the program. -/
def Site.time : Site → Nat
  | .alloc => 1 | .allocSt => 2 | .init0 => 3 | .init1 => 4 | .fence => 5 | .arrive => 6
  | .bulkA => 7 | .bulkB => 8 | .bar0 _ => 9 | .load _ => 10 | .wait0 => 11 | .mma => 12
  | .commit => 13 | .wait1 => 14 | .fence1 => 15 | .ld => 16 | .waitLd => 17
  | .st j => 18 + min j 7 | .fenceB => 26 | .bar1 => 27 | .fence2 => 28 | .dealloc => 29
  | .exit => 30

/-- The virtual time of thread `g` after its last event: its machine's site, `0` once the
machine stopped. -/
def timeOf (L : Launch) (A B D : Nat) (X : Execution) (g : Nat) : Nat :=
  match stateAt L A B D X g (X.tr g).length with
  | some (some d) => d.site.time
  | _ => 0

/-- The rank of an obligation: a thread's time; an allocator operation above every thread. -/
def rank (L : Launch) (A B D : Nat) (X : Execution) : Descent.Obligation → Nat
  | .thread g => timeOf L A B D X g
  | .tmem => 100
  | _ => 0

/-- The sites that can block their thread after their event. -/
def Site.blocks : Site → Bool
  | .bar0 _ | .bar1 | .alloc | .ld | .waitLd | .dealloc => true
  | _ => false

theorem Site.time_le (s : Site) : s.time ≤ 30 := by
  cases s <;> simp only [Site.time] <;> omega

variable {L : Launch} {A B D : Nat} {a b : Nat → Nat → Int} {mem0 : Mem0} {X : Execution}
  {P : Nat → Par} {m : Nat → Nat} {u : Nat → List Event}

theorem timeOf_le (g : Nat) : timeOf L A B D X g ≤ 30 := by
  unfold timeOf
  split
  · exact Site.time_le _
  · omega

theorem timeOf_of {g : Nat} {d : ThreadD}
    (hσ : stateAt L A B D X g (X.tr g).length = some (some d)) :
    timeOf L A B D X g = d.site.time := by
  unfold timeOf
  rw [hσ]

/-- The time of a thread depends only on its trace. -/
theorem timeOf_congr {Y : Execution} (h : Y.tr = X.tr) (g : Nat) :
    timeOf L A B D Y g = timeOf L A B D X g := by
  simp only [timeOf, stateAt, Frame.stateAt, h]

/-- The kernel has no assumptions. -/
theorem wfFree : Assumption.WfFree L mem0 ([] : List Assumption) := fun _ ha => by cases ha

/-! ### An execution's threads -/

section
variable (hW : Wit A B D L.sharedBase X P m u)
include hW

/-- Every thread may perform its first event: no cancellation request exists. -/
theorem launched (g : Nat) : Step.Launched L X g :=
  fun ⟨_, _, _, hi⟩ => (hW.no_clc hi).elim

/-- No write releases. -/
theorem no_release {e : EvId} {pc : Nat} {a' : Acc} {bs : List Byte}
    (he : X.get e = some ⟨pc, .wr a' bs⟩) : a'.release = false := by
  obtain ⟨g, j⟩ := e
  obtain ⟨-, -, h⟩ := hW.writes he
  rcases h with ⟨-, -, rfl, -⟩ | ⟨k, -, -, rfl, -⟩ <;> rfl

theorem not_canceled (hX : Consistent L kernel [] mem0 X) {g : Nat} : ¬ ClcCanceled L X g := by
  rintro ⟨-, req, ho⟩
  obtain ⟨i, s, targets, -, hi, -⟩ := ClcOk.canceled_has_issue hX.clc ho
  exact hW.no_clc hi

/-- **Synchronization is guarded**: the polls are canonical spins (`spins`), no write releases,
the kernel has no thread fence and no record faults. -/
theorem syncGuarded (hpre : Pre L A B D a b mem0) (hX : Consistent L kernel [] mem0 X) :
    SyncGuarded L kernel X :=
  ⟨fun ⟨_, _⟩ _ _ _ _ _ he => spins (hW.wait_pc he),
    fun e f => ⟨(fun ⟨a', b', bs, cs, hw, _, hrel, _⟩ => by
        rcases hW.memWrites hw with ⟨_, rfl, -⟩ | ⟨g, -, k, -, -, rfl, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · cases hrel
        · cases hrel
        · cases h
        · cases h),
      not_fenceSync_of_noFence (fun ⟨_, _⟩ _ _ ⟨_, h⟩ => hW.no_threadFence h) e f⟩,
    fun _ _ _ _ _ hr _ _ _ => object_fault_free hpre hX hW (List.mem_of_getElem? hr)⟩

/-- A thread is released when its last event does not block: no barrier, group wait or
warp-collective `tcgen05` event. -/
theorem released_of_quiet {g : Nat}
    (hlast : ∀ e, X.get (g, (X.tr g).length - 1) = some e → e.kind.resume ≠ .blocking false) :
    Step.Released L X g :=
  hW.tcBulk.released (fun _ _ _ _ hb => (hlast _ hb rfl).elim)
    (fun _ _ h hk => by
      rcases hk with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact (hlast _ h rfl).elim)
    (fun _ _ h hres => (hlast _ h hres).elim)

end

/-- The event of a site that does not block is no barrier and no warp-collective `tcgen05`
event. -/
theorem quiet_of_site {g : Nat} {d : ThreadD} {e : Event} (hev : SiteEvent L A B D g d e)
    (hb : d.site.blocks = false) : e.kind.resume ≠ .blocking false := by
  obtain ⟨site, c, vals⟩ := d
  cases site <;> simp only [Site.blocks, Bool.true_eq_false] at hb <;>
    simp only [SiteEvent] at hev
  all_goals first
    | (subst hev; exact fun h => by cases h)
    | (rcases hev with ⟨-, rfl⟩ | ⟨-, _, rfl⟩ <;> exact fun h => by cases h)
    | (obtain ⟨_, rfl⟩ := hev; exact fun h => by cases h)
    | (obtain ⟨_, _, rfl⟩ := hev; exact fun h => by cases h)

/-! ### The last event -/

section
variable (ht : ThreadFacts L A B D X) (hX : Consistent L kernel [] mem0 X) (hub : ¬ HasUb X)
include ht hX hub

/-- **The last event of a thread** was fired from a followed state; the state after it is that
state's successor along it. -/
theorem last_info {g : Nat} (hg : g < L.threads) (hlen : 0 < (X.tr g).length) :
    ∃ d e, stateAt L A B D X g ((X.tr g).length - 1) = some (some d) ∧
      X.get (g, (X.tr g).length - 1) = some e ∧ SiteEvent L A B D g d e ∧
      stateAt L A B D X g (X.tr g).length = next g d e := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, (X.tr g).length - 1) = some e :=
    ⟨_, List.getElem?_eq_getElem (l := X.tr g) (by omega)⟩
  obtain ⟨d, hd⟩ := Frame.state_of_noUb ht.sound hX ht.tracked hub he
  refine ⟨d, e, hd, he, ht.event hg he hd, ?_⟩
  have h := Frame.stateAt_succ (C := code L A B D) (X := X) (g := g) (k := (X.tr g).length - 1) he
  rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega] at h
  change Frame.stateAt (code L A B D) X g _ = _
  rw [h]
  change Frame.stateAt (code L A B D) X g _ = some (some d) at hd
  rw [hd]
  rfl

/-- A thread whose last event's site does not block is released. -/
theorem released_of_site (hW : Wit A B D L.sharedBase X P m u) {g : Nat} (hg : g < L.threads)
    (h : ∀ d e, 0 < (X.tr g).length →
      stateAt L A B D X g ((X.tr g).length - 1) = some (some d) →
      X.get (g, (X.tr g).length - 1) = some e → SiteEvent L A B D g d e → d.site.blocks = false) :
    Step.Released L X g := by
  refine released_of_quiet hW fun e he => ?_
  have hlen : 0 < (X.tr g).length := by
    rcases Nat.eq_zero_or_pos (X.tr g).length with h0 | h0
    · simp [Execution.get, List.length_eq_zero_iff.mp h0] at he
    · exact h0
  obtain ⟨d, e', hd, he', hev, -⟩ := last_info ht hX hub hg hlen
  rw [he] at he'
  cases he'
  exact quiet_of_site hev (h d e hlen hd he hev)

omit hX hub in
/-- **A thread past a time crossed it at one event**: at a followed state of time at most `T`,
whose successor along its event has time above `T`. -/
theorem crossing {g : Nat} (hg : g < L.threads) {T : Nat} (hT9 : 9 ≤ T)
    (hT : T < timeOf L A B D X g) :
    ∃ k d e d', k < (X.tr g).length ∧ stateAt L A B D X g k = some (some d) ∧
      X.get (g, k) = some e ∧ SiteEvent L A B D g d e ∧ next g d e = some (some d') ∧
      d.site.time ≤ T ∧ T < d'.site.time := by
  classical
  have hex : ∃ k, ∃ d, stateAt L A B D X g k = some (some d) ∧ T < d.site.time := by
    unfold timeOf at hT
    split at hT
    · rename_i d hd
      exact ⟨_, d, hd, hT⟩
    · omega
  obtain ⟨k0, ⟨d', hd', hT'⟩, hmin⟩ : ∃ k0, (∃ d, stateAt L A B D X g k0 = some (some d) ∧
      T < d.site.time) ∧ ∀ k < k0, ¬ ∃ d, stateAt L A B D X g k = some (some d) ∧
        T < d.site.time :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  rcases k0 with _ | k
  · have h0 : stateAt L A B D X g 0 = some (some (code L A B D g).init) := Frame.stateAt_zero
    rw [h0] at hd'
    obtain rfl := Option.some.inj (Option.some.inj hd')
    simp only [code] at hT'
    split at hT' <;> simp [Site.time] at hT' <;> omega
  · have hk := hmin k (by omega)
    cases hs : stateAt L A B D X g k with
    | none =>
      have := Frame.stateAt_none_mono (C := code L A B D) hs (n := k + 1) (by omega)
      change stateAt L A B D X g (k + 1) = none at this
      rw [this] at hd'
      cases hd'
    | some σ =>
      cases σ with
      | none => exact absurd hs (ht.tracked g k hg)
      | some d =>
        have hlt : k < (X.tr g).length := by
          by_contra hge
          have h1 : stateAt L A B D X g (k + 1) = stateAt L A B D X g k := by
            change Frame.stateAt _ X g _ = Frame.stateAt _ X g _
            rw [Frame.stateAt_of_le (k := k + 1) (by omega),
              Frame.stateAt_of_le (k := k) (by omega)]
          rw [h1, hs] at hd'
          obtain rfl := Option.some.inj (Option.some.inj hd')
          exact hk ⟨_, hs, hT'⟩
        obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
        have h := Frame.stateAt_succ (C := code L A B D) (X := X) (g := g) (k := k) he
        change Frame.stateAt (code L A B D) X g k = some (some d) at hs
        rw [hs] at h
        change stateAt L A B D X g (k + 1) = next g d e at h
        rw [h] at hd'
        refine ⟨k, d, e, d', hlt, hs, he, ht.event hg he hs, hd', ?_, hT'⟩
        by_contra hgt
        exact hk ⟨d, hs, by omega⟩

end

/-! ### The events crossing a time -/

section
variable {g : Nat} {d d' : ThreadD} {e : Event} (hev : SiteEvent L A B D g d e)
  (hn : next g d e = some (some d'))
include hev hn

/-- Along an event, the time grows by one or stays (a failed poll); it jumps only from the
allocation to the first barrier, from the address read of a thread other than thread 0 to the
polls of `bar1`, and past the deallocation of a thread outside warp 0. -/
theorem time_step : d'.site.time = d.site.time + 1 ∨ d'.site.time = d.site.time ∨
    (d.site = .alloc ∧ d'.site.time = 9) ∨ (d.site = .load false ∧ d'.site.time = 14) ∨
    (d.site = .fence2 ∧ d'.site.time = 30) := by
  obtain ⟨site, c, vals⟩ := d
  obtain ⟨site', c', vals'⟩ := d'
  have key : ∀ s, some (some (⟨s, c, vals⟩ : ThreadD)) = some (some ⟨site', c', vals'⟩) →
      site' = s := fun s h => by
    simp only [Option.some.injEq, ThreadD.mk.injEq] at h
    exact h.1.symm
  cases site with
  | alloc =>
    simp only [next] at hn
    rw [key _ hn]
    split <;> simp [Site.time]
  | load z =>
    simp only [SiteEvent] at hev
    obtain ⟨bs, -, rfl⟩ := hev
    simp only [next, rdE, Option.map_eq_some_iff] at hn
    obtain ⟨c2, -, h⟩ := hn
    simp only [Option.some.injEq, ThreadD.mk.injEq] at h
    rw [← h.1]
    cases z <;> simp [Site.time]
  | wait0 =>
    simp only [SiteEvent] at hev
    obtain ⟨ok, rfl⟩ := hev
    simp only [next, wait0E] at hn
    rw [key _ hn]
    cases ok <;> simp [Site.time]
  | wait1 =>
    simp only [SiteEvent] at hev
    obtain ⟨ok, rfl⟩ := hev
    simp only [next, wait1E] at hn
    rw [key _ hn]
    cases ok <;> simp [Site.time]
  | ld =>
    simp only [SiteEvent] at hev
    obtain ⟨vs, -, rfl⟩ := hev
    simp only [next, ldE, Option.some.injEq, ThreadD.mk.injEq] at hn
    rw [← hn.1]
    simp [Site.time]
  | st j =>
    simp only [SiteEvent] at hev
    rcases hev with ⟨-, rfl⟩ | ⟨-, f, rfl⟩
    · simp only [next, stE] at hn
      rw [key _ hn]
      split <;> simp [Site.time] <;> omega
    · simp [next] at hn
  | fence2 =>
    simp only [next] at hn
    rw [key _ hn]
    split <;> simp [Site.time]
  | exit => simp [next] at hn
  | _ => simp only [next] at hn; rw [key _ hn]; simp [Site.time]

/-- At a crossing of a time, the event's site has that time, or the event jumps over it. -/
theorem cross_at {T : Nat} (hT : 9 ≤ T) (h1 : d.site.time ≤ T) (h2 : T < d'.site.time) :
    d.site.time = T ∨ (d.site = .load false ∧ T < 14) ∨ (d.site = .fence2 ∧ 28 ≤ T) := by
  rcases time_step hev hn with h | h | ⟨-, h⟩ | ⟨hs, h⟩ | ⟨hs, h⟩
  · exact .inl (by omega)
  · omega
  · omega
  · refine .inr (.inl ⟨hs, by omega⟩)
  · refine .inr (.inr ⟨hs, ?_⟩)
    rw [hs] at h1
    simpa only [Site.time] using h1

theorem cross_9 (h1 : d.site.time ≤ 9) (h2 : 9 < d'.site.time) : e = bar0E := by
  rcases cross_at hev hn le_rfl h1 h2 with h | ⟨hs, -⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · rw [hs] at h1; simp [Site.time] at h1
  · omega

theorem cross_13 (hz : d.site ≠ .load false) (h1 : d.site.time ≤ 13) (h2 : 13 < d'.site.time) :
    e = commitE L.sharedBase := by
  rcases cross_at hev hn (by decide) h1 h2 with h | ⟨hs, -⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · exact (hz hs).elim
  · omega

theorem cross_16 (h1 : d.site.time ≤ 16) (h2 : 16 < d'.site.time) :
    ∃ vals, vals.length = 8 ∧ e = ldE g d.c vals := by
  rcases cross_at hev hn (by decide) h1 h2 with h | ⟨hs, h⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · omega
  · omega

theorem cross_17 (h1 : d.site.time ≤ 17) (h2 : 17 < d'.site.time) : e = wldE := by
  rcases cross_at hev hn (by decide) h1 h2 with h | ⟨hs, h⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · omega
  · omega

theorem cross_27 (h1 : d.site.time ≤ 27) (h2 : 27 < d'.site.time) : e = bar1E := by
  rcases cross_at hev hn (by decide) h1 h2 with h | ⟨hs, h⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · omega
  · omega

/-- Past time 29 a thread of warp 0 deallocated. -/
theorem cross_29 (hg : g / 32 = 0) (h1 : d.site.time ≤ 29) (h2 : 29 < d'.site.time) :
    e = deallocE d.c := by
  rcases cross_at hev hn (by decide) h1 h2 with h | ⟨hs, h⟩ | ⟨hs, h⟩
  · obtain ⟨site, c, vals⟩ := d
    cases site <;> simp only [Site.time] at h <;> first | omega | exact hev
  · omega
  · obtain ⟨site, c, vals⟩ := d
    obtain ⟨site', c', vals'⟩ := d'
    simp only at hs
    subst hs
    simp only [next, hg, ↓reduceIte, Option.some.injEq, ThreadD.mk.injEq] at hn
    rw [← hn.1] at h2
    simp [Site.time] at h2

end

end

end PTX.Kernels.TcGemm.Proof
