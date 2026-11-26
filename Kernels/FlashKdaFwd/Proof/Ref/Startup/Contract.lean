-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Exports
public import Kernels.FlashKdaFwd.Proof.Protocol.Export
public import Lemmas.Flow.RunInv

@[expose] public section

/-! # The startup exports in the vocabulary of the protocol layer

The protocol layer (`Proof/Protocol/`) names the eleven mbarriers of a thread block (`Bar`),
their locations, counts, owners and the `bar.sync 0` that publishes each (`Bar.loc`,
`Bar.count`, `Bar.owner`, `Bar.gen`), and counts barrier events with `bar0Before`. This file
restates exports of `Startup/Exports.lean` in that vocabulary, for the events of the startup
phase: each theorem is the statement of one field of a contract structure of the protocol layer
for an event fired at a followed state, with the second alternative `Left P L X g k` ("the
thread has left the startup phase": the event belongs to a later phase, whose share covers it).

Fields of `Protocol.InitFacts`:

* `init_ev_startup`: `init_ev` (all eleven initializations are in the phase). `barOf j` is the
  barrier that the `j`-th `mbarrier.init` site initializes, `siteOf b` the site of barrier `b`.
* `init_once_startup`: `init_once` (two initializations of one location are at one position).
* `init_done_startup`: `init_done` (at the `bar.sync 0` that publishes a barrier, its owner has
  initialized it: `init_before` finds the earlier event from the ledger's count).
* `use_ev_startup`: `use_ev` (the arrival and the 16 loads are the load leader's, after its
  initialization of the state barrier; the poll is after three `bar.sync 0`).

`Protocol.BarFacts`: `bar_ev_startup` (`shape` and `bar0_pc`).

`Protocol.StateFacts`: `state_arrive_startup` (`arrive`), `state_issue_startup` (`issue`:
4096 bytes, fewer than 16 predecessors), `state_poll_startup` (`poll`). The counts by object
(`arrivals m`, `okPolls m`, `issuesTo m`) are read off the ledger's counts by kind
(`arrivals_zero`, `okPolls_zero`, `issues_state`).

`Protocol.LifeFacts`: `state_polled_startup` (`state_polled`; no alternative: a thread that
exits has left the phase, and `Left.statePolled` says that a thread that has left the phase has
polled the state barrier of its block successfully; the later phases can use that lemma for
the same conjunct of `UnionFacts.thread` and `UnionFacts.store`).

`Protocol.UnionFacts`: `union_load_startup` (`load`, class `init`): a load of the phase that
writes a byte of the union region completes on the state barrier, and with `q` earlier loads
on that barrier it writes block `q`; `stateBlock P l` is the owner function for these bytes
(`Owners.block`): the index of the 4096-byte block of the state buffer that holds byte `l`.

`state_issue_spec`: the load with `q` earlier loads on the state barrier is the copy
`stateSpec P L g q` (for the layer that derives the content of the state buffer). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Protocol
open PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- The barrier initialized at the `j`-th `mbarrier.init` site: the load pipeline's full and
empty barriers of stage 0, 1, 2 (instructions 69 to 80), the store pipeline's (101 to 108),
the state barrier (324). -/
def barOf (j : Fin 11) : Bar :=
  match j.val with
  | 0 => .loadFull 0
  | 1 => .loadEmpty 0
  | 2 => .loadFull 1
  | 3 => .loadEmpty 1
  | 4 => .loadFull 2
  | 5 => .loadEmpty 2
  | 6 => .storeFull 0
  | 7 => .storeEmpty 0
  | 8 => .storeFull 1
  | 9 => .storeEmpty 1
  | _ => .state

theorem barOf_off (j : Fin 11) : (barOf j).off = initOff j.val := by
  fin_cases j <;> rfl

theorem barOf_count (j : Fin 11) : (barOf j).count = initCnt j.val := by
  fin_cases j <;> rfl

theorem barOf_gen (g : Nat) (j : Fin 11) : (barOf j).gen = (led g (.init j)).bars := by
  fin_cases j <;> rfl

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The owner of the barrier of site `j` is the thread the invariant places there. -/
theorem barOf_owner (hb : L.block = 192) (j : Fin 11)
    (ht : tid g = if j.val < 10 then 0 else 128) : g = (barOf j).owner L (g / L.block) := by
  unfold tid at ht
  fin_cases j <;>
    simp [barOf, Bar.owner, initLeader, loadLeader, thr, hb] at ht ⊢ <;> omega

/-- **`Protocol.InitFacts.init_ev` for the startup phase**: an initialization is the owner's,
of a barrier of its block, with the barrier's count, after the barrier's number of
`bar.sync 0`. -/
theorem init_ev_startup (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    {k pc n : Nat} {m : Loc} {s : D} (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ b : Bar, m = b.loc L (g / L.block) ∧ n = b.count ∧ g = b.owner L (g / L.block) ∧
      bar0Before X (g, k) = b.gen) ∨ Left P L X g k := by
  rcases mbInit_startup hpre hX hg he hσ with ⟨j, -, rfl, rfl, ht, hl⟩ | h
  · refine .inl ⟨barOf j, ?_, (barOf_count j).symm, barOf_owner hpre.block j ht, ?_⟩
    · simp only [Bar.loc, hpre.sharedBase, barOf_off]
    · rw [barOf_gen g j, ← hl]
      rfl
  · exact .inr h

/-- No arrival at all is no arrival on `m`. -/
theorem arrivals_zero {m : Loc} {es : List Event} (h : es.countP isArr = 0) :
    arrivals m es = 0 := by
  have h' := List.countP_eq_zero.mp h
  refine List.countP_eq_zero.mpr fun a ha hon => h' a ha ?_
  obtain ⟨tx, c, rel, sc, hk⟩ := arrivesOn_form hon
  simp [isArr, hk]

/-- No successful poll at all is no successful poll of `m`. -/
theorem okPolls_zero {m : Loc} {es : List Event} (h : es.countP isOkPoll = 0) :
    okPolls m es = 0 := by
  have h' := List.countP_eq_zero.mp h
  refine List.countP_eq_zero.mpr fun a ha hon => h' a ha ?_
  obtain ⟨q, acq, sc, hk⟩ := okPoll_wait_form hon
  simp [isOkPoll, hk]

/-! ### Events of a prefix -/

/-- An element of a prefix of the trace is an earlier event of the thread. -/
theorem mem_take {k : Nat} {x : Event} (h : x ∈ (X.tr g).take k) :
    ∃ i < k, X.get (g, i) = some x := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  have h1 : ((X.tr g).take k).length ≤ k := List.length_take_le _ _
  have h2 : ((X.tr g).take k).length ≤ (X.tr g).length := List.length_take_le' _ _
  refine ⟨i, by omega, ?_⟩
  rw [List.getElem_take]
  show (X.tr g)[i]? = _
  exact List.getElem?_eq_getElem (by omega)

/-- An earlier event of the thread is an element of the prefix. -/
theorem get_mem_take {i k : Nat} {x : Event} (h : X.get (g, i) = some x) (hik : i < k) :
    x ∈ (X.tr g).take k :=
  List.mem_of_getElem? (i := i) (by rw [List.getElem?_take_of_lt hik]; exact h)

theorem led_init_inits (j : Fin 11) :
    (led g (.init j)).inits = if j.val < 10 then j.val else 0 := by
  fin_cases j <;> rfl

theorem led_bar_bars (j : Fin 3) : (led g (.bar j)).bars = j.val := by
  fin_cases j <;> rfl

/-- The eleven barriers are at different offsets. -/
theorem initOff_inj : ∀ {j j' : Fin 11}, initOff j.val = initOff j'.val → j = j' := by
  decide

/-- The `mbarrier.init` site of a barrier (the inverse of `barOf`). -/
def siteOf : Bar → Fin 11
  | .loadFull s => ⟨2 * s.val, by omega⟩
  | .loadEmpty s => ⟨2 * s.val + 1, by omega⟩
  | .storeFull o => ⟨6 + 2 * o.val, by omega⟩
  | .storeEmpty o => ⟨7 + 2 * o.val, by omega⟩
  | .state => 10

theorem barOf_siteOf (b : Bar) : barOf (siteOf b) = b := by
  cases b with
  | loadFull s => fin_cases s <;> rfl
  | loadEmpty s => fin_cases s <;> rfl
  | storeFull o => fin_cases o <;> rfl
  | storeEmpty o => fin_cases o <;> rfl
  | state => rfl

/-- The owner of a barrier has initialized it before the `bar.sync 0` that publishes it. -/
theorem init_lt_bar {q : Fin 11} {j : Fin 3} (ht : tid g = if q.val < 10 then 0 else 128)
    (hb : (led g (.init q)).bars = j.val) :
    (led g (.init q)).inits < (led g (.bar j)).inits := by
  fin_cases q <;> fin_cases j <;> simp [led] at ht hb ⊢ <;> simp [ht]

/-- An issue on a barrier is an issue. -/
theorem issuesTo_isIssue {m : Loc} {x : Event} (h : issuesTo m x = true) : isIssue x = true := by
  obtain ⟨pc, kd⟩ := x
  cases kd <;> first | rfl | cases h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **`Protocol.BarFacts.shape` and `bar0_pc` for the startup phase**: a barrier event is
`bar.sync 0`, at the position of its ordinal among the thread's `bar.sync 0`. -/
theorem bar_ev_startup {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (mode = .sync ∧ id = 0 ∧ cnt = none ∧ bar0Pcs[bar0Before X (g, k)]? = some pc) ∨
      Left P L X g k := by
  rcases bar_startup hpre hX hg he hσ with ⟨rfl, rfl, rfl, j, rfl, hj⟩ | h
  · refine .inl ⟨rfl, rfl, rfl, ?_⟩
    have hb : bar0Before X (g, k) = j.val := hj
    rw [hb]
    fin_cases j <;> rfl
  · exact .inr h

/-- **`Protocol.StateFacts.arrive` for the startup phase**: an arrival on the state barrier
is the load leader's first, releasing, expecting 65536 bytes with count 1. -/
theorem state_arrive_startup {i pc tx cnt c : Nat} {rel : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, i) = some ⟨pc, .arrive (Bar.state.loc L c) tx cnt rel sc⟩)
    (hσ : Frame.stateAt (code L) X g i = some (some s)) :
    (g = loadLeader L c ∧ tx = 65536 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (Bar.state.loc L c) ((X.tr g).take i) = 0) ∨ Left P L X g i := by
  rcases arrive_startup hpre hX hg he hσ with ⟨-, hm, rfl, rfl, rfl, -, ht, hl⟩ | h
  · have hc : c = g / L.block := congrArg Loc.cta hm
    have hb := hpre.block
    refine .inl ⟨?_, rfl, rfl, rfl, arrivals_zero (congrArg Led.arrs hl)⟩
    unfold tid at ht
    simp only [loadLeader, thr, hc, hb]
    omega
  · exact .inr h

/-- **`Protocol.StateFacts.poll` for the startup phase**: a poll of the state barrier names
the barrier of the thread's own block, has parity 0, and a successful one acquires and is the
thread's first. -/
theorem state_poll_startup {i pc q c : Nat} {ok acq : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, i) = some ⟨pc, .wait (Bar.state.loc L c) q ok acq sc⟩)
    (hσ : Frame.stateAt (code L) X g i = some (some s)) :
    (c = g / L.block ∧ q % 2 = 0 ∧
      (ok = true → acq = true ∧ okPolls (Bar.state.loc L c) ((X.tr g).take i) = 0)) ∨
      Left P L X g i := by
  rcases wait_startup hpre hX hg he hσ with ⟨-, hm, rfl, rfl, -, -, hp⟩ | h
  · exact .inl ⟨congrArg Loc.cta hm, rfl, fun _ => ⟨rfl, okPolls_zero hp⟩⟩
  · exact .inr h

/-! ### `InitFacts`: `init_once`, `init_done`, `use_ev` -/

/-- **`Protocol.InitFacts.init_once` for the startup phase**: two initializations of one
location by one thread are one event. -/
theorem init_once_startup {k k' pc pc' n n' : Nat} {m : Loc} {s s' : D}
    (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩)
    (he' : X.get (g, k') = some ⟨pc', .mbInit m n'⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hσ' : Frame.stateAt (code L) X g k' = some (some s')) :
    k = k' ∨ Left P L X g k ∨ Left P L X g k' := by
  rcases mbInit_startup hpre hX hg he hσ with ⟨j, -, hm, -, -, hl⟩ | h
  · rcases mbInit_startup hpre hX hg he' hσ' with ⟨j', -, hm', -, -, hl'⟩ | h'
    · have hj : j = j' := initOff_inj (by
        have := hm.symm.trans hm'
        simp only [Loc.mk.injEq, true_and] at this
        omega)
      subst hj
      exact .inl (eq_of_count_eq isInit (X.tr g) he rfl he' rfl
        ((congrArg Led.inits hl).trans (congrArg Led.inits hl').symm))
    · exact .inr (.inr h')
  · exact .inr (.inl h)

/-- **The initialization of the barrier of site `q`, from the ledger**: a thread of the role
that initializes site `q`, with more initializations behind it than the position of site `q`
has before it, has initialized that barrier. -/
theorem init_before {k : Nat} {s : D} (q : Fin 11)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hq : tid g = if q.val < 10 then 0 else 128)
    (hcnt : (led g (.init q)).inits < ((X.tr g).take k).countP isInit) :
    (∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj,
        .mbInit ⟨.shared, g / L.block, P.sharedBase + initOff q.val⟩ (initCnt q.val)⟩) ∨
      Left P L X g k := by
  obtain ⟨i, hi, x, hx, hxi, hc⟩ := exists_nth isInit (X.tr g) hcnt
  obtain ⟨pcj, kd⟩ := x
  obtain ⟨m', n', rfl⟩ : ∃ m' n', kd = .mbInit m' n' := by
    cases kd <;> first | exact ⟨_, _, rfl⟩ | cases hxi
  obtain ⟨si, hσi⟩ := followed_of_le hσ (show i ≤ k by omega)
  rcases mbInit_startup hpre hX hg hx hσi with ⟨j', -, rfl, rfl, ht, hl⟩ | h
  · have hin : (led g (.init j')).inits = (led g (.init q)).inits :=
      (congrArg Led.inits hl).symm.trans hc
    rw [led_init_inits, led_init_inits] at hin
    have hjq : j' = q := by
      apply Fin.ext
      rw [hq] at ht
      have := j'.isLt
      have := q.isLt
      split_ifs at ht hin <;> omega
    subst hjq
    exact .inl ⟨i, pcj, hi, hx⟩
  · exact .inr (h.mono (by omega))

omit hX hg in
/-- The location and the count of a barrier, in the closed form of its site. -/
theorem bar_loc_count (b : Bar) (c : Nat) :
    b.loc L c = ⟨.shared, c, P.sharedBase + initOff (siteOf b).val⟩ ∧
      b.count = initCnt (siteOf b).val := by
  have h1 := barOf_off (siteOf b)
  have h2 := barOf_count (siteOf b)
  rw [barOf_siteOf] at h1 h2
  exact ⟨by simp only [Bar.loc, hpre.sharedBase, h1], h2⟩

omit hX hg in
/-- The owner of a barrier is thread 0 of its block (the ten pipeline barriers) or thread
128 (the state barrier). -/
theorem tid_owner (b : Bar) {c : Nat} (hgb : g = b.owner L c) :
    tid g = (if (siteOf b).val < 10 then 0 else 128) ∧ g / L.block = c := by
  have hb := hpre.block
  subst hgb
  refine ⟨?_, Bar.owner_div hb b⟩
  unfold tid
  cases b with
  | loadFull x =>
    have := x.isLt
    show (c * L.block + 0) % 192 = if 2 * x.val < 10 then 0 else 128
    rw [ite_eq_left (by omega), hb]
    omega
  | loadEmpty x =>
    have := x.isLt
    show (c * L.block + 0) % 192 = if 2 * x.val + 1 < 10 then 0 else 128
    rw [ite_eq_left (by omega), hb]
    omega
  | storeFull x =>
    have := x.isLt
    show (c * L.block + 0) % 192 = if 6 + 2 * x.val < 10 then 0 else 128
    rw [ite_eq_left (by omega), hb]
    omega
  | storeEmpty x =>
    have := x.isLt
    show (c * L.block + 0) % 192 = if 7 + 2 * x.val < 10 then 0 else 128
    rw [ite_eq_left (by omega), hb]
    omega
  | state =>
    show (c * L.block + 128) % 192 = 128
    rw [hb]
    omega

/-- **`Protocol.InitFacts.init_done` for the startup phase**: at the `bar.sync 0` that
publishes a barrier, the barrier's owner has initialized it. -/
theorem init_done_startup {c k pc : Nat} {cnt : Option Nat} {mode : BarMode} {s : D} (b : Bar)
    (hgb : g = b.owner L c) (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hb : bar0Before X (g, k) = b.gen)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj, .mbInit (b.loc L c) b.count⟩) ∨
      Left P L X g k := by
  obtain ⟨ht, hc⟩ := tid_owner hpre b hgb
  obtain ⟨hloc, hcount⟩ := bar_loc_count hpre b c
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
    have hbars : (led g (.init (siteOf b))).bars = j.val := by
      have h1 : bar0Before X (g, k) = (led g (.bar j)).bars := congrArg Led.bars hl
      have h2 := barOf_gen g (siteOf b)
      rw [barOf_siteOf] at h2
      rw [← h2, ← hb, h1, led_bar_bars]
    have hcnt : (led g (.init (siteOf b))).inits < ((X.tr g).take k).countP isInit := by
      have h1 : ((X.tr g).take k).countP isInit = (led g (.bar j)).inits :=
        congrArg Led.inits hl
      rw [h1]
      exact init_lt_bar ht hbars
    rw [hloc, hcount, ← hc]
    exact init_before hpre hX hg (siteOf b) hσ ht hcnt
  · exact .inr h

/-- The load leader at a position after its initialization of the state barrier: it owns the
barrier and has initialized it. -/
theorem state_owner_init {k : Nat} {s : D}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (ht : tid g = 128)
    (hcnt : 0 < ((X.tr g).take k).countP isInit) :
    (g = Bar.state.owner L (g / L.block) ∧ ∃ j pcj, j < k ∧
      X.get (g, j) = some ⟨pcj, .mbInit (Bar.state.loc L (g / L.block)) Bar.state.count⟩) ∨
      Left P L X g k := by
  have hown : g = Bar.state.owner L (g / L.block) :=
    barOf_owner hpre.block 10 (by rw [ht]; rfl)
  rcases init_before hpre hX hg 10 hσ (by rw [ht]; rfl) hcnt with h | h
  · refine .inl ⟨hown, ?_⟩
    obtain ⟨hloc, hcount⟩ := bar_loc_count hpre .state (g / L.block)
    rw [hloc, hcount]
    exact h
  · exact .inr h

/-- **`Protocol.InitFacts.use_ev` for the startup phase**: an event other than its
initialization that names a barrier names one of the thread's block, after the `bar.sync 0`
that publishes it or, in the owner, after the initialization. -/
theorem use_ev_startup {k : Nat} {e : Event} {m : Loc} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hm : MbarOf e m)
    (hni : ∀ n, e.kind ≠ .mbInit m n) :
    (∃ b : Bar, m = b.loc L (g / L.block) ∧
        (b.gen + 1 ≤ bar0Before X (g, k) ∨
          g = b.owner L (g / L.block) ∧
            ∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj, .mbInit m b.count⟩)) ∨
      Left P L X g k := by
  have hstate : Bar.state.loc L (g / L.block) = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
    simp only [Bar.loc, Bar.off, hpre.sharedBase]
  rcases event_at hpre hX hg he hσ with ⟨pos, hr, hl, hev⟩ | h
  · rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      exact hm.elim
    · obtain ⟨v, ok, rfl⟩ := hev
      exact hm.elim
    · subst hev
      obtain rfl : m = _ := hm
      exact absurd rfl (hni _)
    · subst hev
      exact hm.elim
    · subst hev
      exact hm.elim
    · obtain ⟨i, hi, bs, hbs, rfl⟩ := hev
      exact hm.elim
    · subst hev
      obtain rfl : m = _ := hm
      have ht : tid g = 128 := by
        have := hr.pos
        simp only [AtPos] at this
        exact this.2.2.2.2.1
      have hcnt : ((X.tr g).take k).countP isInit = 1 := congrArg Led.inits hl
      rcases state_owner_init hpre hX hg hσ ht (by omega) with ⟨h1, h2⟩ | h
      · exact .inl ⟨.state, hstate.symm, .inr ⟨h1, by rw [← hstate]; exact h2⟩⟩
      · exact .inr h
    · subst hev
      obtain rfl : _ = m := hm
      have ht : tid g = 128 := by
        have := hr.pos
        simp only [AtPos] at this
        exact this.2.2.2.1
      have hcnt : ((X.tr g).take k).countP isInit = 1 := congrArg Led.inits hl
      rcases state_owner_init hpre hX hg hσ ht (by omega) with ⟨h1, h2⟩ | h
      · exact .inl ⟨.state, hstate.symm, .inr ⟨h1, by
          rw [show (stateSpec P L g j.val).mbar = Bar.state.loc L (g / L.block) from hstate.symm]
          exact h2⟩⟩
      · exact .inr h
    · obtain ⟨ok, rfl⟩ := hev
      obtain rfl : m = _ := hm
      have hbars : bar0Before X (g, k) = 3 := congrArg Led.bars hl
      exact .inl ⟨.state, hstate.symm, .inl (by rw [hbars]; rfl)⟩
  · exact .inr h

/-! ### `StateFacts.issue`, `LifeFacts.state_polled`, `UnionFacts.load` -/

/-- **`Protocol.StateFacts.issue` for the startup phase**: a load that completes on the state
barrier is the load leader's, moves 4096 bytes and has fewer than 16 predecessors. -/
theorem state_issue_startup {i pc al c : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = Bar.state.loc L c)
    (hσ : Frame.stateAt (code L) X g i = some (some s)) :
    (g = loadLeader L c ∧ TensorTransfer.bytes sp.descriptor = 4096 ∧
      ((X.tr g).take i).countP (issuesTo (Bar.state.loc L c)) < 16) ∨ Left P L X g i := by
  rcases issue_startup hpre hX hg he hσ with ⟨j, -, -, rfl, ht, hl⟩ | h
  · have hc : c = g / L.block := (congrArg Loc.cta hm).symm
    have hb := hpre.block
    refine .inl ⟨?_, loadSpec_bytes P _ 8 _ _ _, ?_⟩
    · unfold tid at ht
      simp only [loadLeader, thr, hc, hb]
      omega
    · have h1 : ((X.tr g).take i).countP (issuesTo (Bar.state.loc L c)) ≤
          ((X.tr g).take i).countP isIssue :=
        List.countP_mono_left fun x _ hx => issuesTo_isIssue hx
      have h2 : ((X.tr g).take i).countP isIssue = j.val := congrArg Led.issues hl
      have := j.isLt
      omega
  · exact .inr h

/-- **A thread that has left the startup phase has polled the state barrier of its block
successfully.** -/
theorem Left.statePolled {k : Nat} (h : Left P L X g k) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨j0, hj0, s0, hσ0, -, hl⟩ := h
  have h1 : ((X.tr g).take j0).countP isOkPoll = 1 := congrArg Led.polls hl
  obtain ⟨i, hi, x, hx, hxp, hc⟩ :=
    exists_nth isOkPoll (X.tr g) (n := 0) (k := j0) (by omega)
  obtain ⟨pc, kd⟩ := x
  obtain ⟨m, q, acq, sc, rfl⟩ : ∃ m q acq sc, kd = .wait m q true acq sc := by
    cases kd with
    | wait m q ok acq sc =>
      cases ok with
      | false => cases hxp
      | true => exact ⟨m, q, acq, sc, rfl⟩
    | _ => cases hxp
  obtain ⟨si, hσi⟩ := followed_of_le hσ0 (show i ≤ j0 by omega)
  rcases wait_startup hpre hX hg hx hσi with ⟨-, rfl, -⟩ | hleft
  · refine List.countP_pos_iff.mpr ⟨_, get_mem_take hx (by omega), ?_⟩
    rw [okPoll_wait rfl]
    simp only [Bar.loc, Bar.off, hpre.sharedBase, decide_true, Bool.and_self]
  · have := Left.polls hleft
    omega

/-- **`Protocol.LifeFacts.state_polled` for a thread whose machine is at a state at its
exit**: a thread that exits has polled the state barrier of its block successfully (no
position of the startup phase fires an exit, so the thread has left the phase). -/
theorem state_polled_startup {j pcx : Nat} {s : D} (he : X.get (g, j) = some ⟨pcx, .exit⟩)
    (hσ : Frame.stateAt (code L) X g j = some (some s)) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j) := by
  rcases event_at hpre hX hg he hσ with ⟨pos, -, -, hev⟩ | h
  · exfalso
    rcases pos with j | j | j | j | j | j | _ | j | _ <;>
      simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
        false_and] at hev
  · exact Left.statePolled hpre hX hg h

/-- **Inside the phase every tensor load issued so far completes on the state barrier**: the
count by object is the ledger's count by kind. -/
theorem issues_state {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P X g k s) :
    ((X.tr g).take k).countP (issuesTo ⟨.shared, g / L.block, P.sharedBase + 98384⟩) =
      ((X.tr g).take k).countP isIssue := by
  refine List.countP_congr fun x hx => ?_
  obtain ⟨i, hi, hxi⟩ := mem_take hx
  obtain ⟨si, hσi⟩ := followed_of_le hσ (show i ≤ k by omega)
  rcases event_at hpre hX hg hxi hσi with ⟨pos, -, -, hev⟩ | hleft
  · rcases pos with j | j | j | j | j | j | _ | j | _ <;> simp only [Ev] at hev
    · obtain ⟨inst, ld, rfl⟩ := hev
      simp [issuesTo, isIssue]
    · obtain ⟨v, ok, rfl⟩ := hev
      simp [issuesTo, isIssue]
    · subst hev
      simp [issuesTo, isIssue]
    · subst hev
      simp [issuesTo, isIssue]
    · subst hev
      simp [issuesTo, isIssue]
    · obtain ⟨i', hi', bs, hbs, rfl⟩ := hev
      simp [issuesTo, isIssue]
    · subst hev
      simp [issuesTo, isIssue]
    · subst hev
      simp [issuesTo, isIssue, stateSpec]
    · obtain ⟨ok, rfl⟩ := hev
      simp [issuesTo, isIssue]
  · exact absurd (hleft.mono (by omega)) hI.not_left

end

/-- **The block of the state buffer that holds a byte**: the owner function `Owners.block` of
the protocol's contract `UnionFacts` for the bytes the 16 loads of the initial state write
(the `j`-th load writes the 4096 bytes from `shared_mem + 32768 + 4096 j`). -/
def stateBlock (P : Params) (l : Loc) : Nat := (l.addr - (P.sharedBase + 32768)) / 4096

/-- **`Protocol.UnionFacts.load` for the startup phase** (class `init`): a load of the phase
that writes a byte of the union region completes on the state barrier of that block, and with
`q` earlier loads on that barrier it writes block `q` of the state buffer. -/
theorem union_load_startup (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {O : Owners}
    (hO : O.block = stateBlock P) {i pc al x y z c : Nat} {sp : TensorCopy.Spec} {l : Loc}
    {s : D} (he : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hw : TensorCopy.writeLoc sp x y z = some l) (hl : InUnion L c l)
    (hσ : Frame.stateAt (code L) X g i = some (some s)) :
    LoadClass L X O c g i sp l ∨ Left P L X g i := by
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases startup_inv hpre hX hg hi hσ with hI | hleft
  · rcases issue_startup hpre hX hg he hσ with ⟨j, -, -, rfl, ht, hled⟩ | h
    · obtain ⟨-, hcta, hlo, hhi⟩ := writeLoc_range hw
      obtain rfl : c = g / L.block := hl.2.1.symm.trans hcta
      have hstate : Bar.state.loc L (g / L.block) =
          ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
        simp only [Bar.loc, Bar.off, hpre.sharedBase]
      refine .inl (.init hstate.symm ?_)
      rw [hO, hstate, issues_state hpre hX hg hσ hI]
      have h2 : ((X.tr g).take i).countP isIssue = j.val := congrArg Led.issues hled
      have h8 : mapBytes 8 = 4096 := rfl
      rw [h2]
      unfold stateBlock
      omega
    · exact .inr h
  · exact .inr hleft

/-- **The load of the phase with `q` earlier loads on the state barrier is the copy
`stateSpec P L g q`** through the map of parameter object 8 (the map of the initial state). -/
theorem state_issue_spec (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {i pc al c : Nat}
    {sp : TensorCopy.Spec} {s : D} (he : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hm : sp.mbar = Bar.state.loc L c)
    (hσ : Frame.stateAt (code L) X g i = some (some s)) :
    (al = P.objectBase 8 ∧
      sp = stateSpec P L g (((X.tr g).take i).countP (issuesTo (Bar.state.loc L c)))) ∨
      Left P L X g i := by
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases startup_inv hpre hX hg hi hσ with hI | hleft
  · rcases issue_startup hpre hX hg he hσ with ⟨j, -, rfl, rfl, -, hled⟩ | h
    · have hc : c = g / L.block := (congrArg Loc.cta hm).symm
      have hstate : Bar.state.loc L c = ⟨.shared, g / L.block, P.sharedBase + 98384⟩ := by
        simp only [Bar.loc, Bar.off, hpre.sharedBase, hc]
      have h2 : ((X.tr g).take i).countP isIssue = j.val := congrArg Led.issues hled
      rw [hstate, issues_state hpre hX hg hσ hI, h2]
      exact .inl ⟨rfl, rfl⟩
    · exact .inr h
  · exact .inr hleft

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
