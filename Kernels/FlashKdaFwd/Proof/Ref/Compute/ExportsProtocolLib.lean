-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolAccess
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds

@[expose] public section

/-! # Tools for the protocol exports of the Compute phase

The Compute phase (instructions 2106 to 2944: the tile loop of a compute thread, a thread with
index below 128 in its block) has an invariant `Inv P L X g j0 k s` of the state `s` of the
thread machine before the thread's event `k`, for a thread that was at the phase's entry before
its event `j0` (`Inv.lean`). The contracts of the protocol layer are statements about events.
This file turns the invariant into statements about events; `ExportsProtocol.lean` then states
them field by field.

* `EvAt P L g pos e`: **the event of a position in closed form.** A *position* (`Pos`) is the
  entry or the pair of a tile `t` and an index `n < 268` in the tile's straight line of 268
  events. The event at the entry is the thread's sixth `bar.sync 0`; at positions 0 and 1 the
  polls of the "empty" mbarrier of output stage `t % 2` and of the "full" mbarrier of input
  stage `t % 3`; at 264 the named barrier `bar.sync 8, 128`; at 265 the proxy fence; at 266 and
  267 the arrivals on the "full" output mbarrier and on the "empty" input mbarrier; at a
  position with a memory access the read or the write of the footprint `accOf P L g t n`; at
  the other positions a warp matrix event or undefined behaviour (the operands of a matrix
  instruction are data, which the reference layer does not follow).
  `ev_at`: the event at a followed state of a position is the position's.
* `InvAt P L X g j0 k pos s`: the invariant with its position named (`Inv` is
  `∃ pos, InvAt … pos s`).
* **Earlier states.** `inv_before`: when the invariant holds at `k`, it holds at every followed
  state between the entry `j0` and `k` (the thread has not left the phase in between: the
  number of counted events only grows). `step_back`: the state before a position `n ≥ 3` of a
  tile is at position `n - 1` of the same tile, one event earlier (only a poll can fail, and
  polls are at positions 0 and 1). `back`: the same `d` events earlier. `entry_at`: a state at
  the entry position is the state at `j0`.
* **Ledger readouts** (`cnt_*`): the counts of the classes of events of the ledger before a
  state at a position, in the form the contracts use (`okPolls`, `arrivals`, `countP`), and the
  arithmetic of `uses` (`Protocol/Layout.lean`: `uses n t s` is the number of the tiles before
  `t` that use stage `s` of an `n`-stage pipeline).

Words: an *mbarrier* is one of the eleven 8-byte synchronization objects of a block
(`Protocol.Bar`); a *poll* is an `mbarrier.try_wait`; a *counted* event is any event but a
failed poll; a *followed state* at `k` is the state of the thread's machine before the thread's
event `k` (`At (code L) X g k s`). Everything is in the namespace `Compute.Proto`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Proto
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g t : Nat} {e : Event}

/-! ### The sites of the warp matrix events -/

/-- The kind of site is that of a warp matrix event: the second event of an `ldmatrix`, an
`mma.sync`, a `movmatrix`, or the first event of an `stmatrix`. -/
def isMx : SK → Bool
  | .ldMx _ | .mma _ | .mv _ | .st _ => true
  | _ => false

/-- A position between the polls and the named barrier that has no memory access is at a site
of a warp matrix event. -/
theorem mx_pos : ∀ n < 268, 2 ≤ n → n < 264 → (addrOf n).2.2 = 0 → isMx (skOf n) = true := by
  decide +kernel

/-- An event fired at a site of a warp matrix event is a matrix event or undefined
behaviour. -/
theorem fired_matrix {k : Kind} {sk : SK} {s : Site} (h : firedAt k s.kind = true)
    (hat : sk.At s) (hm : isMx sk = true) :
    (∃ op own recv, k = .matrix op own recv) ∨ ∃ f, k = .ub f := by
  cases sk <;> simp only [isMx, Bool.false_eq_true] at hm <;> simp only [SK.At] at hat <;>
    first
      | subst hat
      | (obtain ⟨row, rfl⟩ := hat)
  all_goals
    cases k <;> first
      | exact .inl ⟨_, _, _, rfl⟩
      | exact .inr ⟨_, rfl⟩
      | cases h

/-! ### The event of a position -/

/-- **The event of a position, in closed form**: the sixth `bar.sync 0` at the entry; in tile
`t` the two polls (positions 0 and 1), the named barrier (264), the proxy fence (265), the two
arrivals (266, 267); at a position with a memory access the read, or (at the row write of an
`stmatrix`) the write, of the position's footprint; elsewhere a warp matrix event or undefined
behaviour. -/
def EvAt (P : Params) (L : Launch) (g : Nat) : Pos → Event → Prop
  | .entry, e => e = ⟨1402, .bar 0 none .sync⟩
  | .tile t n, e =>
    if n = 0 then ∃ ok, e = ⟨2144, .wait ((Bar.storeEmpty (stage2 t)).loc L (g / L.block))
      ((t / 2 + 1) % 2) ok true .cta⟩
    else if n = 1 then ∃ ok, e = ⟨2186, .wait ((Bar.loadFull (stage3 t)).loc L (g / L.block))
      (t / 3 % 2) ok true .cta⟩
    else if n = 264 then e = ⟨2913, .bar 8 (some 128) .sync⟩
    else if n = 265 then e = ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩
    else if n = 266 then
      e = ⟨2920, .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true .cta⟩
    else if n = 267 then
      e = ⟨2928, .arrive ((Bar.loadEmpty (stage3 t)).loc L (g / L.block)) 0 1 true .cta⟩
    else if (addrOf n).2.2 = 0 then (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f
    else (∃ bs, e.kind = .rd (accOf P L g t n) bs ∧ isWr (skOf n) = false) ∨
      ∃ bs, e.kind = .wr (accOf P L g t n) bs ∧ isWr (skOf n) = true

theorem evAt_0 : EvAt P L g (.tile t 0) e ↔ ∃ ok, e = ⟨2144,
    .wait ((Bar.storeEmpty (stage2 t)).loc L (g / L.block)) ((t / 2 + 1) % 2) ok true .cta⟩ :=
  Iff.rfl

theorem evAt_1 : EvAt P L g (.tile t 1) e ↔ ∃ ok, e = ⟨2186,
    .wait ((Bar.loadFull (stage3 t)).loc L (g / L.block)) (t / 3 % 2) ok true .cta⟩ := Iff.rfl

theorem evAt_264 : EvAt P L g (.tile t 264) e ↔ e = ⟨2913, .bar 8 (some 128) .sync⟩ := Iff.rfl

theorem evAt_265 : EvAt P L g (.tile t 265) e ↔
    e = ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩ := Iff.rfl

theorem evAt_266 : EvAt P L g (.tile t 266) e ↔ e = ⟨2920,
    .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true .cta⟩ := Iff.rfl

theorem evAt_267 : EvAt P L g (.tile t 267) e ↔ e = ⟨2928,
    .arrive ((Bar.loadEmpty (stage3 t)).loc L (g / L.block)) 0 1 true .cta⟩ := Iff.rfl

/-- The event of a position between the polls and the named barrier: a matrix event or
undefined behaviour, or the access of the position. -/
theorem evAt_body {n : Nat} (h2 : 2 ≤ n) (h264 : n < 264) : EvAt P L g (.tile t n) e ↔
    if (addrOf n).2.2 = 0 then (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f
    else (∃ bs, e.kind = .rd (accOf P L g t n) bs ∧ isWr (skOf n) = false) ∨
      ∃ bs, e.kind = .wr (accOf P L g t n) bs ∧ isWr (skOf n) = true := by
  have e0 : ¬ n = 0 := by omega
  have e1 : ¬ n = 1 := by omega
  have e2 : ¬ n = 264 := by omega
  have e3 : ¬ n = 265 := by omega
  have e4 : ¬ n = 266 := by omega
  have e5 : ¬ n = 267 := by omega
  simp only [EvAt, ite_eq_right e0, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3,
    ite_eq_right e4, ite_eq_right e5]

/-- The positions of a tile: the six control positions, or a position of the body. -/
theorem pos_cases {n : Nat} (hn : n < 268) :
    n = 0 ∨ n = 1 ∨ n = 264 ∨ n = 265 ∨ n = 266 ∨ n = 267 ∨ (2 ≤ n ∧ n < 264) := by omega

/-- An event that is no poll counts. -/
theorem counts_of_kind (h : ∀ m q ok acq sc, e.kind ≠ .wait m q ok acq sc) :
    e.counts = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first | rfl | exact absurd rfl (h _ _ _ _ _)

/-- **Every event of the phase but the two polls counts.** -/
theorem EvAt.counts {pos : Pos} (h : EvAt P L g pos e) (hp : ∀ t n, pos = .tile t n → 2 ≤ n) :
    e.counts = true := by
  cases pos with
  | entry =>
    rw [show e = _ from h]
    rfl
  | tile t n =>
    have h2 := hp t n rfl
    have e0 : ¬ n = 0 := by omega
    have e1 : ¬ n = 1 := by omega
    simp only [EvAt, ite_eq_right e0, ite_eq_right e1] at h
    split_ifs at h
    · rw [h]; rfl
    · rw [h]; rfl
    · rw [h]; rfl
    · rw [h]; rfl
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;>
        exact counts_of_kind fun m q ok acq sc hk => by rw [h] at hk; cases hk
    · rcases h with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;>
        exact counts_of_kind fun m q ok acq sc hk => by rw [h] at hk; cases hk

/-- **The event at a followed state of a position is the position's event.** -/
theorem ev_at (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {pos : Pos} {s : D} {k : Nat} (h : RefAt P L g pos s) (hs : At (code L) X g k s)
    (he : X.get (g, k) = some e) : EvAt P L g pos e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hs
  have hfire := site_fires (sounds hpre) hX he hs
  obtain ⟨site, w, p, x⟩ := s
  cases pos with
  | entry =>
    obtain rfl : site = .bar 5 := h.site
    exact ev_entry hc hf
  | tile t n =>
    have hn : n < 268 := h.facts.pos
    have hsite : (skOf n).At site := h.site
    rcases pos_cases hn with rfl | rfl | rfl | rfl | rfl | rfl | ⟨h2, h264⟩
    · obtain rfl : site = .mbarWait 7 := hsite
      exact evAt_0.mpr (ev_pollE hpre h.facts hat hc hf)
    · obtain rfl : site = .mbarWait 8 := hsite
      exact evAt_1.mpr (ev_pollF hpre h.facts hat hc hf)
    · obtain rfl : site = .bar 6 := hsite
      exact evAt_264.mpr (ev_bar8 hpre h.facts hat hc hf)
    · obtain rfl : site = .fenceProxy 2 := hsite
      exact evAt_265.mpr (ev_fence hc hf)
    · obtain rfl : site = .mbarArrive 4 := hsite
      exact evAt_266.mpr (ev_arriveF hpre h.facts hat hc hf)
    · obtain rfl : site = .mbarArrive 5 := hsite
      exact evAt_267.mpr (ev_arriveE hpre hg h.facts hat hc hf)
    · rw [evAt_body h2 h264]
      by_cases ha : (addrOf n).2.2 = 0
      · rw [ite_eq_left ha]
        exact fired_matrix hfire hsite (mx_pos n hn h2 h264 ha)
      · rw [ite_eq_right ha]
        rcases acc_at hpre h.facts hsite hat hc hf ha with ⟨bs, h1, h3⟩ | ⟨j, row, -, h1, h3⟩
        · exact .inl ⟨bs, h1, h3⟩
        · exact .inr ⟨_, h1, h3⟩

/-! ### The invariant with its position named -/

/-- **The invariant of the Compute phase with its position named**: the state `s` before the
thread's event `k` is at the position `pos` with that position's register facts, the ledger of
the first `k` events is the position's, and the counted events since the entry `j0` are the
position's. `Inv P L X g j0 k s` is `∃ pos, InvAt P L X g j0 k pos s`. -/
def InvAt (P : Params) (L : Launch) (X : Execution) (g j0 k : Nat) (pos : Pos) (s : D) :
    Prop :=
  RefAt P L g pos s ∧ ledOf L (g / L.block) ((X.tr g).take k) = led pos ∧ j0 ≤ k ∧
    counted X g j0 k = pos.idx

theorem InvAt.inv {j0 k : Nat} {pos : Pos} {s : D} (h : InvAt P L X g j0 k pos s) :
    Inv P L X g j0 k s := ⟨pos, h⟩

/-- A state of the invariant is a state of a compute thread. -/
theorem refAt_compute {pos : Pos} {s : D} (h : RefAt P L g pos s) : tid g < 128 := by
  cases pos with
  | entry => exact (show Entry P g s from h.facts).compute
  | tile t n => exact (show Tile P L g t n s.w s.p s.x from h.facts).compute

/-- The counted events of a position are fewer than those of the exit. -/
theorem idx_lt {pos : Pos} {s : D} (h : RefAt P L g pos s) :
    pos.idx < 1 + 268 * tilesOf P g := by
  cases pos with
  | entry =>
    simp only [Pos.idx]
    omega
  | tile t n =>
    have h1 : t < tilesOf P g := h.facts.lt
    have h2 : n < 268 := h.facts.pos
    simp only [Pos.idx]
    omega

/-- The counted events since the entry only grow. -/
theorem counted_mono (X : Execution) (g j0 : Nat) {j k : Nat} (h : j ≤ k) :
    counted X g j0 j ≤ counted X g j0 k :=
  ((List.take_sublist_take_left h).drop j0).countP_le

/-- A position is determined by its number of counted events. -/
theorem pos_of_idx {pos pos' : Pos} {s s' : D} (h : RefAt P L g pos s)
    (h' : RefAt P L g pos' s') (hi : pos.idx = pos'.idx) : pos = pos' := by
  cases pos with
  | entry =>
    cases pos' with
    | entry => rfl
    | tile t' n' =>
      simp only [Pos.idx] at hi
      omega
  | tile t n =>
    cases pos' with
    | entry =>
      simp only [Pos.idx] at hi
      omega
    | tile t' n' =>
      have h1 : n < 268 := h.facts.pos
      have h2 : n' < 268 := h'.facts.pos
      simp only [Pos.idx] at hi
      obtain ⟨rfl, rfl⟩ : t = t' ∧ n = n' := by omega
      rfl

/-! ### Earlier states -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 k : Nat} {s0 s : D} (h0 : At (code L) X g j0 s0)
  (hin : In P L X g j0 s0) (hk : k ≤ (X.tr g).length) (hs : At (code L) X g k s)
include hpre hX hg h0 hin hk hs

/-- **The invariant holds between the entry and a state of the invariant**: the thread has not
left the phase before `k`, because at the exit it has made more counted events than at any
position. -/
theorem inv_before (hI : Inv P L X g j0 k s) {i : Nat} (hi0 : j0 ≤ i) (hik : i ≤ k) :
    ∃ si, At (code L) X g i si ∧ Inv P L X g j0 i si := by
  obtain ⟨si, hsi⟩ := followed_of_le hs hik
  refine ⟨si, hsi, ?_⟩
  rcases inv_at hpre hX hg h0 hin hi0 (by omega) hsi with h | ⟨j, s1, -, h2, -, -, -, -, hc⟩
  · exact h
  · obtain ⟨pos, hR, -, -, hcnt⟩ := hI
    have h3 := idx_lt hR
    have h4 := counted_mono X g j0 (show j ≤ k by omega)
    omega

omit hg hs in
/-- **A state at the entry position is the state at the entry index**: the event of the entry
state (the sixth `bar.sync 0`) counts. -/
theorem entry_at (hI : InvAt P L X g j0 k .entry s) : k = j0 := by
  obtain ⟨-, -, hjk, hcnt⟩ := hI
  by_contra hne
  have hlt : j0 < k := by omega
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, j0) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (show j0 < (X.tr g).length by omega)⟩
  have hev : EvAt P L g .entry e0 := ev_at hpre hX ⟨hin.1.site, hin.1⟩ h0 he0
  have h1 : counted X g j0 (j0 + 1) = 1 := by
    rw [counted_succ (le_refl j0) he0, counted_self, show e0 = _ from hev]
    rfl
  have h2 := counted_mono X g j0 (show j0 + 1 ≤ k by omega)
  have h3 : counted X g j0 k = 0 := hcnt
  omega

/-- **One event back inside a tile**: the state before a state at position `n ≥ 3` of tile `t`
is at position `n - 1` of the same tile, and the event between them leads from the one to the
other. -/
theorem step_back {t n : Nat} (hI : InvAt P L X g j0 k (.tile t n) s) (hn : 3 ≤ n) :
    0 < k ∧ ∃ s' e', At (code L) X g (k - 1) s' ∧
      InvAt P L X g j0 (k - 1) (.tile t (n - 1)) s' ∧ X.get (g, k - 1) = some e' ∧
      Thread.next L g s' e' = some (some s) := by
  obtain ⟨hR, hled, hjk, hcnt⟩ := hI
  have hk0 : j0 < k := by
    rcases Nat.eq_or_lt_of_le hjk with rfl | h
    · rw [counted_self] at hcnt
      simp only [Pos.idx] at hcnt
      omega
    · exact h
  obtain ⟨s', hs', pos', hR', hled', hjk', hcnt'⟩ :=
    inv_before hpre hX hg h0 hin hk hs ⟨_, hR, hled, hjk, hcnt⟩ (show j0 ≤ k - 1 by omega)
      (Nat.sub_le k 1)
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, k - 1) = some e' :=
    ⟨_, List.getElem?_eq_getElem (show k - 1 < (X.tr g).length by omega)⟩
  have hk1 : k - 1 + 1 = k := by omega
  have hsucc := counted_succ hjk' he'
  rw [hk1, hcnt, hcnt'] at hsucc
  have hev := ev_at hpre hX hR' hs' he'
  have hnext : Thread.next L g s' e' = some (some s) := by
    have h := Frame.stateAt_succ (C := code L) he'
    rw [hk1, hs, hs'] at h
    exact h.symm
  have hn268 : n < 268 := hR.facts.pos
  have hpos : pos' = .tile t (n - 1) := by
    cases pos' with
    | entry =>
      simp only [Pos.idx] at hsucc
      split_ifs at hsucc <;> omega
    | tile t' n' =>
      have hn' : n' < 268 := hR'.facts.pos
      by_cases h2 : 2 ≤ n'
      · have hc := hev.counts fun _ _ h => by cases h; exact h2
        rw [hc] at hsucc
        simp only [Pos.idx, ite_true] at hsucc
        obtain ⟨rfl, rfl⟩ : t' = t ∧ n' = n - 1 := by omega
        rfl
      · simp only [Pos.idx] at hsucc
        split_ifs at hsucc <;> omega
  subst hpos
  exact ⟨by omega, s', e', hs', ⟨hR', hled', hjk', hcnt'⟩, he', hnext⟩

/-- **`d` events back inside a tile**: from position `n` of tile `t`, the state `d` events
earlier is at position `n - d`, as long as that is no poll (`d + 2 ≤ n`). -/
theorem back {t n : Nat} (hI : InvAt P L X g j0 k (.tile t n) s) :
    ∀ d, d + 2 ≤ n → d ≤ k ∧ ∃ s', At (code L) X g (k - d) s' ∧
      InvAt P L X g j0 (k - d) (.tile t (n - d)) s' := by
  intro d
  induction d with
  | zero => exact fun _ => ⟨Nat.zero_le _, s, hs, hI⟩
  | succ d ih =>
    intro hd
    obtain ⟨hdk, s', hs', hI'⟩ := ih (by omega)
    obtain ⟨hpos, s'', e', hs'', hI'', -, -⟩ :=
      step_back hpre hX hg h0 hin (show k - d ≤ (X.tr g).length by omega) hs' hI' (by omega)
    have e1 : k - (d + 1) = k - d - 1 := by omega
    have e2 : n - (d + 1) = n - d - 1 := by omega
    rw [e1, e2]
    exact ⟨by omega, s'', hs'', hI''⟩

end

/-! ### Ledger readouts -/

section
variable {c : Nat} {es : List Event}

/-- The ledger at the entry: five `bar.sync 0`, no named barrier, the poll of the state
mbarrier. -/
theorem cnt_entry (hl : ledOf L c es = led .entry) :
    es.countP (Execution.isBarId 0) = 5 ∧ es.countP (Execution.isBarId 8) = 0 ∧
      okPolls (Bar.state.loc L c) es = 1 :=
  ⟨congrArg Led.bar0 hl, congrArg Led.bar8 hl, congrArg Led.pollS hl⟩

variable {t n : Nat} (hl : ledOf L c es = led (.tile t n))
include hl

/-- Six `bar.sync 0` before a state of a tile. -/
theorem cnt_bar0 : es.countP (Execution.isBarId 0) = 6 := congrArg Led.bar0 hl

/-- One named barrier per earlier tile, and the tile's own from position 265 on. -/
theorem cnt_bar8 : es.countP (Execution.isBarId 8) = t + ind 265 n := congrArg Led.bar8 hl

/-- The poll of the state mbarrier (in the startup phase). -/
theorem cnt_state : okPolls (Bar.state.loc L c) es = 1 := congrArg Led.pollS hl

/-- Successful polls of the "empty" mbarrier of output stage `o`. -/
theorem cnt_pe (o : Fin 2) :
    okPolls ((Bar.storeEmpty o).loc L c) es = uses 2 (t + ind 1 n) o.val := by
  fin_cases o
  · exact congrArg Led.pe0 hl
  · exact congrArg Led.pe1 hl

/-- Successful polls of the "full" mbarrier of input stage `s`. -/
theorem cnt_pf (s : Fin 3) :
    okPolls ((Bar.loadFull s).loc L c) es = uses 3 (t + ind 2 n) s.val := by
  fin_cases s
  · exact congrArg Led.pf0 hl
  · exact congrArg Led.pf1 hl
  · exact congrArg Led.pf2 hl

/-- Arrivals on the "full" mbarrier of output stage `o`. -/
theorem cnt_af (o : Fin 2) :
    arrivals ((Bar.storeFull o).loc L c) es = uses 2 (t + ind 267 n) o.val := by
  fin_cases o
  · exact congrArg Led.af0 hl
  · exact congrArg Led.af1 hl

/-- Arrivals on the "empty" mbarrier of input stage `s`. -/
theorem cnt_ae (s : Fin 3) : arrivals ((Bar.loadEmpty s).loc L c) es = uses 3 t s.val := by
  fin_cases s
  · exact congrArg Led.ae0 hl
  · exact congrArg Led.ae1 hl
  · exact congrArg Led.ae2 hl

end

/-- The uses of the stage of tile `t` among the tiles before `t`, and with tile `t`. -/
theorem uses2_self (t : Nat) : uses 2 t (t % 2) = t / 2 := by
  simp only [uses]
  omega

theorem uses2_succ (t : Nat) : uses 2 (t + 1) (t % 2) = t / 2 + 1 := by
  simp only [uses]
  omega

theorem uses3_self (t : Nat) : uses 3 t (t % 3) = t / 3 := by
  simp only [uses]
  omega

theorem uses3_succ (t : Nat) : uses 3 (t + 1) (t % 3) = t / 3 + 1 := by
  simp only [uses]
  omega

/-- More tiles use a stage no less often. -/
theorem uses_mono {n a b : Nat} (s : Nat) (h : a ≤ b) : uses n a s ≤ uses n b s :=
  Nat.div_le_div_right (by omega)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Proto
