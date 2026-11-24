-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsOrigin
public import Kernels.FlashAttn4Fwd.Proof.Thread.Tracked
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemLife
public import Lemmas.Flow.CountFirst

@[expose] public section

/-! # Barrier 2 (fields of `TmemLifeFacts` and `ExitFacts`)

Barrier 2 is used by the start and end barriers of warps 0-12. The facts here:

* **Who.** Every named-barrier instruction of the kernel is at a site of the softmax, correction
  or MMA role (`kernel_bar_pcs`; no prologue, loader, store or idle site is one), so an event on
  any named barrier, barrier 2 included, is a thread's of warps 0-12 (`bar_warp13`,
  `TmemLifeFacts_bar2_warp`, `ExitFacts_bar2_warp`).
* **Shape.** A softmax or correction thread's events with barrier id 2 are its `bar.sync 2, 416`
  and its `bar.arrive 2, 416` (`bar2_split`): its other named barriers have ids `k + 3 + 4 st`
  (its `Ev`). So the barrier-2 ordinal of such a thread is the sum of the role's `bar2` counts
  (`barOrd_split`): `bar2Sync` (`1` after the start barrier) and `bar2Arrive` (`1` at the exit).
* **When.** At its exit such a thread has made both events (`exit_bar2`); a Tensor Memory load or
  store follows its start barrier, which is its first barrier-2 event (`tc_sync`); every event
  other than the exit has at most one barrier-2 event before it (`soft_barOrd_le`), which gives
  `wait_bar2` and the softmax and correction part of `peer_bar2`.

The MMA warp's part (its two `bar.sync 2, 416` and its uses of the peer CTA before the second)
and the loader and store warps' part of `peer_bar2` are premises here, to be supplied by the
role packages' run invariants (`MmaExitBar2`, `PeerBar2High`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Cross
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Named-barrier sites -/

/-- The positions of the named-barrier instructions. -/
abbrev barPcs : List Nat := Flow.bar.toList ++ Flow.barArrive.toList

/-- Every named-barrier instruction of the kernel is listed. -/
theorem kernel_bar_pcs : OpPcsFast kernel.code barOp barPcs = true := by
  decide +kernel

theorem Prologue.site_not_bar (s : Prologue.Site) : s.pc ∉ barPcs := by
  cases s <;> site_decide

theorem Loader.site_not_bar (s : Loader.Site) : s.pc ∉ barPcs := by
  cases s <;> site_decide

theorem Store.site_not_bar (s : Store.Site) : s.pc ∉ barPcs := by
  cases s <;> site_decide

theorem Idle.site_not_bar (s : Idle.Site) : s.pc ∉ barPcs := by
  cases s <;> site_decide

/-- **A named-barrier event is a thread's of a softmax, correction or MMA state.** -/
theorem bar_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    ∃ r, Frame.stateAt (code L) X g i = some (some (.inr r)) ∧
      (r.kind = .softmax ∨ r.kind = .corr ∨ r.kind = .mma) := by
  obtain ⟨d, t, ins, o, hσ, -, -, -, hc, hf⟩ :=
    event_origin hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) he nofun
  have hpc := OpPcsFast.mem kernel_bar_pcs hc (fires_bar_op hf rfl)
  rcases d with p | r
  · exact absurd hpc (Prologue.site_not_bar p.site)
  refine ⟨r, hσ, ?_⟩
  cases r with
  | idle s => exact absurd hpc (Idle.site_not_bar s.site)
  | loader l => exact absurd hpc (Loader.site_not_bar l.site)
  | store s => exact absurd hpc (Store.site_not_bar s.site)
  | softmax _ => exact .inl rfl
  | corr _ => exact .inr (.inl rfl)
  | mma _ => exact .inr (.inr rfl)

/-- **A named-barrier event is a thread's of warps 0-12.** -/
theorem bar_warp13 (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) : warpOf L g < 13 := by
  obtain ⟨r, hσ, hk⟩ := bar_state hpre hX ht he
  have hw := role_of_state hpre hX (Frame.lt_of_get hX he) hσ
  rcases hk with hk | hk | hk <;> rw [hk] at hw <;> simp only [RoleKind.Warp] at hw <;> omega

theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TmemLifeFacts_bar2_warp
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ → warpOf L g < 13 :=
  fun _ he => bar_warp13 hpre hX ht he

theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ExitFacts_bar2_warp
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar 2 cnt m⟩ → warpOf L g < 13 :=
  fun _ he => bar_warp13 hpre hX ht he

/-! ### The barrier-2 events of the softmax and correction warps -/

/-- An event of barrier id 2 is a `bar.sync 2, 416` or a `bar.arrive 2, 416`. -/
def Bar2Kind (x : Event) : Prop :=
  Execution.isBarId 2 x = (barIs 2 416 .sync x || barIs 2 416 .arrive x)

theorem bar2Kind_of_kind {x : Event} {id : Nat} {c : Option Nat} {md : BarMode}
    (hk : x.kind = .bar id c md) (h : id ≠ 2) : Bar2Kind x := by
  obtain ⟨pc, k⟩ := x
  simp only at hk
  subst hk
  cases c <;> simp [Bar2Kind, Execution.isBarId, barIs, h]

theorem bar2Kind_sync {x : Event} (hk : x.kind = .bar 2 (some 416) .sync) : Bar2Kind x := by
  obtain ⟨pc, k⟩ := x
  simp only at hk
  subst hk
  simp [Bar2Kind, Execution.isBarId, barIs]

theorem bar2Kind_arrive {x : Event} (hk : x.kind = .bar 2 (some 416) .arrive) : Bar2Kind x := by
  obtain ⟨pc, k⟩ := x
  simp only at hk
  subst hk
  simp [Bar2Kind, Execution.isBarId, barIs]

theorem Softmax.bar2Kind {L : Launch} {g : Nat} {d : Softmax.D} {x : Event}
    (hev : Softmax.Ev L g d x) (hpc : d.site.pc ∈ barPcs) : Bar2Kind x := by
  have hne : Softmax.kOf L g + 3 + 4 * Softmax.stOf L g ≠ 2 := by omega
  unfold Softmax.Ev at hev
  cases hs : d.site <;> simp only [hs] at hev hpc
  case bar0 => exact bar2Kind_sync hev
  case barEnd => exact bar2Kind_arrive hev
  case gen => exact bar2Kind_of_kind hev hne
  all_goals (exfalso; clear hev hs; revert hpc; site_decide)

theorem Correction.bar2Kind {L : Launch} {g : Nat} {d : Correction.D} {x : Event}
    (hev : Correction.Ev L g d x) (hpc : d.site.pc ∈ barPcs) : Bar2Kind x := by
  have hne : ∀ st : Fin 2, Correction.kOf L g + 3 + 4 * st.val ≠ 2 := fun _ => by omega
  obtain ⟨-, hev⟩ := hev
  cases hs : d.site <;> simp only [hs] at hev hpc
  case bar0 => exact bar2Kind_sync hev
  case barEnd => exact bar2Kind_arrive hev
  case sync st _ => exact bar2Kind_of_kind hev (hne st)
  all_goals (exfalso; clear hev hs; revert hpc; site_decide)

/-- **A softmax or correction thread's events of barrier id 2** are its `bar.sync 2, 416` and
`bar.arrive 2, 416`. -/
theorem bar2_split (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g j : Nat} {x : Event} (hw : warpOf L g < 12)
    (hx : X.get (g, j) = some x) (hl : j + 1 < (X.tr g).length) : Bar2Kind x := by
  obtain ⟨xpc, xk⟩ := x
  cases xk
  case bar id cnt md =>
    have hg := Frame.lt_of_get hX hx
    obtain ⟨d, t, ins, u, hσ, -, hat, hi, hc, hf⟩ :=
      prior_cont hpre hX ht (J := fun _ _ _ => True) (fun g _ => trueJ_run L g) hx hl
    have hpc := OpPcsFast.mem kernel_bar_pcs hc (fires_bar_op hf rfl)
    rcases d with p | r
    · exact absurd hpc (Prologue.site_not_bar p.site)
    have hk := role_of_state hpre hX hg hσ
    cases r with
    | softmax s => exact Softmax.bar2Kind (Softmax.site_event hpre hg hi hat hc hf) hpc
    | corr c => exact Correction.bar2Kind (Correction.site_event hpre hg hi hat hc hf) hpc
    | _ => simp only [Role.kind, RoleKind.Warp] at hk; omega
  all_goals simp [Bar2Kind, Execution.isBarId, barIs]

/-- **The barrier-2 ordinal of a softmax or correction thread** is the sum of its counts of
`bar.sync 2, 416` and `bar.arrive 2, 416`. -/
theorem barOrd_split (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} (hw : warpOf L g < 12)
    (hk : k < (X.tr g).length) :
    barOrd X g k 2 = barEvents 2 416 .sync ((X.tr g).take k) +
      barEvents 2 416 .arrive ((X.tr g).take k) := by
  unfold barOrd barEvents
  refine countP_split (fun x hx => ?_) (fun x _ => ?_)
  · obtain ⟨j, hj, hget⟩ := get_of_mem_take hx
    exact bar2_split hpre hX ht hw hget (by omega)
  · obtain ⟨pc, k⟩ := x
    cases k with
    | bar id c md => cases c <;> cases md <;> simp [barIs]
    | _ => simp [barIs]

/-! ### When the barrier-2 events come -/

/-- A softmax or correction state of a thread's event, with its counts and the event of its
site. -/
theorem sc_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (hw : warpOf L g < 12)
    (he : X.get (g, k) = some e) (hend : ¬ Ends e) :
    (∃ p, Frame.stateAt (code L) X g k = some (some (.inl p)) ∧
      (∀ x ∈ (X.tr g).take k, Prologue.ProKind x.kind) ∧ Prologue.ProKind e.kind) ∨
    (∃ d, Frame.stateAt (code L) X g k = some (some (.inr (.softmax d))) ∧
      Softmax.Counts L g d ((X.tr g).take k) ∧ Softmax.Ev L g d e) ∨
    (∃ d, Frame.stateAt (code L) X g k = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take k) ∧ Correction.Ev L g d e) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, u, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_cont hpre hX ht (fun g hg => roleJ_run hpre hg) he hend
  rcases d with p | r
  · have hat' : At t p.site.pc (Prologue.facts L g p) :=
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
    rcases Prologue.event_cases hpre hat' hc hf with h | ⟨⟨f, hf'⟩, -⟩
    · exact .inl ⟨p, hσ, hJ.1, h.proKind⟩
    · exact absurd (.inl ⟨f, hf'⟩) hend
  have hk := role_of_state hpre hX hg hσ
  cases r with
  | softmax s => exact .inr (.inl ⟨s, hσ, hJ, Softmax.site_event hpre hg hi hat hc hf⟩)
  | corr c => exact .inr (.inr ⟨c, hσ, hJ, Correction.site_event hpre hg hi hat hc hf⟩)
  | _ => simp only [Role.kind, RoleKind.Warp] at hk; omega

theorem Softmax.bar2_of_ev {L : Launch} {g : Nat} {d : Softmax.D} {e : Event}
    (hev : Softmax.Ev L g d e) (h1 : ∀ inc n inst, e.kind ≠ .setMaxReg inc n inst)
    (h2 : e.kind ≠ .bar 2 (some 416) .sync) (h3 : e.kind ≠ .exit) :
    Softmax.bar2Sync d = 1 ∧ Softmax.bar2Arrive d = 0 := by
  unfold Softmax.Ev at hev
  unfold Softmax.bar2Sync Softmax.bar2Arrive
  cases hs : d.site <;> simp only [hs] at hev ⊢
  case setMaxReg => obtain ⟨inst, h⟩ := hev; exact absurd h (h1 _ _ inst)
  case bar0 => exact absurd hev h2
  case exit => exact absurd hev h3
  all_goals simp

theorem Correction.bar2_of_ev {L : Launch} {g : Nat} {d : Correction.D} {e : Event}
    (hev : Correction.Ev L g d e) (h1 : ∀ inc n inst, e.kind ≠ .setMaxReg inc n inst)
    (h2 : e.kind ≠ .bar 2 (some 416) .sync) (h3 : e.kind ≠ .exit) :
    Correction.bar2Sync d = 1 ∧ Correction.bar2Arrive d = 0 := by
  obtain ⟨-, hev⟩ := hev
  unfold Correction.bar2Sync Correction.bar2Arrive
  cases hs : d.site <;> simp only [hs] at hev ⊢
  case setMaxReg => obtain ⟨inst, h⟩ := hev; exact absurd h (h1 _ _ inst)
  case bar0 => exact absurd hev h2
  case exit => exact absurd hev h3
  all_goals simp

theorem Softmax.bar2Sync_le (d : Softmax.D) : Softmax.bar2Sync d ≤ 1 := by
  unfold Softmax.bar2Sync; split <;> simp

theorem Correction.bar2Sync_le (d : Correction.D) : Correction.bar2Sync d ≤ 1 := by
  unfold Correction.bar2Sync; split <;> simp

/-- The prologue's kinds make no named-barrier event. -/
theorem barEvents_pro {es : List Event} (h : ∀ x ∈ es, Prologue.ProKind x.kind) (id c : Nat)
    (m : BarMode) : barEvents id c m es = 0 := by
  unfold barEvents
  refine List.countP_eq_zero.mpr fun x hx => ?_
  have hk := h x hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [Prologue.ProKind] at hk <;> simp [barIs]

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Before an event other than its exit**, a softmax or correction thread has made at most
one barrier-2 event, and none that is a `bar.arrive`. -/
theorem soft_bar2_le {g k : Nat} {e : Event} (hw : warpOf L g < 12) (he : X.get (g, k) = some e)
    (hend : ¬ Ends e) :
    barEvents 2 416 .sync ((X.tr g).take k) ≤ 1 ∧
      barEvents 2 416 .arrive ((X.tr g).take k) = 0 := by
  have hx : e.kind ≠ .exit := fun h => hend (.inr h)
  rcases sc_state hpre hX ht hw he hend with ⟨p, -, hJ, -⟩ | ⟨d, -, hJ, hev⟩ |
      ⟨d, -, hJ, hev⟩
  · simp [barEvents_pro hJ]
  · refine ⟨hJ.bar2.1 ▸ Softmax.bar2Sync_le d, hJ.bar2.2.trans ?_⟩
    unfold Softmax.Ev at hev
    unfold Softmax.bar2Arrive
    cases hs : d.site <;> simp only [hs] at hev ⊢
    exact absurd hev hx
  · refine ⟨hJ.bar2.1 ▸ Correction.bar2Sync_le d, hJ.bar2.2.trans ?_⟩
    obtain ⟨-, hev⟩ := hev
    unfold Correction.bar2Arrive
    cases hs : d.site <;> simp only [hs] at hev ⊢
    exact absurd hev hx

/-- **Every event of a softmax or correction thread but its exit has at most one barrier-2 event
before it.** -/
theorem soft_barOrd_le {g k : Nat} {e : Event} (hw : warpOf L g < 12) (he : X.get (g, k) = some e)
    (hend : ¬ Ends e) : barOrd X g k 2 ≤ 1 := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rw [barOrd_split hpre hX ht hw hk]
  have := soft_bar2_le hpre hX ht hw he hend
  omega

theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TmemLifeFacts_wait_bar2 :
    ∀ {h k pc : Nat} {wk : TcKind}, h < L.threads → warpOf L h < 12 →
      X.get (h, k) = some ⟨pc, .tc wk⟩ → barOrd X h k 2 ≤ 1 := by
  intro h k pc wk _ hw he
  exact soft_barOrd_le hpre hX ht hw he (by rintro (⟨f, hf⟩ | hf) <;> cases hf)

/-- **A softmax or correction Tensor Memory load or store follows the thread's start barrier**,
its `bar.sync 2, 416` of ordinal 0. -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TmemLifeFacts_tc_sync :
    ∀ {h k a : Nat} {vals : List Value}, h < L.threads → warpOf L h < 12 →
      (X.TLd (h, k) a vals .s32x32b ∨ X.TSt (h, k) a vals .s32x32b) → ∃ b < k,
        Bar2Sync X h b 0 := by
  intro h k a vals _ hw htc
  obtain ⟨pc, tk, he, htk⟩ : ∃ pc tk, X.get (h, k) = some ⟨pc, .tc tk⟩ ∧
      (tk = .ld a vals .s32x32b ∨ tk = .st a vals .s32x32b) := by
    rcases htc with ⟨pc, he⟩ | ⟨pc, he⟩
    · exact ⟨pc, _, he, .inl rfl⟩
    · exact ⟨pc, _, he, .inr rfl⟩
  have hend : ¬ Ends ⟨pc, .tc tk⟩ := by rintro (⟨f, hf⟩ | hf) <;> cases hf
  have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  -- the start barrier has been passed, and no `bar.arrive 2, 416` made
  have hsync : barEvents 2 416 .sync ((X.tr h).take k) = 1 ∧
      barEvents 2 416 .arrive ((X.tr h).take k) = 0 := by
    have h1 : ∀ inc n inst, Kind.tc tk ≠ .setMaxReg inc n inst := fun _ _ _ h => by cases h
    have h2 : Kind.tc tk ≠ .bar 2 (some 416) .sync := fun h => by cases h
    have h3 : Kind.tc tk ≠ .exit := fun h => by cases h
    rcases sc_state hpre hX ht hw he hend with ⟨p, -, -, hk⟩ | ⟨d, -, hJ, hev⟩ |
        ⟨d, -, hJ, hev⟩
    · simp only [Prologue.ProKind] at hk
    · rw [hJ.bar2.1, hJ.bar2.2]; exact Softmax.bar2_of_ev hev h1 h2 h3
    · rw [hJ.bar2.1, hJ.bar2.2]; exact Correction.bar2_of_ev hev h1 h2 h3
  obtain ⟨b, hb, x, hx, hp, hc⟩ := first_countP (p := barIs 2 416 .sync) (l := X.tr h) (k := k)
    (by unfold barEvents at hsync; omega)
  have hxb : X.get (h, b) = some x := hx
  have hkind : x.kind = .bar 2 (some 416) .sync := by
    obtain ⟨xpc, xk⟩ := x
    cases xk with
    | bar id c md =>
      cases c with
      | none => simp [barIs] at hp
      | some c => simp only [barIs, decide_eq_true_eq] at hp; simp [hp]
    | _ => simp [barIs] at hp
  refine ⟨b, hb, x.pc, by rw [hxb, ← hkind], ?_⟩
  rw [barOrd_split hpre hX ht hw (by omega)]
  have hle : barEvents 2 416 .arrive ((X.tr h).take b) ≤
      barEvents 2 416 .arrive ((X.tr h).take k) :=
    (List.take_sublist_take_left (by omega)).countP_le
  unfold barEvents at hle hsync ⊢
  omega

omit hpre hX ht in
theorem Softmax.site_exit (s : Softmax.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

omit hpre hX ht in
theorem Correction.site_exit (s : Correction.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

/-- **A softmax or correction thread exits after its two barrier-2 events.** -/
theorem soft_exit_bar2 {g k pc : Nat} (hw : warpOf L g < 12) (he : X.get (g, k) = some ⟨pc, .exit⟩)
    : 2 ≤ barOrd X g k 2 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hret : retOp ins.op = true := retOp_of_fires hf rfl
  have hpc := OpPcsFast.mem kernel_ret_pcs hc hret
  simp only [List.mem_singleton] at hpc
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rw [barOrd_split hpre hX ht hw hk]
  rcases d with p | r
  · exact absurd hpc (Prologue.site_ne_exit p.site)
  have hk := role_of_state hpre hX hg hσ
  cases r with
  | softmax s =>
    have hs := Softmax.site_exit s.site hpc
    have hb := hJ.bar2
    simp only [Softmax.bar2Sync, Softmax.bar2Arrive, hs] at hb
    omega
  | corr c =>
    have hs := Correction.site_exit c.site hpc
    have hb := hJ.bar2
    simp only [Correction.bar2Sync, Correction.bar2Arrive, hs] at hb
    omega
  | _ => simp only [Role.kind, RoleKind.Warp] at hk; omega

omit hpre hX ht in
/-- The MMA warp's part of `exit_bar2`, a fact of its run invariant (WP4: a barrier-2 count of
`Mma.Counts`). -/
def MmaExitBar2 (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat}, g < L.threads → warpOf L g = 12 → X.get (g, k) = some ⟨pc, .exit⟩ →
    2 ≤ barOrd X g k 2

theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.TmemLifeFacts_exit_bar2 (hmma : MmaExitBar2 L X) :
    ∀ {g k pc : Nat}, g < L.threads → warpOf L g < 13 →
      X.get (g, k) = some ⟨pc, .exit⟩ → 2 ≤ barOrd X g k 2 := by
  intro g k pc hg hw he
  by_cases h12 : warpOf L g = 12
  · exact hmma hg h12 he
  · exact soft_exit_bar2 hpre hX ht (by omega) he

theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ExitFacts_bar2_exit (hmma : MmaExitBar2 L X) :
    ∀ {g k pc : Nat}, g < L.threads → warpOf L g < 13 →
      X.get (g, k) = some ⟨pc, .exit⟩ → 2 ≤ barOrd X g k 2 :=
  TmemLifeFacts_exit_bar2 hpre hX ht hmma

omit hpre hX ht in
/-- The part of `peer_bar2` for warps 12-15, a fact of the MMA warp's run invariant (WP4: its
commits and its arrivals on the peer CTA come before its second barrier-2 event) and of the
loader's and the store warp's events (WP2, WP1: they use only barriers of their own CTA, and
make no commit). -/
def PeerBar2High (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {ev : Event}, g < L.threads → 12 ≤ warpOf L g → X.get (g, k) = some ev →
    PeerEvent L g ev → warpOf L g = 12 ∧ barOrd X g k 2 ≤ 1

/-- **A use of the other CTA but the handshake arrival comes before the thread's second
barrier-2 event.** -/
theorem _root_.PTX.Kernels.FlashAttn4Fwd.Proof.ExitFacts_peer_bar2 (hhigh : PeerBar2High L X) :
    ∀ {g k : Nat} {ev : Event}, g < L.threads → X.get (g, k) = some ev →
      PeerEvent L g ev → warpOf L g < 13 ∧ barOrd X g k 2 ≤ 1 := by
  intro g k ev hg he hp
  by_cases hw : 12 ≤ warpOf L g
  · obtain ⟨h12, hb⟩ := hhigh hg hw he hp
    exact ⟨by omega, hb⟩
  · refine ⟨by omega, soft_barOrd_le hpre hX ht (by omega) he ?_⟩
    rintro (⟨f, hf⟩ | hf) <;>
      rcases hp with ⟨m, tx, cnt, rel, sc, hk, -⟩ | ⟨sp, hk⟩ <;> rw [hk] at hf <;> cases hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Cross
