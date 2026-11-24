-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.NoBarArrive
public import Kernels.RmsNorm.Proof.Progress.Rank
public import Lemmas.Kernel.Descent
public import Lemmas.Step.WarpShfl

@[expose] public section

/-! # The lanes of a warp at a shuffle

A pending thread is at a state of its machine (`pending_state`): the machine stops only at a
value it rejects, and every value is accepted (`next_ne_none`). No lane of a warp has made more
shuffles than a pending lane (`lane_count_le`, DEP-ORDER, DEP-WARP-INSTANCE), and an exited lane
has made the shuffles of all its CTA's rows (`exit_counts`). So a lane of the warp of a thread at a
shuffle site is at the same site of the same row, or pending with less progress (`lane_lower`). -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The last event of a thread, if a barrier arrival, is released. -/
abbrev LastReleased (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ id count pc, 0 < (X.tr g).length → X.IsBarrier (g, (X.tr g).length - 1) id count pc →
    ∃ key, CtaBarK L X (g, (X.tr g).length - 1) key ∧ CtaBarDone L X (g / L.block) key

/-- The rank of a thread: the progress of its state, `0` if it has none. -/
def rankOf (P : Params) (L : Launch) (X : Execution) (g : Nat) : Nat :=
  match stateAt P L X g (X.tr g).length with
  | some (some d) => d.vt + 1
  | _ => 0

/-- The mode of a shuffle site's shuffle. -/
def shflMode : Site → ShflMode
  | .shfl0 => .idx
  | _ => .bfly

/-- The lane operand of a shuffle site's shuffle. -/
def shflOff : Site → Nat
  | .bfa k | .bfb k => bfOff k
  | _ => 0

/-- The operand of a shuffle state's shuffle. -/
def shflOp (g : Nat) (d : D) : Value :=
  match d.site with
  | .shfl0 => b32 (g % 256 / 32)
  | .bfa k => bsumV (ssqV d) d.ra k
  | .bfb k => bfbOp d k
  | _ => b32 0

/-- **A shuffle state fires its shuffle** with every received value. -/
theorem fires_shfl {g : Nat} {d : D} {t : TState} (hs : d.site.isShfl = true) (recv : Value)
    (ok : Bool) : ∃ o, Fires d.site.pc (siteTmpl P g d t)
      ⟨d.site.pc, .shfl (shflMode d.site) (shflOp g d) (shflOff d.site) 31 recv ok⟩ o := by
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.false_eq_true] at hs <;>
    simp only [siteTmpl, hsd, Fires, shflMode, shflOp, shflOff] <;>
    exact ⟨_, recv, ok, rfl, rfl⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **A pending thread is at a state of its machine.** -/
theorem pending_state {g : Nat} (hp : Frame.Pending L X g) :
    ∃ d, stateAt P L X g (X.tr g).length = some (some d) := by
  have hg := hp.1
  cases hσ : stateAt P L X g (X.tr g).length with
  | none =>
    exfalso
    obtain ⟨j, d, e, hj, hσj, hej, hn⟩ := ht.dead hg le_rfl hσ
    obtain ⟨h0, h1, h2⟩ := ht.counts hg hσj
    have hA : At P L X g j d e := ⟨hσj, ht.event hg hej hσj,
      ht.index hg (len_of_get hej).le hσj, ht.inv hg hσj, ht.data hg hσj, h0, h1, h2⟩
    by_cases hx : d.site = .exit
    · obtain ⟨pcx, rfl⟩ := exit_site_of hA.event hx
      have hl := Execution.exit_last hX hg hej
      apply hp.2.2 pcx
      rw [List.getLast?_eq_getElem?, ← hl]
      exact hej
    · exact next_ne_none hpre hX ht hej hA hx hn
  | some σ =>
    cases σ with
    | none => exact absurd hσ (ht.tracked g _ hg)
    | some d => exact ⟨d, rfl⟩

omit hpre hX in
/-- The counts of a thread's trace, at the state at its end. -/
theorem end_counts {g : Nat} (hg : g < L.threads) {d : D}
    (hσ : stateAt P L X g (X.tr g).length = some (some d)) :
    (X.tr g).countP (Execution.isBarId 0) = d.bc0 ∧ (X.tr g).countP (Execution.isBarId 1) = d.bc1 ∧
      (X.tr g).countP Execution.isShfl = d.sc g := by
  have := ht.counts hg hσ
  rwa [List.take_length] at this

/-- **An exited thread made the arrivals and shuffles of all rows of its CTA.** -/
theorem exit_counts {x kx pc : Nat} (hx : X.get (x, kx) = some ⟨pc, .exit⟩) :
    ∃ R, P.Bt ≤ x / 256 + 152 * R ∧ (X.tr x).countP (Execution.isBarId 0) = 2 * R ∧
      (X.tr x).countP (Execution.isBarId 1) = R ∧
      (X.tr x).countP Execution.isShfl = 1 + 5 * (1 + w0 x) * R := by
  have hg := Frame.lt_of_get hX hx
  obtain ⟨-, dx, hA⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
  have hxs := exit_site hA.event
  have hl := Execution.exit_last hX hg hx
  have htr : X.tr x = (X.tr x).take kx ++ [⟨pc, .exit⟩] := by
    conv_lhs => rw [← List.take_append_drop kx (X.tr x)]
    congr 1
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    have : (X.tr x)[kx]? = some ⟨pc, .exit⟩ := hx
    rw [List.getElem?_eq_getElem (by omega)] at this
    rw [Option.some.inj this]
  refine ⟨dx.i, hA.inv.exit hxs, ?_, ?_, ?_⟩ <;> rw [htr, List.countP_append]
  · rw [hA.bc0]; simp [D.bc0, hxs, Execution.isBarId]
  · rw [hA.bc1]; simp [D.bc1, hxs, Execution.isBarId]
  · rw [hA.sc]; simp [D.sc, hxs, Execution.isShfl]

omit hpre ht in
theorem not_canceled {g : Nat} : ¬ ClcCanceled L X g := by
  rintro ⟨-, req, ho⟩
  obtain ⟨i, s, targets, -, ⟨pc, hi⟩, -⟩ := hX.clc.canceled_has_issue ho
  cases noTma_of_consistent noTma hX _ _ _ hi

omit hpre ht in
/-- **No lane of a warp has made more shuffles than a pending lane.** -/
theorem lane_count_le {g h : Nat} (hp : Frame.Pending L X g) (hw : SameWarp L g h) :
    (X.tr h).countP Execution.isShfl ≤ (X.tr g).countP Execution.isShfl := by
  by_contra hlt
  obtain ⟨j, hj⟩ := Step.exists_shflK (X := X) (g := h) (c := (X.tr g).countP Execution.isShfl)
    (by omega)
  obtain ⟨⟨pc, m, a, b, c, r, o, hget⟩, -⟩ := id hj
  rcases Step.shfl_lane_of_ready hX hget hj (sameWarp_symm hw) with ⟨j', hk'⟩ | ⟨k, pcx, hx, -⟩
  · exact Nat.lt_irrefl _ (Step.ShflK.lt_count hk')
  · have hl := Execution.exit_last hX hp.1 hx
    apply hp.2.2 pcx
    rw [List.getLast?_eq_getElem?, ← hl]
    exact hx

omit hpre hX ht in
/-- The shuffles before a shuffle state are fewer than the shuffles of all rows of its CTA. -/
theorem shfl_lt_rows {g R : Nat} {d : D} (hi : Inv P g d) (hs : d.site.isShfl = true)
    (hR : P.Bt ≤ g / 256 + 152 * R) : d.sc g < 1 + 5 * (1 + w0 g) * R := by
  have hb := hi.bfa
  have hb' := hi.bfb
  have hw := w0_le' g
  rcases hsd : d.site <;> simp only [hsd, Site.isShfl, Bool.false_eq_true] at hs <;>
    simp only [D.sc, hsd]
  · omega
  all_goals
    have hr := hi.row (by simp [hsd, Site.inRow])
    simp only [row] at hr
    have hiR : d.i + 1 ≤ R := by omega
    have := Nat.mul_le_mul_left (5 * (1 + w0 g)) hiR
    rw [Nat.mul_succ] at this
  · have := hb _ hsd; omega
  · have := hb' _ hsd
    have : w0 g = 1 := by simp [w0, this.2]
    omega

/-- **A lane of the warp of a thread at a shuffle site** is at that site of its row, or pending
with less progress. -/
theorem lane_lower {g h : Nat} {dg : D} (hp : Frame.Pending L X g)
    (hσ : stateAt P L X g (X.tr g).length = some (some dg)) (hs : dg.site.isShfl = true)
    (hw : SameWarp L g h)
    (hne : ¬ ∃ dh, stateAt P L X h (X.tr h).length = some (some dh) ∧ dh.site = dg.site ∧
      (dg.site ≠ .shfl0 → dh.i = dg.i)) :
    Frame.Pending L X h ∧ rankOf P L X h < rankOf P L X g := by
  have hB := hpre.hyp.block
  have hg := hp.1
  have hh := hw.1.2.1
  have hc : h / 256 = g / 256 := by have := hw.1.2.2; rw [hB] at this; omega
  have hww : h % 256 / 32 = g % 256 / 32 := by have := hw.2; rw [hB] at this; omega
  have hw0 : w0 h = w0 g := by unfold w0; split_ifs <;> omega
  have hig := ht.inv hg hσ
  have hcnt := lane_count_le hX hp hw
  rw [(end_counts ht hg hσ).2.2] at hcnt
  have hex : ∀ pc, (X.tr h).getLast? ≠ some ⟨pc, .exit⟩ := by
    intro pc hl
    have hx : X.get (h, (X.tr h).length - 1) = some ⟨pc, .exit⟩ := by
      unfold Execution.get; rw [← List.getLast?_eq_getElem?]; exact hl
    obtain ⟨R, hR, -, -, hsc⟩ := exit_counts hpre hX ht hx
    rw [hc] at hR
    have := shfl_lt_rows hig hs hR
    rw [hw0] at hsc
    omega
  have hph : Frame.Pending L X h := ⟨hh, not_canceled hX, hex⟩
  refine ⟨hph, ?_⟩
  obtain ⟨dh, hσh⟩ := pending_state hpre hX ht hph
  have hih := ht.inv hh hσh
  have hxh : dh.site ≠ .exit := by
    intro hx
    have hR := hih.exit hx
    rw [hc] at hR
    have hsc := (end_counts ht hh hσh).2.2
    simp only [D.sc, hx, hw0] at hsc
    have := shfl_lt_rows hig hs hR
    omega
  have hle : dh.sc h ≤ dg.sc g := by rw [← (end_counts ht hh hσh).2.2]; exact hcnt
  have hlt := vt_lt_of_sc hig hih hxh hs hw0 hle (fun h' => hne ⟨dh, hσh, h'⟩)
  simp only [rankOf, hσ, hσh]
  omega

omit hpre hX ht in
theorem no_ub_at (hub : ¬ HasUb X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  exact hub ⟨_, pc, f, he⟩

omit hpre hX in
/-- A thread at a state at its end has not exited. -/
theorem last_not_exit {x : Nat} (hx : x < L.threads) {dx : D}
    (hσ : stateAt P L X x (X.tr x).length = some (some dx)) (hl : 0 < (X.tr x).length) :
    ∀ pc, X.get (x, (X.tr x).length - 1) ≠ some ⟨pc, .exit⟩ := by
  intro pc he
  obtain ⟨d1, hσ1⟩ := Frame.stateAt_live ht.tracked hx hσ (Nat.sub_le _ 1)
  have hs := exit_site (ht.event hx he hσ1)
  have h := Frame.stateAt_succ (C := codes P L) (X := X) (g := x) (k := (X.tr x).length - 1) he
  rw [Nat.sub_add_cancel hl, hσ1] at h
  have hn : next P x d1 ⟨pc, .exit⟩ = none := by simp [next, hs]
  have h2 : stateAt P L X x (X.tr x).length = none := by
    show Frame.stateAt (codes P L) X x _ = none
    rw [h]
    exact hn
  rw [hσ] at h2
  cases h2

/-- **The first barrier of a lane at warp 0's first round**: the lane arrived on barrier `0`
for the row, its arrival number `2 i`, at its last event or, for lanes `0..7`, before its load of a
warp sum. -/
theorem bfb0_bar (hub : ¬ HasUb X) {x : Nat} (hx : x < L.threads) {dx : D}
    (hσ : stateAt P L X x (X.tr x).length = some (some dx)) (hs : dx.site = .bfb 0) :
    ∃ pc, X.get (x, rowBase x dx.i + (29 + l0 x)) = some ⟨pc, .bar 0 none⟩ ∧
      ((X.tr x).take (rowBase x dx.i + (29 + l0 x))).countP (Execution.isBarId 0) = 2 * dx.i ∧
      (X.tr x).length = rowBase x dx.i + (29 + l0 x) + 1 + l8 x := by
  have hi := ht.inv hx hσ
  have hr : dx.site.inRow = true := by simp [hs, Site.inRow]
  have hidx := ht.index hx le_rfl hσ
  rw [idx_of_row hr] at hidx
  have hpos : dx.pos x = 30 + l0 x + l8 x := by simp [D.pos, hs]
  have hl0 := l0_le x
  have hl8 := l8_le x
  have hlen : (X.tr x).length = rowBase x dx.i + (29 + l0 x) + 1 + l8 x := by omega
  obtain ⟨e, he⟩ : ∃ e, X.get (x, (X.tr x).length - 1) = some e :=
    ⟨_, List.getElem?_eq_getElem (show (X.tr x).length - 1 < (X.tr x).length by omega)⟩
  have hk : rowBase x dx.i + (29 + l0 x) < (X.tr x).length - 1 ∨
      (rowBase x dx.i + (29 + l0 x) = (X.tr x).length - 1 ∧ ∀ pc, e ≠ ⟨pc, .exit⟩) := by
    rcases Nat.lt_or_eq_of_le (show rowBase x dx.i + (29 + l0 x) ≤ (X.tr x).length - 1 by omega)
      with h | h
    · exact .inl h
    · refine .inr ⟨h, fun pc hpc => ?_⟩
      subst hpc
      exact last_not_exit ht hx hσ (by omega) pc he
  obtain ⟨d', e', he', hA', hi', hp', hr'⟩ := row_state hpre hX ht he (no_ub_at hub he)
    (by unfold rowLen p1; omega) hk
  have hs' := bar0_of_pos hA'.inv hp'
  obtain ⟨t, o, hf⟩ := hA'.event
  simp only [siteTmpl, hs', Fires] at hf
  obtain ⟨rfl, -⟩ := hf
  refine ⟨_, he', ?_, hlen⟩
  rw [hA'.bc0]
  simp [D.bc0, hs', hi']

/-- **The generation of warp 0's first barrier of a row is released** when a lane at the row's
first round of warp 0's butterfly is released. -/
theorem gen_released (hub : ¬ HasUb X) {g : Nat} (hg : g < L.threads) {dg : D}
    (hσ : stateAt P L X g (X.tr g).length = some (some dg)) (hs : dg.site = .bfb 0)
    (hrel : LastReleased L X g) :
    CtaBarrier.Released L.block (X.barriers (g / L.block)) 0 (2 * dg.i) := by
  obtain ⟨pc, hb, hcnt, hlen⟩ := bfb0_bar hpre hX ht hub hg hσ hs
  have hl8 := l8_le g
  have hbar : X.IsBarrier (g, rowBase g dg.i + (29 + l0 g)) 0 none pc := hb
  rcases (by omega : l8 g = 1 ∨ l8 g = 0) with h8 | h8
  · have := released hpre hX ht hbar (by omega)
    rwa [hcnt] at this
  · have hp : rowBase g dg.i + (29 + l0 g) = (X.tr g).length - 1 := by omega
    rw [hp] at hbar
    obtain ⟨key, hk, hdone⟩ := hrel 0 none pc (by omega) hbar
    have hkey := bar_key hpre hX ht hk
    obtain ⟨count, pc', he'⟩ := hk.2.1
    have hid : key % 16 = 0 :=
      (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hbar))).2).1
    rw [hid, ← hp, hcnt] at hkey
    unfold CtaBarDone at hdone
    rwa [hid, hkey] at hdone

/-- **A lane's arrival on warp 0's first barrier of a row is released** once its generation is. -/
theorem lane_bar_released (hub : ¬ HasUb X) {x : Nat} (hx : x < L.threads) {dx : D}
    (hσ : stateAt P L X x (X.tr x).length = some (some dx)) (hs : dx.site = .bfb 0)
    (hgen : CtaBarrier.Released L.block (X.barriers (x / L.block)) 0 (2 * dx.i)) :
    LastReleased L X x := by
  intro id count pc hl hbar
  obtain ⟨pc', hb, hcnt, hlen⟩ := bfb0_bar hpre hX ht hub hx hσ hs
  have hl8 := l8_le x
  have hp : rowBase x dx.i + (29 + l0 x) = (X.tr x).length - 1 := by
    rcases (by omega : l8 x = 1 ∨ l8 x = 0) with h8 | h8
    · exfalso
      have h8' : x % 256 < 8 := by
        by_contra h; simp [l8, h] at h8
      obtain ⟨d1, e1, he1, hA1, -, hp1, hr1⟩ := row_state hpre hX ht hbar (no_ub_at hub hbar)
        (i := dx.i) (q := 30 + l0 x) (by unfold rowLen p1; omega) (.inr ⟨by omega, by
          intro _ h; cases h⟩)
      have hs1 := ldws_of_pos hA1.inv hr1 h8' hp1
      obtain ⟨pcr, a, bs, he2⟩ := rd_event hA1.event (by simp [hs1, Site.isLoad])
      have : X.get (x, (X.tr x).length - 1) = some ⟨pcr, .rd a bs⟩ := by
        rw [show (X.tr x).length - 1 = rowBase x dx.i + (30 + l0 x) by omega, ← he2]; exact he1
      rw [hbar] at this
      cases this
    · omega
  have hbar' : X.IsBarrier (x, rowBase x dx.i + (29 + l0 x)) 0 none pc' := hb
  rw [hp] at hbar'
  obtain ⟨rfl, rfl⟩ : id = 0 ∧ count = none := by
    have := Event.mk.inj (Option.some.inj (hbar.symm.trans hbar'))
    exact ⟨(Kind.bar.inj this.2).1, (Kind.bar.inj this.2).2.1⟩
  have hB := hpre.hyp.block
  refine ⟨0 + 16 * (2 * dx.i), ?_, ?_⟩
  · rw [hp] at hcnt
    exact NamedBar.reached_key_of_release hX (n := 8) (by decide) (target_none hpre)
      (p := Finset.range 8) (by decide) hbar' hx (by rw [hB, Finset.mem_range]; omega) hcnt hgen
      (fun i _ => protocol_prefix hpre hX ht (cta_lt hpre hx) 0 (i + 1)) (Finset.card_range 8)
      (warps_bound hpre)
  · unfold CtaBarDone
    rwa [show (0 + 16 * (2 * dx.i)) % 16 = 0 by omega,
      show (0 + 16 * (2 * dx.i)) / 16 = 2 * dx.i by omega]

omit hpre hX in
/-- **A state after a barrier arrival** is the next site of a barrier site. -/
theorem after_bar {x : Nat} (hx : x < L.threads) {dx : D}
    (hσ : stateAt P L X x (X.tr x).length = some (some dx)) (hl : 0 < (X.tr x).length)
    {id pc : Nat} {c : Option Nat} (hb : X.IsBarrier (x, (X.tr x).length - 1) id c pc) :
    dx.site = .bar1 ∨ dx.site = .ldws ∨ dx.site = .bfb 0 ∨ dx.site = .ldts ∨ dx.site = .ldxa ∨
      dx.site = .exit := by
  obtain ⟨d1, hσ1⟩ := Frame.stateAt_live ht.tracked hx hσ (Nat.sub_le _ 1)
  have hev := ht.event hx hb hσ1
  have h := Frame.stateAt_succ (C := codes P L) (X := X) (g := x) (k := (X.tr x).length - 1) hb
  rw [Nat.sub_add_cancel hl, hσ1] at h
  have hn : next P x d1 ⟨pc, .bar id c⟩ = some (some dx) := by
    have : Frame.stateAt (codes P L) X x (X.tr x).length = some (some dx) := hσ
    rw [h] at this
    exact this
  obtain ⟨-, hs⟩ := bar_site hev
  rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp only [next, h1] at hn <;>
    (try split_ifs at hn) <;> cases hn <;> simp

omit hpre ht in
/-- A released last barrier arrival is ready (DEP-ORDER). -/
theorem ready_of_lastReleased {g : Nat} (hrel : LastReleased L X g) {id pc : Nat}
    {count : Option Nat} (hbar : X.IsBarrier (g, (X.tr g).length - 1) id count pc) :
    Ready L X (g, (X.tr g).length - 1) := by
  have hl : 0 < (X.tr g).length := by have := len_of_get hbar; simp only at this; omega
  obtain ⟨key, hk, hd⟩ := hrel id count pc hl hbar
  exact NamedBar.ready_of_released hX.ctaBar hbar hk hd

/-- **Every lane of the warp at the shuffle: the warp performs it**, a counted extension. -/
theorem shfl_batch (hub : ¬ HasUb X) {g : Nat} {dg : D} (hp : Frame.Pending L X g)
    (hσ : stateAt P L X g (X.tr g).length = some (some dg)) (hs : dg.site.isShfl = true)
    (hrel : LastReleased L X g)
    (hall : ∀ h, SameWarp L g h → ∃ dh, stateAt P L X h (X.tr h).length = some (some dh) ∧
      dh.site = dg.site ∧ (dg.site ≠ .shfl0 → dh.i = dg.i)) :
    ∃ Y, Consistent L kernel Prod mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hB := hpre.hyp.block
  have hb : L.block % 32 = 0 := by rw [hB]
  have hn := noTma_of_consistent noTma hX
  let stOf : Nat → D := fun h => match stateAt P L X h (X.tr h).length with
    | some (some d) => d
    | _ => { site := .shfl0 }
  have hstOf : ∀ h dh, stateAt P L X h (X.tr h).length = some (some dh) → stOf h = dh := by
    intro h dh hσh
    simp only [stOf, hσh]
  have hpend : ∀ h, SameWarp L g h → Frame.Pending L X h := by
    intro h hw
    obtain ⟨dh, hσh, -, -⟩ := hall h hw
    refine ⟨hw.1.2.1, not_canceled hX, fun pc hlast => ?_⟩
    have hl : 0 < (X.tr h).length := by
      rcases hx : X.tr h with _ | ⟨e, es⟩
      · rw [hx] at hlast; cases hlast
      · simp
    apply last_not_exit ht hw.1.2.1 hσh hl pc
    unfold Execution.get
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  refine Step.shfl_counted_extension hX hb (pc := dg.site.pc) (m := shflMode dg.site)
    (fun h => shflOp h (stOf h)) (fun _ => shflOff dg.site) (fun _ => 31) hp.1 ?_ ?_ ?_ ?_
  · intro h _
    right
    rintro ⟨i, s, ts, pc, hi⟩
    cases hn _ _ _ hi
  · intro h hw
    obtain ⟨dh, hσh, hsite, hih⟩ := hall h hw
    have hh := hw.1.2.1
    have hrelh : LastReleased L X h := by
      by_cases h0 : dg.site = .bfb 0
      · have hgen := gen_released hpre hX ht hub hp.1 hσ h0 hrel
        have hc : h / L.block = g / L.block := hw.1.2.2.symm
        exact lane_bar_released hpre hX ht hub hh hσh (hsite.trans h0)
          (by rw [hc, hih (by rw [h0]; simp)]; exact hgen)
      · intro id count pc hl hbar
        exfalso
        rcases after_bar ht hh hσh hl hbar with h1 | h1 | h1 | h1 | h1 | h1 <;>
          rw [hsite] at h1 <;> rw [h1] at hs h0 <;> simp [Site.isShfl] at hs h0
    exact Execution.NoTma.released hn fun _ _ _ hbar => ready_of_lastReleased hX hrelh hbar
  · intro h hw recv ok
    obtain ⟨dh, hσh, hsite, -⟩ := hall h hw
    have hh := hw.1.2.1
    obtain ⟨t, hrun⟩ := Frame.run_some hX hub (hpend h hw)
    obtain ⟨t1, hl, hpc, hout⟩ := ht.fire hh hrun hσh
    have hsh : dh.site.isShfl = true := by rw [hsite]; exact hs
    obtain ⟨o, hf⟩ := fires_shfl (P := P) (g := h) (d := dh) (t := t1) hsh recv ok
    refine ⟨t, t1, o, hrun, hl, siteTmpl P h dh t1, hout, ?_⟩
    rw [hpc, hstOf h dh hσh, ← hsite]
    exact hf
  · intro ev _ a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> trivial

end
end PTX.Kernels.RmsNorm.Proof
