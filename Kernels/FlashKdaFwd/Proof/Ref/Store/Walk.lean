-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # Store phase: from one trace position to its neighbours

The invariant `Inv` speaks about one trace position. Several contract fields relate two
positions of a thread ("the write is the fifth event after the vector load", "between the store
and the arrival there is a group wait"). This file has the tools for that, all from the
invariant, the explicit successor relation of the positions (`Step`, `Steps.lean`) and the
ledger; tracking (`Frame.Tracked`) is not assumed anywhere.

* `Entered P L X g k0`: the thread is at the entry of the phase before its event `k0` (the
  entry condition `In` at a followed state). `Left P L X g k0 k`: it has left the phase at a
  position between `k0` and `k` (the exit condition `Out` at a followed state).
* `Pos.tile`: the tile of a position (0 at the entry); `tile_of`, `lead_of`: a position other
  than the entry is a position of the store leader inside a tile of its sequence.
* `not_out`: **inside the phase means not past it**: a position with the invariant has no exit
  condition at or before it (the exit ledger has more `bar.sync 0` than the entry and more
  arrivals than any tile).
* `inv_before`: the invariant at a position gives the invariant at every earlier position from
  the entry on.
* `pos_unique`: **a state and a ledger determine the position.**
* `pred`: **one step back**: the state before a position other than the entry is at a
  predecessor position (`Step`), with its invariant.
* `succ`: **one step forward**: when a later event of the thread is not undefined behaviour,
  the state after an invariant state is at a successor position with its invariant, or it is
  the exit.
* `InChunk t row c n pos`: the position is the `n`-th of the twelve positions of the chunk
  `(t, row, c)` of a partial tile (four element reads, eight global stores).
* `chunk_back`: a state at the `n`-th position of a chunk was at the chunk's vector load `n`
  events earlier. `chunk_fwd`: from the vector load of a chunk, the state `n ≤ 11` events later
  is at the `n`-th position of the chunk, when an event exists there that is not undefined
  behaviour. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Positions -/

/-- **The tile of a position**: 0 at the entry, the tile being stored elsewhere. -/
def Pos.tile : Pos → Nat
  | .entry => 0
  | .wait t => t
  | .ts t _ => t
  | .commit t => t
  | .ld0 t _ _ => t
  | .ld1 t _ _ _ => t
  | .ld2 t _ _ _ _ => t
  | .ld3 t _ _ _ _ _ => t
  | .gst t _ _ _ => t
  | .bwait t => t
  | .arrive t => t

/-- A state at a position other than the entry has the registers of the tile loop. -/
theorem tile_of {pos : Pos} {d : D} (hr : RefAt P g pos d) (hp : pos ≠ .entry) :
    Tile P g pos.tile d := by
  have h := hr.pos
  cases pos with
  | entry => exact absurd rfl hp
  | _ => exact h.1

/-- **A position other than the entry is the store leader's, inside a tile of its sequence.** -/
theorem lead_of {pos : Pos} {d : D} (hr : RefAt P g pos d) (hp : pos ≠ .entry) :
    lane g = 0 ∧ pos.tile < tiles (P.length (seqOf P g)) :=
  ⟨(tile_of hr hp).1, (tile_of hr hp).2.1⟩

/-- No position of the phase is at the exit site. -/
theorem site_ne_exit (pos : Pos) : pos.site ≠ .bar 7 := by
  cases pos <;> simp [Pos.site]

/-! ### Projections of the ledger of a position -/

theorem led_bars {len : Nat} {pos : Pos} (hp : pos ≠ .entry) : (led len pos).bars = 6 := by
  cases pos <;> first
    | exact absurd rfl hp
    | rfl
    | (simp only [led]; split_ifs <;> rfl)

theorem led_pollS (len : Nat) (pos : Pos) : (led len pos).pollS = 1 := by
  cases pos <;> first
    | rfl
    | (simp only [led]; split_ifs <;> rfl)

/-- The arrivals on the two "store empty" mbarriers before a position: one per earlier tile. -/
theorem led_arr {len : Nat} {pos : Pos} (hp : pos ≠ .entry) :
    (led len pos).arrE0 = (pos.tile + 1) / 2 ∧ (led len pos).arrE1 = pos.tile / 2 := by
  cases pos <;> first
    | exact absurd rfl hp
    | exact ⟨rfl, rfl⟩
    | (simp only [led]; split_ifs <;> exact ⟨rfl, rfl⟩)

/-- The successful polls of the two "store full" mbarriers before a position: one per earlier
tile, and the tile's own after its poll. -/
theorem led_poll {len : Nat} {pos : Pos} (hp : pos ≠ .entry) :
    (led len pos).pollF0 + (led len pos).pollF1 =
      pos.tile + (match pos with | .wait _ => 0 | _ => 1) := by
  cases pos <;> first
    | exact absurd rfl hp
    | (simp only [led, ledIn, Pos.tile]; omega)
    | (simp only [led, ledIn, Pos.tile]; split_ifs <;> simp only [] <;> omega)

/-- The ledger of the exit of the store leader of a nonempty sequence. -/
theorem ledExit_lead (hl : lane g = 0) (hlen : 1 ≤ P.length (seqOf P g)) :
    ledExit P g = ⟨6, 1, (tiles (P.length (seqOf P g)) + 1) / 2,
      tiles (P.length (seqOf P g)) / 2, (tiles (P.length (seqOf P g)) + 1) / 2,
      tiles (P.length (seqOf P g)) / 2, 16 * (P.length (seqOf P g) / 16),
      P.length (seqOf P g) / 16, tiles (P.length (seqOf P g)),
      128 * (P.length (seqOf P g) % 16)⟩ := by
  simp only [ledExit, hl, hlen, and_self, ↓reduceIte]

theorem ledExit_bars (P : Params) (g : Nat) : (ledExit P g).bars = 6 := by
  unfold ledExit
  split_ifs <;> rfl

/-- A count over a shorter prefix is at most the count over a longer one. -/
theorem take_count_le (c : Event → Bool) {j k : Nat} (h : j ≤ k) :
    ((X.tr g).take j).countP c ≤ ((X.tr g).take k).countP c :=
  (List.take_sublist_take_left h).countP_le

/-! ### Inside the phase -/

/-- **The thread is at the entry of the store phase before its event `k0`**: the entry
condition `In` (`Interface.lean`) holds at a followed state. The phases before this one prove
it for every thread of the store warp. -/
def Entered (P : Params) (L : Launch) (X : Execution) (g k0 : Nat) : Prop :=
  ∃ s0, Frame.stateAt (code L) X g k0 = some (some s0) ∧ In P X g k0 s0

/-- **The thread has left the store phase** at a position between `k0` and `k`: the exit
condition `Out` held at a followed state there. -/
def Left (P : Params) (L : Launch) (X : Execution) (g k0 k : Nat) : Prop :=
  ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ Frame.stateAt (code L) X g j = some (some s1) ∧ Out P X g j s1

/-- The entry is not the start of the trace: five `bar.sync 0` precede it. -/
theorem Entered.pos {k0 : Nat} (h : Entered P L X g k0) : 0 < k0 := by
  obtain ⟨s0, -, hin⟩ := h
  rcases Nat.eq_zero_or_pos k0 with rfl | h
  · have := hin.2
    simp [ledOf, ledEntry] at this
  · exact h

/-- **Inside the phase means not past it**: a position with its ledger excludes the exit
condition at the same or an earlier trace position. -/
theorem not_out {k j : Nat} {s s1 : D} {pos : Pos} (hr : RefAt P g pos s)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos)
    (ho : Out P X g j s1) (hj : j ≤ k) : False := by
  by_cases hp : pos = .entry
  · have h1 : ((X.tr g).take j).countP (Execution.isBarId 0) = 6 :=
      (congrArg Led.bars ho.2).trans (ledExit_bars P g)
    have h2 : ((X.tr g).take k).countP (Execution.isBarId 0) = 5 := by
      have := congrArg Led.bars hl
      rw [hp] at this
      exact this
    have := take_count_le (X := X) (g := g) (Execution.isBarId 0) hj
    omega
  · obtain ⟨hl0, ht⟩ := lead_of hr hp
    have hlen : 1 ≤ P.length (seqOf P g) := by
      unfold tiles at ht
      omega
    have he := ho.2
    rw [ledExit_lead hl0 hlen] at he
    have a0 : arrivals (emptyBar P g 0) ((X.tr g).take j) = _ := congrArg Led.arrE0 he
    have a1 : arrivals (emptyBar P g 1) ((X.tr g).take j) = _ := congrArg Led.arrE1 he
    have b0 : arrivals (emptyBar P g 0) ((X.tr g).take k) = _ :=
      (congrArg Led.arrE0 hl).trans (led_arr hp).1
    have b1 : arrivals (emptyBar P g 1) ((X.tr g).take k) = _ :=
      (congrArg Led.arrE1 hl).trans (led_arr hp).2
    have c0 := take_count_le (X := X) (g := g) (arrivesOn (emptyBar P g 0)) hj
    have c1 := take_count_le (X := X) (g := g) (arrivesOn (emptyBar P g 1)) hj
    simp only [arrivals] at a0 a1 b0 b1
    omega

/-- Two positions other than the entry with one ledger are in one tile. -/
theorem tile_eq {len : Nat} {pos pos' : Pos} (hp : pos ≠ .entry) (hp' : pos' ≠ .entry)
    (hl : led len pos = led len pos') : pos.tile = pos'.tile := by
  have a := led_arr (len := len) hp
  have b := led_arr (len := len) hp'
  rw [hl] at a
  have h0 := a.1.symm.trans b.1
  have h1 := a.2.symm.trans b.2
  omega

/-- **A state and a ledger determine the position**: two positions whose register facts hold
of one state and whose ledgers agree are one. -/
theorem pos_unique {pos pos' : Pos} {d : D} (h1 : RefAt P g pos d) (h2 : RefAt P g pos' d)
    (hl : led (P.length (seqOf P g)) pos = led (P.length (seqOf P g)) pos') : pos = pos' := by
  have hs : pos.site = pos'.site := h1.site.symm.trans h2.site
  have p1 := h1.pos
  have p2 := h2.pos
  have eg := congrArg Led.gstores hl
  cases pos with
  | entry => cases pos' <;> first | rfl | exact absurd hs (by simp [Pos.site])
  | wait t =>
    cases pos' with
    | wait t' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])
  | ts t i =>
    cases pos' with
    | ts t' i' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hi : i = i' := by
        simp only [Pos.site, Site.tensorCopy.injEq, Fin.mk.injEq] at hs
        exact Fin.ext (by omega)
      rw [ht, hi]
    | _ => exact absurd hs (by simp [Pos.site])
  | commit t =>
    cases pos' with
    | commit t' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])
  | ld0 t r c =>
    cases pos' with
    | ld0 t' r' c' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hc1 : c < 16 := p1.2.2.2.1
      have hc2 : c' < 16 := p2.2.2.2.1
      simp only [led, ledIn] at eg
      obtain ⟨rfl, rfl⟩ : r = r' ∧ c = c' := by constructor <;> omega
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])
  | ld1 t r c v0 =>
    cases pos' with
    | ld1 t' r' c' v0' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hc1 : c < 16 := p1.2.2.2.1
      have hc2 : c' < 16 := p2.2.2.2.1
      simp only [led, ledIn] at eg
      obtain ⟨rfl, rfl⟩ : r = r' ∧ c = c' := by constructor <;> omega
      simp only [Pos.site, Site.loadEl1.injEq, true_and] at hs
      rw [ht, hs]
    | _ => exact absurd hs (by simp [Pos.site])
  | ld2 t r c v0 v1 =>
    cases pos' with
    | ld2 t' r' c' v0' v1' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hc1 : c < 16 := p1.2.2.2.1
      have hc2 : c' < 16 := p2.2.2.2.1
      simp only [led, ledIn] at eg
      obtain ⟨rfl, rfl⟩ : r = r' ∧ c = c' := by constructor <;> omega
      simp only [Pos.site, Site.loadEl2.injEq, true_and] at hs
      rw [ht, hs.1, hs.2]
    | _ => exact absurd hs (by simp [Pos.site])
  | ld3 t r c v0 v1 v2 =>
    cases pos' with
    | ld3 t' r' c' v0' v1' v2' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hc1 : c < 16 := p1.2.2.2.1
      have hc2 : c' < 16 := p2.2.2.2.1
      simp only [led, ledIn] at eg
      obtain ⟨rfl, rfl⟩ : r = r' ∧ c = c' := by constructor <;> omega
      simp only [Pos.site, Site.loadEl3.injEq, true_and] at hs
      rw [ht, hs.1, hs.2.1, hs.2.2]
    | _ => exact absurd hs (by simp [Pos.site])
  | gst t r c j =>
    cases pos' with
    | gst t' r' c' j' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      have hc1 : c < 16 := p1.2.2.2.1
      have hc2 : c' < 16 := p2.2.2.2.1
      have hj : j = j' := by
        simp only [Pos.site, Site.store.injEq, Fin.mk.injEq] at hs
        exact Fin.ext (by omega)
      subst hj
      simp only [led, ledIn] at eg
      obtain ⟨rfl, rfl⟩ : r = r' ∧ c = c' := by constructor <;> omega
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])
  | bwait t =>
    cases pos' with
    | bwait t' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])
  | arrive t =>
    cases pos' with
    | arrive t' =>
      have ht := tile_eq (by intro h; cases h) (by intro h; cases h) hl
      simp only [Pos.tile] at ht
      rw [ht]
    | _ => exact absurd hs (by simp [Pos.site])

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The invariant from the entry on**: `store_inv` for a thread that entered. -/
theorem inv_at {k0 k : Nat} {s : D} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (hk : k < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    Inv P X g k s ∨ Left P L X g k0 k := by
  obtain ⟨s0, h0, hin⟩ := hen
  exact store_inv hpre hX hg h0 hin hk0 hk hσ

/-- **The invariant at a position gives the invariant at every earlier position** from the
entry on. -/
theorem inv_before {k0 k k' : Nat} {s' : D} {pos' : Pos} (hen : Entered P L X g k0)
    (hk0 : k0 ≤ k) (hkk : k ≤ k') (hk : k < (X.tr g).length)
    (hσ' : Frame.stateAt (code L) X g k' = some (some s')) (hr' : RefAt P g pos' s')
    (hl' : ledOf P g ((X.tr g).take k') = led (P.length (seqOf P g)) pos') :
    ∃ s, Frame.stateAt (code L) X g k = some (some s) ∧ Inv P X g k s := by
  obtain ⟨s, hσ⟩ := followed_of_le hσ' hkk
  rcases inv_at hpre hX hg hen hk0 hk hσ with h | ⟨j, s1, -, hj, -, ho⟩
  · exact ⟨s, hσ, h⟩
  · exact (not_out hr' hl' ho (by omega)).elim

/-- **One step back**: the state before a position other than the entry is at a predecessor
position with its register facts and ledger. -/
theorem pred {k0 k : Nat} {s' : D} {pos' : Pos} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (hk : k < (X.tr g).length) (hσ' : Frame.stateAt (code L) X g k = some (some s'))
    (hr' : RefAt P g pos' s')
    (hl' : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos')
    (hne : pos' ≠ .entry) :
    0 < k ∧ k0 ≤ k - 1 ∧ ∃ s pos e, Frame.stateAt (code L) X g (k - 1) = some (some s) ∧
      X.get (g, k - 1) = some e ∧ RefAt P g pos s ∧
      ledOf P g ((X.tr g).take (k - 1)) = led (P.length (seqOf P g)) pos ∧
      Step (P.length (seqOf P g)) pos pos' := by
  have hpos := hen.pos
  have hkk : k ≠ k0 := by
    rintro rfl
    obtain ⟨s0, h0, hin⟩ := hen
    have h1 := congrArg Led.bars (hl'.symm.trans hin.2)
    rw [led_bars hne] at h1
    cases h1
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine ⟨by omega, by omega, ?_⟩
  obtain ⟨s, hσ, pos, hr, hl⟩ :=
    inv_before hpre hX hg hen (k := j) (by omega) (Nat.le_succ j) (by omega) hσ' hr' hl'
  obtain ⟨e, he⟩ : ∃ e, X.get (g, j) = some e :=
    ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, j + 1) = some e' := ⟨_, List.getElem?_eq_getElem hk⟩
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    have := ub_last hX he he'
    omega
  have hn : Thread.next L g s e = some (some s') := by
    rw [Frame.stateAt_succ he, hσ] at hσ'
    exact hσ'
  rcases inv_step_at hpre hX hg he hσ hr hl hub hn with ⟨pos₁, h1, h2, h3⟩ | ⟨-, hE, -⟩
  · obtain rfl : pos₁ = pos' := pos_unique h1 hr' (h2.symm.trans hl')
    exact ⟨s, pos, e, hσ, he, hr, hl, h3⟩
  · exact absurd (hr'.site.symm.trans hE.site) (site_ne_exit pos')

omit hg in
/-- A later event that is not undefined behaviour keeps the machine from having stopped. -/
theorem alive {k j : Nat} {e' : Event} (he' : X.get (g, j) = some e')
    (hub' : ∀ pc f, e' ≠ ⟨pc, .ub f⟩) (hkj : k ≤ j) :
    Frame.stateAt (code L) X g k ≠ none := by
  intro h
  have hn := Frame.stateAt_none_mono h hkj
  rcases Frame.fired (fun g hg => Thread.sound hpre hg) hX he' with ⟨σ, o, hσ, -⟩ |
    ⟨-, pc, f, rfl⟩
  · rw [hn] at hσ
    cases hσ
  · exact hub' pc f rfl

/-- **One step forward**: when a later event of the thread exists and is not undefined
behaviour, the state after an invariant state is followed, and it is at a successor position
with its register facts and ledger, or it satisfies the exit condition. -/
theorem succ {k j : Nat} {s : D} {pos : Pos} {e e' : Event}
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hr : RefAt P g pos s)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos)
    (he : X.get (g, k) = some e) (he' : X.get (g, j) = some e')
    (hub' : ∀ pc f, e' ≠ ⟨pc, .ub f⟩) (hkj : k < j) :
    ∃ s', Frame.stateAt (code L) X g (k + 1) = some (some s') ∧
      Thread.next L g s e = some (some s') ∧
      ((∃ pos', RefAt P g pos' s' ∧
          ledOf P g ((X.tr g).take (k + 1)) = led (P.length (seqOf P g)) pos' ∧
          Step (P.length (seqOf P g)) pos pos') ∨ (pos.canExit ∧ Out P X g (k + 1) s')) := by
  have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
    rintro pc f rfl
    have := ub_last hX he he'
    omega
  have ha := alive hpre hX he' hub' (k := k + 1) (by omega)
  have hs := Frame.stateAt_succ (C := code L) he
  rw [hσ] at hs
  have hf := store_followed hpre hg (e := e) hσ ⟨pos, hr, hl⟩
  cases hn : Thread.next L g s e with
  | none =>
    exact absurd (hs.trans hn) ha
  | some o =>
    cases o with
    | none => exact absurd hn hf
    | some s' =>
      exact ⟨s', hs.trans hn, rfl, inv_step_at hpre hX hg he hσ hr hl hub hn⟩

end

/-! ### The twelve positions of a chunk -/

/-- **The position is the `n`-th of the chunk `(t, row, c)`**: the four element reads of the
vector load (`n` from 0 to 3), then the eight global stores (`n = 4 + j`). -/
def InChunk (t row c n : Nat) : Pos → Prop
  | .ld0 t' r' c' => t' = t ∧ r' = row ∧ c' = c ∧ n = 0
  | .ld1 t' r' c' _ => t' = t ∧ r' = row ∧ c' = c ∧ n = 1
  | .ld2 t' r' c' _ _ => t' = t ∧ r' = row ∧ c' = c ∧ n = 2
  | .ld3 t' r' c' _ _ _ => t' = t ∧ r' = row ∧ c' = c ∧ n = 3
  | .gst t' r' c' j => t' = t ∧ r' = row ∧ c' = c ∧ n = 4 + j.val
  | _ => False

variable {t row c n : Nat} {pos pos' : Pos}

theorem InChunk.ne_entry (h : InChunk t row c n pos) : pos ≠ .entry := by
  rintro rfl
  exact h

theorem InChunk.not_exit (h : InChunk t row c n pos) : ¬ pos.canExit := by
  cases pos <;> first | exact h.elim | exact fun h' => h'

/-- The first position of a chunk is its vector load. -/
theorem InChunk.zero (h : InChunk t row c 0 pos) : pos = .ld0 t row c := by
  cases pos <;> simp only [InChunk] at h <;> first
    | exact h.elim
    | (obtain ⟨rfl, rfl, rfl, h4⟩ := h; first | rfl | (exfalso; omega))

/-- The position `4 + j` of a chunk is its global store `j`. -/
theorem InChunk.gst {j : Fin 8} (h : InChunk t row c (4 + j.val) pos) : pos = .gst t row c j := by
  cases pos with
  | gst t' r' c' j' =>
    obtain ⟨rfl, rfl, rfl, h4⟩ := h
    obtain rfl : j = j' := Fin.ext (by omega)
    rfl
  | ld0 t' r' c' => exact absurd h.2.2.2 (by omega)
  | ld1 t' r' c' v0 => exact absurd h.2.2.2 (by omega)
  | ld2 t' r' c' v0 v1 => exact absurd h.2.2.2 (by omega)
  | ld3 t' r' c' v0 v1 v2 => exact absurd h.2.2.2 (by omega)
  | _ => exact False.elim h

/-- The successor of the `n`-th position of a chunk is its `(n + 1)`-th position. -/
theorem InChunk.step {len : Nat} (h : InChunk t row c n pos) (hn : n < 11)
    (hs : Step len pos pos') : InChunk t row c (n + 1) pos' := by
  cases hs <;> simp only [InChunk, finVal] at h ⊢ <;> first
    | exact h.elim
    | (obtain ⟨h1, h2, h3, h4⟩ := h
       first
        | exact ⟨h1, h2, h3, by omega⟩
        | (exfalso; omega))

/-- The predecessor of the `(n + 1)`-th position of a chunk is its `n`-th position. -/
theorem InChunk.pred {len : Nat} (h : InChunk t row c (n + 1) pos') (hs : Step len pos pos') :
    InChunk t row c n pos := by
  cases hs <;> simp only [InChunk, finVal] at h ⊢ <;> first
    | exact h.elim
    | (obtain ⟨h1, h2, h3, h4⟩ := h
       first
        | exact ⟨h1, h2, h3, by omega⟩
        | (exfalso; omega))

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **Forward along a chunk**: from a state at the vector load of a chunk, the state `n ≤ 11`
events later is at the `n`-th position of the chunk, with its register facts and ledger, when
an event exists there that is not undefined behaviour. -/
theorem chunk_fwd {k : Nat} {s : D} (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hr : RefAt P g pos s)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos)
    (hc : InChunk t row c 0 pos) (n : Nat) (hn : n ≤ 11) {e' : Event}
    (he' : X.get (g, k + n) = some e') (hub' : ∀ pc f, e' ≠ ⟨pc, .ub f⟩) :
    ∃ s' pos', Frame.stateAt (code L) X g (k + n) = some (some s') ∧ RefAt P g pos' s' ∧
      ledOf P g ((X.tr g).take (k + n)) = led (P.length (seqOf P g)) pos' ∧
      InChunk t row c n pos' := by
  induction n generalizing e' with
  | zero => exact ⟨s, pos, hσ, hr, hl, hc⟩
  | succ n ih =>
    have hlen : k + (n + 1) < (X.tr g).length := (List.getElem?_eq_some_iff.mp he').1
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k + n) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k + n < (X.tr g).length by omega)⟩
    have hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
      rintro pc f rfl
      have := ub_last hX he he'
      omega
    obtain ⟨s1, pos1, hσ1, hr1, hl1, hc1⟩ := ih (by omega) he hub
    obtain ⟨s', hσ', -, hsucc⟩ :=
      succ hpre hX hg hσ1 hr1 hl1 he he' hub' (show k + n < k + (n + 1) by omega)
    rcases hsucc with ⟨pos', h1, h2, h3⟩ | ⟨hx, -⟩
    · exact ⟨s', pos', hσ', h1, h2, hc1.step (by omega) h3⟩
    · exact absurd hx hc1.not_exit

/-- **Back along a chunk**: a state at the `n`-th position of a chunk was at the chunk's vector
load `n` events earlier. -/
theorem chunk_back {k0 k : Nat} {s : D} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (hk : k < (X.tr g).length) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hr : RefAt P g pos s)
    (hl : ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos)
    (hc : InChunk t row c n pos) :
    n ≤ k ∧ k0 ≤ k - n ∧ ∃ d0, Frame.stateAt (code L) X g (k - n) = some (some d0) ∧
      RefAt P g (.ld0 t row c) d0 ∧
      ledOf P g ((X.tr g).take (k - n)) = led (P.length (seqOf P g)) (.ld0 t row c) := by
  induction n generalizing k s pos with
  | zero =>
    obtain rfl := hc.zero
    exact ⟨Nat.zero_le _, hk0, s, hσ, hr, hl⟩
  | succ n ih =>
    obtain ⟨h1, h2, s1, pos1, e1, hσ1, -, hr1, hl1, hst⟩ :=
      pred hpre hX hg hen hk0 hk hσ hr hl hc.ne_entry
    obtain ⟨h3, h4, d0, h5, h6, h7⟩ := ih h2 (by omega) hσ1 hr1 hl1 (hc.pred hst)
    have e : k - (n + 1) = k - 1 - n := by omega
    rw [e]
    exact ⟨by omega, h4, d0, h5, h6, h7⟩

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
