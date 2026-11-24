-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftValBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPKeys

@[expose] public section

/-! # `ValueFacts.soft`: the softmax values

For scores `S` its loads returned (`SoftLoads`), a softmax thread's values are the recurrence
`softC P S`, `softL P S` (`FactsSoftValBase`). At its state, the reference and the row sum are
the recurrence of the trace prefix's scores (`Counts.refs`), the state's scores are the tile's
loaded scores (`words_scores`), and those are `S` on loaded tiles (`soft_tsc_S`):

* a probability store of tile `u` writes, at source `p` of the store of columns `64 + 16 c …`,
  the pack of keys `32 c + 2 p` and `32 c + 2 p + 1` (`pst_keys_*`; the low half is the lower
  key, as `pKey`), each `2 ^ (P.scale · S u k - softC u)` (`p0_eq`, `p1_eq`, the reference
  `refM` of the tile);
* the store of the rescale factor of loop trip `t` (generation `(n + 1) j + 1 + t`) reads as
  `2 ^ (c (n j + t) - c (n j + t + 1))` (`alpha_eq`); the store of the row sum (generation
  `(n + 1) j + n`) is the row sum after the item's last tile. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The probability of key `k` at a store site of the first tile (`p0`) or a loop tile (`p1`). -/
def pkVal (L : Launch) (lp : Bool) (d : Softmax.D) (k : Nat) : ℝ :=
  if lp then Softmax.p1 L d k else Softmax.p0 L d k

/-- The keys of every store site, when the scale word reads as a number and the reference and
the words are single-precision payloads. -/
theorem pst_keys {g : Nat} {d : Softmax.D} {t : TState} {ta : Nat} {ss : List Opnd} {lp : Bool}
    {c : Fin 4} (hsc : Softmax.ScaleOk L) {x : ℝ} (hm : d.m = .float .f32 x)
    (hwf : Softmax.WordsF32 d.w) (hs : d.site = .pst lp c) (h : Holds t.regs (Softmax.facts L g d))
    (hc : kernel.code[(Softmax.Site.pst lp c).pc]? = some ⟨none, .tcSt ta ss⟩) :
    ∀ p < 16, ∃ r, ss[p]? = some (.reg r) ∧ t.regs r = some (.pair
      (.float .f16 (pkVal L lp d (32 * c.val + 2 * p)))
      (.float .f16 (pkVal L lp d (32 * c.val + 2 * p + 1)))) := by
  cases lp <;> rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
  · exact Softmax.pst_keys_0 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_1 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_2 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_3 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_4 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_5 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_6 hsc hm hwf hs h hc
  · exact Softmax.pst_keys_7 hsc hm hwf hs h hc

/-- The reading of a reference that is a single-precision payload. -/
theorem mR_of {d : Softmax.D} {x : ℝ} (h : d.m = .float .f32 x) : d.mR = x := by
  rw [Softmax.D.mR, h, Softmax.rd32_float]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

set_option maxHeartbeats 1000000 in
/-- **`SoftValues.pStore`.** -/
theorem SoftValues_pStore {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) :
    SoftPStores L X h fun u k => (2 : ℝ) ^ (P.scale * S u k - softC P S u) := by
  intro i a p u vals hst hsp hp
  obtain ⟨pc, he⟩ := hst
  obtain ⟨d, t, ins, o, -, hc, hi, hat, hcode, hf, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  have hscE := soft_sc_eq hpre
  have hnE := soft_trips_eq hpre
  have hsc0 := Softmax.scale_ok hpre
  have hF := soft_loadsF32 hpre hX ht hw hS i
  obtain ⟨hH, hRl⟩ := hc.refs hF hsc0
  cases hsd : d.site with
  | pst lp cc =>
    simp only [Softmax.Ev, hsd] at hev
    obtain ⟨vals', hk⟩ := hev
    injection hk with hk
    injection hk with ha hv
    subst ha hv
    obtain ⟨ta, ss, hcd, hl⟩ := pst_len lp cc
    rw [hsd] at hcode hf
    obtain rfl := Option.some.inj (hcode.symm.trans hcd)
    have hp16 : p < 16 := by rw [fires_tcSt_len (fun _ h => by cases h) hf rfl, hl] at hp; exact hp
    have hwf := Softmax.words_f32 hc.words hF (by simp [Softmax.chunks, hsd])
    obtain ⟨xm, hmx⟩ : ∃ x, d.m = .float .f32 x := by
      cases lp
      · exact ⟨_, hH (by rw [hsd]; rfl)⟩
      · exact ⟨_, (hRl (.inl (by rw [hsd]; rfl))).1⟩
    obtain ⟨r, hss, hr⟩ := pst_keys hsc0 hmx hwf hsd hat.2.2.2.2 hcd p hp16
    rw [fires_tcSt_vals (fun _ h => by cases h) hf rfl hss hr]
    have hkey : pKey L h (Softmax.tmem L h (64 + 16 * cc.val)) p = 32 * cc.val + 2 * p := by
      unfold pKey
      rw [soft_column L h h _ _ hw (by omega)]
      have : Softmax.stOf L h = warpOf L h / 4 := rfl
      omega
    rw [hkey]
    -- the tile and its loads
    obtain ⟨h1, h2, -, h0⟩ := soft_tile hpre hi (.inr ⟨lp, cc, hsd⟩)
    have hu : u = Softmax.trips L * d.i + Softmax.tileNo d := by
      unfold sPolls at hsp; rw [soft_sFullBar, hc.score, h1] at hsp; omega
    have hld : Softmax.ldPos d = 4 * Softmax.tileNo d + 4 := by
      obtain ⟨site, ii, tt, w, mm, ll⟩ := d
      simp only at hsd ⊢
      subst hsd
      cases lp <;> simp [Softmax.ldPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip]
    have h4 : 4 * u + 4 ≤ tcLdsIn (Softmax.tmem L h 0) (Softmax.tmem L h 128)
        ((X.tr h).take i) := by
      rw [hc.tcLd, hld, hu]; ring_nf; omega
    have hsc := Softmax.words_scores hc.words hF (by simp [Softmax.chunks, hsd])
    rw [← hu] at hsc
    have hsS : ∀ k < 128, d.s k = S u k := fun k hk =>
      (hsc k hk).trans (soft_tsc_S hpre hX ht hw hS h4 hk)
    -- the probability of a key
    have hp1 : ∀ k < 128, pkVal L lp d k = (2 : ℝ) ^ (P.scale * S u k - softC P S u) := by
      intro k hk
      cases lp
      · have hT : Softmax.tileNo d = 0 := (h0.mp (by rw [hsd]; rfl))
        rw [hT, Nat.add_zero] at hu
        have hm := mR_of (hH (by rw [hsd]; rfl))
        rw [← hu, soft_refM_S hpre hX ht hw hS h4] at hm
        simp only [pkVal, Bool.false_eq_true, ↓reduceIte]
        rw [Softmax.p0_eq, hsS k hk, hm, hscE, softC, hnE]
      · have htr := hi.trip (by rw [hsd]; rfl)
        have hT : Softmax.tileNo d = d.t + 1 := by
          simp [Softmax.tileNo, hsd, Softmax.Site.tile0]
        rw [hT] at hu
        have hm := mR_of (hRl (.inl (by rw [hsd]; rfl))).1
        rw [soft_refM_S hpre hX ht hw hS (u := Softmax.trips L * d.i + d.t) (by omega)] at hm
        have hmod : (Softmax.trips L * d.i + d.t + 1) % Softmax.trips L ≠ 0 := by
          rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          omega
        rw [hscE] at hm
        have hmN := soft_mN_refM (n := Softmax.trips L) hscE hm
          (fun j hj => by rw [hsS j hj, hu, Nat.add_assoc]) hmod
        simp only [pkVal, ↓reduceIte]
        rw [Softmax.p1_eq, hsS k hk, hmN, hscE, softC, hu, Nat.add_assoc, hnE]
    rw [hp1 _ (by omega), hp1 _ (by omega)]
  | _ => all_goals exfalso; simp [Softmax.Ev, hsd] at hev

/-- The statistics store of a softmax thread at generation `(n + 1) j + 1 + t` (`t + 1 < n`) is
loop trip `t`'s store of the rescale factor, at a state of item `j` and trip `t`; at generation
`(n + 1) j + n` it is item `j`'s store of the row sum, at its last trip. -/
theorem soft_store_gen {g i pc : Nat} {a : Acc} {ws : List Byte} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .wr a ws⟩) {j t : Nat} (hlast : t + 1 ≤ Softmax.trips L)
    (hb : barOrd X g i (warpOf L g + 3) = (Softmax.trips L + 1) * j + 1 + t) :
    ∃ d : Softmax.D, Softmax.Counts L g d ((X.tr g).take i) ∧ Softmax.Inv L g d ∧
      d.i = j ∧ d.t = t ∧
      ((t + 1 < Softmax.trips L ∧ d.site = .alphaSt ∧ ws = (Softmax.alphaV L d).toBytes) ∨
        (t + 1 = Softmax.trips L ∧ d.site = .lSt ∧
          ∃ v, storeValue 32 d.l = .ok v ∧ ws = v.toBytes)) := by
  obtain ⟨d, -, hc, hi, -, -, hs⟩ := soft_wr hpre hX ht hw he
  have hs' : d.site = .alphaSt ∨ d.site = .lSt := hs.imp (·.1) (·.1)
  obtain ⟨-, hb', -⟩ := soft_wr_counts hpre hX ht hw hc hi hs'
  rw [hb'] at hb
  have hdt : d.t + 1 ≤ Softmax.trips L := by
    rcases hs' with h | h
    · exact Nat.le_of_lt (hi.trip (by rw [h]; rfl))
    · exact le_of_eq (hi.last (.inl h))
  obtain ⟨hij, htt⟩ := tile_inj (n := Softmax.trips L + 1) (i := d.i) (i' := j) (T := d.t + 1)
    (T' := t + 1) (by omega) (by omega) (by omega)
  refine ⟨d, hc, hi, hij, by omega, ?_⟩
  rcases hs with ⟨h, hw'⟩ | ⟨h, hw'⟩
  · exact .inl ⟨by have := hi.trip (by rw [h]; rfl); omega, h, hw'⟩
  · exact .inr ⟨by have := hi.last (.inl h); omega, h, hw'⟩

set_option maxHeartbeats 1000000 in
/-- **`SoftValues.alphaStore`.** -/
theorem SoftValues_alphaStore {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) {i pc j t : Nat} {a : Acc} {ws : List Byte}
    (he : X.get (h, i) = some ⟨pc, .wr a ws⟩) (_hs : SoftStore L X h i a true)
    (ht1 : t + 1 < kvBlocks P)
    (hb : barOrd X h i (warpOf L h + 3) = (kvBlocks P + 1) * j + 1 + t) :
    F32Word ws ((2 : ℝ) ^ (softC P S (kvBlocks P * j + t) -
      softC P S (kvBlocks P * j + t + 1))) := by
  have hscE := soft_sc_eq hpre
  have hnE := soft_trips_eq hpre
  rw [← hnE] at ht1 hb ⊢
  obtain ⟨d, hc, hi, rfl, rfl, hcase⟩ := soft_store_gen hpre hX ht hw he (by omega) hb
  rcases hcase with ⟨-, hs, rfl⟩ | ⟨h1, -⟩
  swap
  · omega
  have hF := soft_loadsF32 hpre hX ht hw hS i
  obtain ⟨-, hRl⟩ := hc.refs hF (Softmax.scale_ok hpre)
  have hmx := (hRl (.inl (by rw [hs]; rfl))).1
  have hwf := Softmax.words_f32 hc.words hF (by simp [Softmax.chunks, hs])
  have hm := mR_of hmx
  have hld : Softmax.ldPos d = 4 * (d.t + 1) + 4 := by
    simp [Softmax.ldPos, hs, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip]
  have h4 : 4 * (Softmax.trips L * d.i + d.t + 1) + 4 ≤
      tcLdsIn (Softmax.tmem L h 0) (Softmax.tmem L h 128) ((X.tr h).take i) := by
    rw [hc.tcLd, hld]; ring_nf; omega
  rw [soft_refM_S hpre hX ht hw hS (by omega), hscE] at hm
  have hT : Softmax.tileNo d = d.t + 1 := by simp [Softmax.tileNo, hs, Softmax.Site.tile0]
  have hsc := Softmax.words_scores hc.words hF (by simp [Softmax.chunks, hs])
  rw [hT, ← Nat.add_assoc] at hsc
  have hmod : (Softmax.trips L * d.i + d.t + 1) % Softmax.trips L ≠ 0 := by
    rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  have hmN := soft_mN_refM (n := Softmax.trips L) hscE hm
    (fun k hk => (hsc k hk).trans (soft_tsc_S hpre hX ht hw hS h4 hk)) hmod
  have hα : Softmax.alpha L d = (2 : ℝ) ^ (softC P S (Softmax.trips L * d.i + d.t) -
      softC P S (Softmax.trips L * d.i + d.t + 1)) := by
    rw [(Softmax.alpha_eq L d).1, hmN, hm, hscE, softC, softC, hnE]
  rw [← hα]
  exact f32Word_of (alphaV_f32Val (Softmax.scale_ok hpre) hmx hwf)

/-- **`SoftValues.sumStore`.** -/
theorem SoftValues_sumStore {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) {i pc j : Nat} {a : Acc} {ws : List Byte}
    (he : X.get (h, i) = some ⟨pc, .wr a ws⟩) (_hs : SoftStore L X h i a true)
    (hb : barOrd X h i (warpOf L h + 3) = (kvBlocks P + 1) * j + kvBlocks P) :
    F32Word ws (softL P S (kvBlocks P * j + kvBlocks P - 1)) := by
  have hnE := soft_trips_eq hpre
  have hT := soft_trips_pos hpre
  rw [← hnE] at hb ⊢
  obtain ⟨d, hc, hi, rfl, ht', hcase⟩ := soft_store_gen hpre hX ht hw he (j := j)
    (t := Softmax.trips L - 1)
    (by omega) (by rw [hb]; omega)
  rcases hcase with ⟨h1, -⟩ | ⟨-, hs, v, hv, rfl⟩
  · omega
  have hF := soft_loadsF32 hpre hX ht hw hS i
  obtain ⟨-, hRl⟩ := hc.refs hF (Softmax.scale_ok hpre)
  obtain ⟨-, hl⟩ := hRl (.inr (.inl hs))
  rw [hl, storeValue_of_bytes (by rfl)] at hv
  cases hv
  have hld : Softmax.ldPos d = 4 * (d.t + 1) := by
    simp [Softmax.ldPos, hs, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.inTrip]
  rw [soft_rowL_S hpre hX ht hw hS (by rw [hc.tcLd, hld]; ring_nf; omega), soft_sc_eq hpre]
  rw [show Softmax.trips L * d.i + Softmax.trips L - 1 = Softmax.trips L * d.i + d.t by omega,
    softL, ← hnE]
  exact f32Word_of (f32Val_float _)

/-- **`ValueFacts.soft`**: every softmax thread computes on the scores it loaded. -/
theorem ValueFacts_soft {h : Nat} {S : Nat → Nat → ℝ} (_hh : h < L.threads)
    (hw : warpOf L h < 8) (hS : SoftLoads L X h S) : ∃ c l, SoftValues P L X h S c l :=
  ⟨softC P S, softL P S,
    { pStore := SoftValues_pStore hpre hX ht hw hS
      sumFirst := softValues_sumFirst P S
      refStep := softValues_refStep P S
      sumStep := softValues_sumStep P S
      alphaStore := fun he hs ht1 hb => SoftValues_alphaStore hpre hX ht hw hS he hs ht1 hb
      sumStore := fun he hs hb => SoftValues_sumStore hpre hX ht hw hS he hs hb }⟩

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
