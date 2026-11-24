-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStoreF32
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftLow
public import Kernels.FlashAttn4Fwd.Proof.Interface.Values

@[expose] public section

/-! # The softmax values: the recurrence and the loaded scores

The reference exponent and row sum of tile `u` for the scores `S` are the recurrence of the code
(`Softmax.refM`, `Softmax.rowL` with the scale `P.scale` and `n = kvBlocks P` tiles per item):
`softC P S u = P.scale · refM … u`, `softL P S u = rowL … u`. Their relations (`sumFirst`,
`refStep`, `sumStep`) hold by the recurrence. The scale register reads as `P.scale`
(`soft_sc_eq`). Under `SoftLoads S`, every load of the thread returned single-precision numbers
(`soft_loadsF32`), and the scores of the trace prefix (`Softmax.tsc`) are `S` on every loaded
tile (`soft_tsc_S`), hence so are the recurrence's values (`soft_refM_S`, `soft_rowL_S`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The reference exponent of tile `u`. -/
def softC (P : Params) (S : Nat → Nat → ℝ) (u : Nat) : ℝ :=
  P.scale * Softmax.refM P.scale (kvBlocks P) S u

/-- The row sum after tile `u`. -/
def softL (P : Params) (S : Nat → Nat → ℝ) (u : Nat) : ℝ :=
  Softmax.rowL P.scale (kvBlocks P) S u

theorem softValues_sumFirst (P : Params) (S : Nat → Nat → ℝ) (u : Nat)
    (h : u % kvBlocks P = 0) :
    softL P S u = ∑ k ∈ Finset.range 128, (2 : ℝ) ^ (P.scale * S u k - softC P S u) := by
  rw [softL, Softmax.rowL_first h]
  rfl

theorem softValues_refStep (P : Params) (S : Nat → Nat → ℝ) (u : Nat)
    (h : u % kvBlocks P ≠ 0) : softC P S (u - 1) ≤ softC P S u := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by cases u <;> simp_all⟩
  exact Softmax.refM_mono h

theorem softValues_sumStep (P : Params) (S : Nat → Nat → ℝ) (u : Nat)
    (h : u % kvBlocks P ≠ 0) :
    softL P S u = softL P S (u - 1) * 2 ^ (softC P S (u - 1) - softC P S u) +
      ∑ k ∈ Finset.range 128, (2 : ℝ) ^ (P.scale * S u k - softC P S u) := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by cases u <;> simp_all⟩
  rw [softL, Softmax.rowL_loop h]
  rfl

/-- The scale register reads as the scale. -/
theorem soft_sc_eq (hpre : Pre P L mem0) : Softmax.sc L = P.scale := by
  obtain ⟨bits, hb, hp, hv⟩ := hpre.paramScale
  cases hq : f32Value bits with
  | none => simp [hq] at hv
  | some q =>
    simp only [hq, Option.map_some, Option.some.injEq] at hv
    have hs : Softmax.scaleV L = b32 bits := by
      simp only [Softmax.scaleV, hp, Option.getD_some, truncBits, BitVec.toNat_ofNat, b32]
      congr 2
      omega
    have h1 := Softmax.scale_ok hpre
    rw [hs, valFloat_b32 (by omega) hq] at h1
    injection h1 with h1
    rw [← h1, hv]

/-- The reference after a loop tile from the previous reference and the tile's scores. -/
theorem soft_mN_refM {L : Launch} {d : Softmax.D} {sc : ℝ} {n v : Nat} {S : Nat → Nat → ℝ}
    (hsc : Softmax.sc L = sc) (hm : d.mR = Softmax.refM sc n S v)
    (hs : ∀ j < 128, d.s j = S (v + 1) j) (hmod : (v + 1) % n ≠ 0) :
    Softmax.mN L d = Softmax.refM sc n S (v + 1) := by
  rw [Softmax.refM_loop hmod, ← hm, Softmax.mNr_congr (fun k hk => (hs k hk).symm)]
  unfold Softmax.mN Softmax.gap Softmax.mNr
  rw [hsc]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Under `SoftLoads`, every load of the thread returned 32 single-precision numbers.** -/
theorem soft_loadsF32 {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) (i : Nat) : Softmax.LoadsF32 ((X.tr h).take i) := by
  intro x hx pc a vals hxe
  subst hxe
  obtain ⟨j, -, hget⟩ := get_of_mem_take hx
  have hl := (soft_tld hpre hX ht hw hget).choose_spec.choose_spec.choose_spec.2.2.2.2.2
  refine ⟨hl, fun v hv => ?_⟩
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv
  have hpos := (ScoreFacts_soft_ld hpre hX ht (Frame.lt_of_get hX hget) hw ⟨pc, hget⟩).2.2
  have := hS ⟨pc, hget⟩ (u := sPolls L X h (warpOf L h / 4) j - 1) (by omega) hp
  rw [List.getElem?_eq_getElem hp] at this
  exact ⟨_, Option.some.inj this⟩

/-- **Under `SoftLoads`, the scores of a loaded tile of the trace prefix are `S`.** -/
theorem soft_tsc_S {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) {i u k : Nat}
    (h4 : 4 * u + 4 ≤ tcLdsIn (Softmax.tmem L h 0) (Softmax.tmem L h 128) ((X.tr h).take i))
    (hk : k < 128) : Softmax.tsc L h ((X.tr h).take i) u k = S u k := by
  have ho : 4 * u + k / 32 <
      ((X.tr h).take i).countP (tcLdAt (Softmax.tmem L h 0) (Softmax.tmem L h 128)) := by
    unfold tcLdsIn at h4; omega
  obtain ⟨b, hb, x, hxb, hpx, hcb⟩ := nth_countP ho
  obtain ⟨xpc, a, vals, sh, rfl⟩ : ∃ pc a vals sh, x = ⟨pc, .tc (.ld a vals sh)⟩ := by
    obtain ⟨pc, kd⟩ := x
    cases kd <;> simp [tcLdAt] at hpx
    rename_i tk
    cases tk <;> simp_all
  obtain rfl := tc_shape_of_get hpre hX ht hxb (.inl rfl)
  have hget : X.get (h, b) = some ⟨xpc, .tc (.ld a vals .s32x32b)⟩ := hxb
  obtain ⟨d, lp, c, -, hc, hi, hs, ha, hl⟩ := soft_tld hpre hX ht hw hget
  obtain ⟨h1, h2, -, -⟩ := soft_tile hpre hi (.inl ⟨lp, c, hs⟩)
  have q := hc.tcLd
  unfold tcLdsIn at q
  rw [hcb, Softmax.ldPos_ld hs] at q
  have e4 : 4 * Softmax.trips L * d.i = 4 * (Softmax.trips L * d.i) := by ring
  have hu : u = Softmax.trips L * d.i + Softmax.tileNo d := by omega
  have hcc : c.val = k / 32 := by omega
  -- the load's S-full polls and columns
  have hsp : sPolls L X h (warpOf L h / 4) b = u + 1 := by
    unfold sPolls; rw [soft_sFullBar, hc.score, h1]; omega
  have hS' := hS ⟨xpc, hget⟩ hsp (p := k % 32) (by rw [hl]; omega)
  have hcol : (tcDataCell32 L h a (k % 32)).column - 128 * (warpOf L h / 4) = k := by
    rw [ha, soft_column L h h _ _ hw (by omega)]
    have : Softmax.stOf L h = warpOf L h / 4 := rfl
    omega
  rw [hcol] at hS'
  -- the load is the one of the trace prefix's ordinal
  have hlv : Softmax.loadValsAt L h ((X.tr h).take i) (4 * u + k / 32) = vals := by
    have hxi : ((X.tr h).take i)[b]? = some ⟨xpc, .tc (.ld a vals .s32x32b)⟩ := by
      rw [List.getElem?_take_of_lt hb]; exact hxb
    have hf := filter_getElem_countP (p := tcLdAt (Softmax.tmem L h 0) (Softmax.tmem L h 128))
      hxi hpx
    rw [List.take_take, Nat.min_eq_left (by omega), hcb] at hf
    unfold Softmax.loadValsAt
    rw [hf]
  unfold Softmax.tsc
  rw [hlv, List.getD_eq_getElem?_getD, hS', Option.getD_some]
  simp [rd32, valFloat, pure, Except.pure, Except.toOption]

theorem soft_refM_S {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) {i u : Nat}
    (h4 : 4 * u + 4 ≤ tcLdsIn (Softmax.tmem L h 0) (Softmax.tmem L h 128) ((X.tr h).take i))
    (sc : ℝ) (n : Nat) :
    Softmax.refM sc n (Softmax.tsc L h ((X.tr h).take i)) u = Softmax.refM sc n S u :=
  Softmax.refM_congr fun _ hu' _ hk => soft_tsc_S hpre hX ht hw hS (by omega) hk

theorem soft_rowL_S {h : Nat} {S : Nat → Nat → ℝ} (hw : warpOf L h < 8)
    (hS : SoftLoads L X h S) {i u : Nat}
    (h4 : 4 * u + 4 ≤ tcLdsIn (Softmax.tmem L h 0) (Softmax.tmem L h 128) ((X.tr h).take i))
    (sc : ℝ) (n : Nat) :
    Softmax.rowL sc n (Softmax.tsc L h ((X.tr h).take i)) u = Softmax.rowL sc n S u :=
  Softmax.rowL_congr fun _ hu' _ hk => soft_tsc_S hpre hX ht hw hS (by omega) hk

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
