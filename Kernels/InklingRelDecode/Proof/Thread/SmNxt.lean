-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmPackBase
public import Kernels.InklingRelDecode.Proof.Thread.MmaBits

@[expose] public section

/-! # The loop's bias loads of the softmax region (pcs 1124-1256)

The 64 loads of the next block's bias (`nxt j`, pc `1124 + 2 j`) have the shape of the preloads
(`SmLoads`): guarded `ld.global.b16` instructions that alternate with `mov.u16 %rs, %rs152`, the
zero fill of the next destination. This file gives the register table at the loop's words
(`valueOf_nxt`, `valueOf_frameV`), the guard of every load (`site_ok_nxt`), the step of a load
(`step_nxt`: the event, the zero fill of the next destination, the arrival at the next load, or
after the last load the six local instructions to the `s_ready` poll at pc 1257) and the skip of
all 64 loads where the mask `%p92` is false (`seg_skipNxt`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event}

/-! ### The table at the loop's words -/

/-- The lookup in the bias-word section of a register outside the loop's words does not depend on
them. -/
theorem lookup_valuesWf_off (wd vd vd' : Nat → Value) {r : Nat} (hr : ¬ (332 ≤ r ∧ r < 397)) :
    (valuesWf wd vd').lookup r = (valuesWf wd vd).lookup r := by
  have e1 : (r == 332) = false := by simp; omega
  have e2 : (r == 333) = false := by simp; omega
  have h3 : ¬ (334 ≤ r ∧ r < 334 + 63) := by omega
  simp only [valuesWf, lookup_append', List.lookup, e1, e2, lookup_range_map, h3, ↓reduceIte]

/-- Two states that agree on everything but the loop's words give a register outside them the same
value. -/
theorem valueOf_frameV {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hw : d'.wd = d.wd) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf) {r : Nat}
    (hr : ¬ (332 ≤ r ∧ r < 397)) (hx : d'.stg = d.stg := by rfl) :
    valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hx]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eW : (valuesW d').lookup r = (valuesW d).lookup r := by
    simp only [valuesW, hw]
    exact lookup_valuesWf_off _ _ _ hr
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, eX]

/-- Two states with the same words give every register the same value. -/
theorem valueOf_congr {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) (h5 : d'.sv = d.sv)
    (h6 : d'.pf = d.pf) (hx : d'.stg = d.stg) (r : Nat) :
    valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hx]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  simp only [valueOf, values, eI, eS, eP, eQ, eR, eW, eX]

/-- The loop's words: `%rs151`, then `%rs153 …` after the zero constant `%rs152`. -/
theorem valueOf_nxt (d : D) {k : Nat} (hk : k < 64) : valueOf L g d (nxtDst k) = d.vd k := by
  obtain ⟨hS, hP, hQ, hR⟩ := keys_off_words (L := L) (g := g) d (r := nxtDst k)
    (Or.inr (Or.inl ⟨by unfold nxtDst; split <;> omega, by unfold nxtDst; split <;> omega⟩))
  have hX := keys_off_X (L := L) (g := g) d (r := nxtDst k)
    (Or.inr (Or.inl ⟨by unfold nxtDst; split <;> omega, by unfold nxtDst; split <;> omega⟩))
  have hI := notI (L := L) (g := g) d (r := nxtDst k) (by unfold IKey nxtDst; split <;> omega)
  simp only [valueOf, values, lookup_append', lookup_none_of_not_mem _ hI,
    lookup_none_of_not_mem _ hS,
    lookup_none_of_not_mem _ hP, lookup_none_of_not_mem _ hQ, lookup_none_of_not_mem _ hR,
    lookup_none_of_not_mem _ hX, Option.none_or, Option.or_none, valuesW, valuesWf,
    lookup_range_map]
  by_cases h0 : k = 0
  · subst h0
    simp [nxtDst, List.lookup]
  · have e1 : (nxtDst k == 332) = false := by simp [nxtDst, h0]; omega
    have e2 : (nxtDst k == 333) = false := by simp [nxtDst, h0]
    have h1 : ¬ (263 ≤ nxtDst k ∧ nxtDst k < 263 + 64) := by simp [nxtDst, h0]; omega
    have h2 : 334 ≤ nxtDst k ∧ nxtDst k < 334 + 63 := by simp [nxtDst, h0]; omega
    have h3 : nxtDst k - 334 + 1 = k := by simp [nxtDst, h0]; omega
    simp [h1, h2, List.lookup, e1, e2, lookup_range_map, h3]

/-- The zero constant `%rs152`. -/
theorem valueOf_z152 (d : D) : valueOf L g d 333 = z16 := by sm_vals

/-- The words after load `j` returned `x`. -/
def D.afterNxt (d : D) (j : Nat) (x : Value) : D :=
  { d with cv := j + 1, v := setW d.v j x }

/-- The loop's word `k` of a state after load `j`, where `j` words were loaded. -/
theorem vd_afterNxt {d : D} {j k : Nat} (hcv : d.cv = j) (x : Value) (hk : k ≠ j) :
    (d.afterNxt j x).vd k = d.vd k := by
  by_cases h : k < j
  · simp [D.afterNxt, D.vd, setW, hcv, h, Function.update_of_ne hk, show k < j + 1 by omega]
  · simp [D.afterNxt, D.vd, hcv, h, show ¬ k < j + 1 by omega]

/-! ### The code of the loop's loads, decided -/

theorem movAt_nxt : ∀ j < 63, movAt (1125 + 2 * j) (334 + j) 333 = true := by decide +kernel
theorem emu_nxt : ∀ j < 64, Assumptions.emuSites.contains (1125 + 2 * j) = false := by
  decide +kernel
theorem live_movN : ∀ j < 63, 333 ∈ Flow.live (1125 + 2 * j) ∧
    ∀ r ∈ Flow.live (1125 + 2 * j + 1), r = 334 + j ∨ r ∈ Flow.live (1125 + 2 * j) := by
  decide +kernel
theorem live_afterN : ∀ j < 63, ∀ r ∈ Flow.live (1124 + 2 * (j + 1)),
    r ∈ Flow.live (1125 + 2 * j + 1) := by decide +kernel
theorem live_loadN : ∀ j < 64, ∀ r ∈ Flow.live (1125 + 2 * j),
    r = nxtDst j ∨ r ∈ Flow.live (1124 + 2 * j) := by decide +kernel

/-! ### The guards -/

/-- The loop mask's register reads as the state's `actB`. -/
theorem valueOf_p92 (d : D) : valueOf L g d 92 = .pred (actB d.e (g % L.block) d.i) := by
  sm_vals

/-- **Every loop load's guard holds**: the instruction is a load guarded by `%p92`, whose fact is
the state's mask, true by the invariant. -/
theorem site_ok_nxt (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j) :
    ∃ ins, kernel.code[d.site.pc]? = some ins ∧ ins.op.isLocal = false ∧
      Code.GuardTrue (facts L g d) ins.guard := by
  obtain ⟨a, hc, -, -, -, -, hl⟩ := loadAt_spec (loadAt_nxt j.val j.isLt)
  have hpc : d.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  refine ⟨_, by rw [hpc]; exact hc, hl, ?_⟩
  show (92, Value.pred (!false)) ∈ factsAt L g d.site.pc d
  have hact := (hi.cwNxt j hs).2.2.1
  have := Flow.mem_factsFrom (val := valueOf L g d) (live_nxt j.val j.isLt)
  rw [valueOf_p92, hact] at this
  rw [hpc]
  exact this

/-! ### The facts after a load and the invariant -/

/-- The facts at the zero fill after load `j` (pc `1125 + 2 j`): the loaded word is in its
destination, every other register is as before. -/
theorem holds_afterNxt {R : Nat → Option Value} (hi : Inv L g d) {j : Fin 64}
    (hs : d.site = .nxt j) {x : Value}
    (hR : ∀ r ∈ Flow.live (1124 + 2 * j.val), r ≠ nxtDst j.val →
      R r = some (valueOf L g d r))
    (hx : R (nxtDst j.val) = some x) :
    Holds R (factsAt L g (1125 + 2 * j.val) (d.afterNxt j.val x)) := by
  obtain ⟨hcw, hcv, -, -⟩ := hi.cwNxt j hs
  refine Flow.holds_of_pointwise fun r hr => ?_
  by_cases hrj : r = nxtDst j.val
  · subst hrj
    rw [valueOf_nxt _ j.isLt]
    simpa [D.afterNxt, D.vd, setW] using hx
  rcases live_loadN j.val j.isLt r hr with h | hl
  · exact absurd h hrj
  have hR' := hR r hl hrj
  by_cases hw : 332 ≤ r ∧ r < 397
  · by_cases h334 : r = 333
    · subst h334
      rw [valueOf_z152] at hR' ⊢
      exact hR'
    · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 64 ∧ r = nxtDst k := by
        by_cases h333 : r = 332
        · exact ⟨0, by omega, by simp [nxtDst, h333]⟩
        · exact ⟨r - 333, by omega, by unfold nxtDst; split <;> omega⟩
      have hkj : k ≠ j.val := fun h => hrj (by rw [h])
      rw [valueOf_nxt _ hk] at hR' ⊢
      rw [vd_afterNxt hcv x hkj]
      exact hR'
  · have := valueOf_frameV (L := L) (g := g) (d := d) (d' := d.afterNxt j.val x) rfl rfl rfl rfl
      rfl rfl rfl hw (r := r)
    rw [this]
    exact hR'

/-- The invariant after load `j` (`j + 1 < 64`) returned a word. -/
theorem inv_afterNxt (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j) (hj : j.val + 1 < 64)
    (x : Value) (hx : x.bytes = 2) (hxf : BfOk x) :
    Inv L g { d with site := .nxt ⟨j.val + 1, hj⟩, cv := j.val + 1, v := setW d.v j.val x } := by
  obtain ⟨hcw, hcv, hact, hlt⟩ := hi.cwNxt j hs
  refine ⟨hi.tid, hi.ok, hi.i, fun k hk => absurd hk (by simp), ?_, ?_, hi.wb, ?_,
    fun h => absurd h (by simp), fun h => absurd h (by simp [LateSite]),
    fun h => absurd h (by simp), hi.re, hi.lb, hi.four, hi.bw, hi.wf, bfOk_setW hi.vf hxf⟩
  · intro k hk
    have : (⟨j.val + 1, hj⟩ : Fin 64) = k := by injection hk
    subst this
    exact ⟨hcw, rfl, hact, hlt⟩
  · exact ⟨fun k hk => absurd hk (by simp), fun hk => absurd hk (by simp)⟩
  · intro k
    by_cases hk : k = j.val
    · subst hk; simpa [setW] using hx
    · simpa [setW, Function.update_of_ne hk] using hi.vb k

/-- The invariant after the last load returned a word: the machine is at the `s_ready` poll. -/
theorem inv_afterNxtLast (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j)
    (x : Value) (hx : x.bytes = 2) (hxf : BfOk x) :
    Inv L g { d with site := .waitS, cv := 64, v := setW d.v j.val x } := by
  obtain ⟨hcw, hcv, hact, hlt⟩ := hi.cwNxt j hs
  refine ⟨hi.tid, hi.ok, hi.i, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp),
    ⟨fun k hk => absurd hk (by simp), fun hk => absurd hk (by simp)⟩, hi.wb, ?_,
    fun h => absurd h (by simp), fun _ => ⟨hcw, rfl, hlt⟩, fun h => absurd h (by simp),
    hi.re, hi.lb, hi.four, hi.bw, hi.wf, bfOk_setW hi.vf hxf⟩
  intro k
  by_cases hk : k = j.val
  · subst hk; simpa [setW] using hx
  · simpa [setW, Function.update_of_ne hk] using hi.vb k

/-! ### The zero fill and the end of the loads -/

/-- `mov.u16 %rs(335 + j), %rs152` (pc `1125 + 2 j`) where the destination holds the zero
half-word already. -/
theorem seg_fillN (d : D) {j : Nat} (hj : j < 63) (hz : d.vd (j + 1) = z16) :
    Seg kernel asms L g 1 (1125 + 2 * j) (factsAt L g (1125 + 2 * j) d) (1125 + 2 * j + 1)
      (factsAt L g (1125 + 2 * j + 1) d) := by
  obtain ⟨hl0, hl1⟩ := live_movN j hj
  refine seg_one (r := 334 + j) (v := z16) (movAt_spec (movAt_nxt j hj)) rfl ?_ ?_ hl1
  · intro t h
    have h0 := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) hl0)
    rw [valueOf_z152] at h0
    exact exec_mov16 (segFree (by rw [h.1]; exact emu_nxt j (by omega))) h0
  · have := valueOf_nxt (L := L) (g := g) d (k := j + 1) (by omega)
    rw [show nxtDst (j + 1) = 334 + j by simp [nxtDst]; omega] at this
    rw [this, hz]

/-- The six local instructions after the last load to the `s_ready` poll (pcs 1251 to 1256): the
parity and the poll's address. -/
theorem seg_toWaitS (d : D) (hT : g % L.block < 128) (hok : d.e.Ok) (hi : d.i ≤ d.e.r26) :
    Seg kernel asms L g 6 1251 (factsAt L g 1251 d) 1257 (factsAt L g 1257 d) := by
  have := hok.r26_lt
  intro t h
  sm_seg h [Mma.bfe_u32]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
