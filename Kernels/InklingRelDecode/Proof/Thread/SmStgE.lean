-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgD

@[expose] public section

/-! # The O rescale after the test (pcs 2260 to 2329)

When the minimum of the alphas is below 1 (the branch of pc 2258 is not taken), the thread loads
its 64 words of `O` from Tensor Memory (`ldO`, pc 2260), waits for the load (`waitLdO`, pc 2261),
multiplies each word by `alpha` (`mul.f32 %r(1151 + k), %r46, %r(1086 + k)`, pcs 2262 to 2325),
synchronizes the warpgroup (`bar24`, pc 2326), sets the guard `%p171` (pc 2327), stores the products
(`stO`, pc 2328) and waits for the store (`waitStO`, pc 2329, in `SmEdge`).

The 64 words and the products are in the table's last section (`valuesXs`): the words
`%r1086 …` are `Stg.ow`, as the load returned them, and the products are the outcomes of the
multiplications (`prodO`: `mulE` of `alpha` and the word). The machine follows every loaded word:
where a product faults (`D.owOk` fails) the thread is dead and `next waitLdO` is `none`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### The table's entries for the rescale -/

theorem valueOf_p171 (d : D) : valueOf L g d 171 = .pred true := by
  sm_vals

/-- The registers of the words of `O` and of the products are looked up in the last section. -/
theorem lookup_valuesX_Xs (d : D) {r : Nat}
    (h : (1415 ≤ r ∧ r < 1499) ∨ (1547 ≤ r ∧ r < 1611) ∨ (1612 ≤ r ∧ r < 1676)) :
    (valuesX L g d).lookup r = (valuesXs d.stg.fsv d.stg.ow d.stg.al).lookup r := by
  have hxt : (valuesXt d).lookup r = none := by
    refine lookup_none_of_not_mem _ (fun hm => ?_)
    simp only [valuesXt, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    omega
  have b : ∀ k, k ∈ [172, 506, 168, 507, 1522, 1531, 1544, 1520, 1529, 1536, 1538, 1540, 1534,
      1542] → (r == k) = false := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp <;> omega
  simp only [valuesX, lookup_append', List.lookup, hxt]
  rw [b 172 (by simp), b 506 (by simp), b 168 (by simp), b 507 (by simp), b 1522 (by simp),
    b 1531 (by simp), b 1544 (by simp), b 1520 (by simp), b 1529 (by simp), b 1536 (by simp),
    b 1538 (by simp), b 1540 (by simp), b 1534 (by simp), b 1542 (by simp)]
  rfl

theorem lookup_col_none (fsv : Nat → { v : Value // v.bytes = 4 }) {r : Nat}
    (h : ¬ (1415 ≤ r ∧ r < 1499)) :
    ((List.range 64).map (fun k => (colReg k, (fsv k).1))).lookup r = none := by
  refine lookup_none_of_not_mem _ (fun hm => ?_)
  simp only [List.map_map, List.mem_map, List.mem_range, Function.comp_apply] at hm
  obtain ⟨j, hj, hjr⟩ := hm
  have := colReg_range j hj
  omega

theorem lookup_Xs_off (fsv : Nat → { v : Value // v.bytes = 4 }) (ow : Nat → Value) (al : Value)
    {r : Nat} (h1 : ¬ (1547 ≤ r ∧ r < 1611)) (h2 : ¬ (1612 ≤ r ∧ r < 1676)) :
    (valuesXs fsv ow al).lookup r =
      ((List.range 64).map (fun k => (colReg k, (fsv k).1))).lookup r := by
  unfold valuesXs
  rw [lookup_append', lookup_append', lookup_range_map, lookup_range_map, if_neg (by omega),
    if_neg (by omega)]
  simp

theorem lookup_Xs_ow (fsv : Nat → { v : Value // v.bytes = 4 }) (ow : Nat → Value) (al : Value)
    {k : Nat} (hk : k < 64) : (valuesXs fsv ow al).lookup (1547 + k) = some (ow k) := by
  unfold valuesXs
  rw [lookup_append', lookup_col_none fsv (by omega), lookup_append', lookup_range_map,
    if_pos (by omega)]
  simp

theorem lookup_Xs_prod (fsv : Nat → { v : Value // v.bytes = 4 }) (ow : Nat → Value)
    (al : Value) {k : Nat} (hk : k < 64) :
    (valuesXs fsv ow al).lookup (1612 + k) = some (prodO al (ow k)) := by
  unfold valuesXs
  rw [lookup_append', lookup_col_none fsv (by omega), lookup_append', lookup_range_map,
    lookup_range_map, if_neg (by omega), if_pos (by omega)]
  simp

theorem valueOf_al (d : D) : valueOf L g d 507 = d.stg.al := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_ow (d : D) {k : Nat} (hk : k < 64) :
    valueOf L g d (1547 + k) = d.stg.ow k := by
  rw [valueOf_X d (by unfold XKey; omega), lookup_valuesX_Xs d (by omega), lookup_Xs_ow _ _ _ hk]
  rfl

theorem valueOf_prod (d : D) {k : Nat} (hk : k < 64) :
    valueOf L g d (1612 + k) = prodO d.stg.al (d.stg.ow k) := by
  rw [valueOf_X d (by unfold XKey; omega), lookup_valuesX_Xs d (by omega),
    lookup_Xs_prod _ _ _ hk]
  rfl

/-- **The product of a number by `alpha`**: where `alpha` reads as the real `alr` and the word is
the `f32` number `y`, the product is the `f32` number `alr · y`. -/
theorem mulE_alpha {al : Value} {alr y : ℝ} (hal : readEReal .f32 al = some (.ok (alr : EReal))) :
    mulE false al (.float .f32 y) = .ok (.float .f32 (alr * y)) := by
  have hy : readEReal .f32 (.float .f32 y) = some (.ok (y : EReal)) :=
    readEReal_of_valFloat (valFloat_float y)
  simp only [mulE, idealMul, hal, hy, bindRead, mulEReal_coe, Option.map_some,
    erealValue_coe, pure, Except.pure]

theorem prodO_float {al : Value} {alr y : ℝ} (hal : readEReal .f32 al = some (.ok (alr : EReal))) :
    prodO al (.float .f32 y) = .float .f32 (alr * y) := by
  rw [prodO, mulE_alpha hal]
  rfl

/-- A register that is neither a word of `O` nor a product has the same value in two states that
differ in the words of `O` (and the site). -/
theorem frame_ow (d : D) (s : Site) (ow : Nat → Value) {r : Nat}
    (h1 : ¬ (1547 ≤ r ∧ r < 1611)) (h2 : ¬ (1612 ≤ r ∧ r < 1676)) :
    valueOf L g { d with site := s, stg := { d.stg with ow := ow } } r = valueOf L g d r := by
  have hX : (valuesX L g { d with site := s, stg := { d.stg with ow := ow } }).lookup r =
      (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, lookup_append',
      lookup_Xs_off _ _ _ h1 h2]
  exact valueOf_congrX (d := d) (d' := { d with site := s, stg := { d.stg with ow := ow } })
    rfl rfl rfl rfl rfl rfl hX


/-! ### The load of `O` (pc 2260) -/

/-- The 64 destination registers of the load of `O`. -/
def ldORegs : List Nat := (List.range 64).map (1547 + ·)

theorem ldORegs_nodup : ldORegs.Nodup := by decide
theorem ldORegs_length : ldORegs.length = 64 := by decide

theorem code_ldO : kernel.code[2260]? = some ⟨none, .tcLd ldORegs 1611 (.s16x32bx2 64) none⟩ := by
  rw [Flow.code_2260]
  rfl

theorem live_ldO_cov : ∀ r ∈ Flow.live 2261, r ∈ ldORegs ∨ (r ∉ ldORegs ∧ r ∈ Flow.live 2260) := by
  decide +kernel
theorem live_ldO_off : ∀ r ∈ Flow.live 2260, r ∉ ldORegs ∧ ¬ (1547 ≤ r ∧ r < 1611) ∧
    ¬ (1612 ≤ r ∧ r < 1676) := by decide +kernel

/-- The facts after the load: the destinations hold the words, the other registers keep their
values. -/
theorem holds_ldO (d : D) (vals : List Value) (hlen : vals.length = 64) (t : TState)
    (hh : Holds t.regs (factsAt L g 2260 d)) :
    Holds (setRegs t ldORegs vals).regs
      (factsAt L g 2261 { d with site := .waitLdO, stg := { d.stg with ow := owOf vals } }) := by
  have hw := holds_setRegs t ldORegs vals
    (valueOf L g { d with site := .waitLdO, stg := { d.stg with ow := owOf vals } })
    ldORegs_nodup (by rw [hlen, ldORegs_length]) (fun p hp => by
      have hp' : p < 64 := by simpa [ldORegs_length] using hp
      have : ldORegs.getD p 0 = 1547 + p := by
        simp [ldORegs, List.getD_eq_getElem?_getD, hp']
      rw [this, valueOf_ow _ hp']
      rfl)
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases live_ldO_cov r hr with hd | ⟨hd, hl⟩
  · exact holds_mem hw (Flow.mem_factsFrom hd)
  · obtain ⟨-, hr1, hr2⟩ := live_ldO_off r hl
    rw [setRegs_other t ldORegs vals r hd, frame_ow d .waitLdO (owOf vals) hr1 hr2]
    exact holds_mem hh (Flow.mem_factsFrom hl)

/-- **The Tensor Memory load of `O`** (pc 2260): the event returns the 64 words, which the machine
records whatever they are. -/
theorem step_ldO {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .ldO) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2260 := by rw [hs]; rfl
  have hc' : kernel.code[2260]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans code_ldO)
  obtain ⟨a, vals, hl, rfl, hu⟩ := fires_tcLd (L := L) (g := g) (A := asms)
    (by intro s hs; cases hs) hf (by hooks_off)
  have hlen : vals.length = 64 := by rw [hl, ldORegs_length]
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h' : At t 2260 (factsAt L g 2260 d) := hpc ▸ h
  obtain ⟨hpc', hsub, hacc, hfl⟩ := setRegs_skel (PTX.next t) ldORegs vals
  have hAt : At u 2261 (factsAt L g 2261
      { d with site := .waitLdO, stg := { d.stg with ow := owOf vals } }) := by
    rw [hu]
    refine ⟨by rw [hpc']; simp [PTX.next, h'.1], by rw [hsub]; exact h'.2.1,
      by rw [hacc]; exact h'.2.2.1, by rw [hfl]; exact h'.2.2.2.1, ?_⟩
    rw [setRegs_next_regs]
    exact holds_ldO d vals hlen t h'.2.2.2.2
  exact .inl (.inr ⟨{ d with site := .waitLdO, stg := { d.stg with ow := owOf vals } }, u,
    by simp only [next, hs], .refl, hAt,
    inv_stg (inv_late hi hlate (s := .waitLdO) trivial (fun h => absurd h (by simp))) _ _
        (by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩)⟩)

/-! ### The wait for the load and the 64 products (pcs 2261 to 2325) -/

/-- The instruction at `pc` is `mul.f32 d, a, b`. -/
def mulAt (pc d a b : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ =>
    f == { op := .mul, ty := ty1 .f32, dsts := [some d], srcs := [.reg a, .reg b] }
  | _ => false

theorem mulAt_spec {pc d a b : Nat} (h : mulAt pc d a b = true) :
    kernel.code[pc]? = some ⟨none, mulOp d a b⟩ := by
  unfold mulAt at h
  split at h
  · rename_i f hc
    rw [hc, mulOp, beq_iff_eq.mp h]
  · cases h

theorem mulK_code : ∀ k < 64, mulAt (2262 + k) (1612 + k) 507 (1547 + k) = true := by
  decide +kernel
theorem emu_mulK : ∀ k < 64, Assumptions.emuSites.contains (2262 + k) = false := by
  decide +kernel
theorem live_mulK : ∀ k < 64, 507 ∈ Flow.live (2262 + k) ∧ (1547 + k) ∈ Flow.live (2262 + k) ∧
    ∀ r ∈ Flow.live (2262 + k + 1), r = 1612 + k ∨ r ∈ Flow.live (2262 + k) := by
  decide +kernel

/-- `mul.f32 %r(1151 + k), %r46, %r(1086 + k)` (pc `2262 + k`) between the table's facts: the
thread continues where the product has an outcome and is dead where it faults. -/
theorem seg_mul1 (d : D) {k : Nat} (hk : k < 64) :
    SegD kernel asms L g 1 (2262 + k) (factsAt L g (2262 + k) d) (2262 + k + 1)
      (factsAt L g (2262 + k + 1) d) ((mulE false d.stg.al (d.stg.ow k)).toBool = true) := by
  obtain ⟨la, lb, lc⟩ := live_mulK k hk
  refine SegD.one (d := 1612 + k) (mulAt_spec (mulK_code k hk)) rfl (fun t h => ?_) ?_ ?_
  · have ha := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) la)
    have hb := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d) lb)
    rw [valueOf_al] at ha
    rw [valueOf_ow d hk] at hb
    have hE : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; exact emu_mulK k hk
    have hp : t.pc = 2262 + k := h.1
    exact PTX.Flow.exec_mulE (idealAtSc (by decide) hE)
      (declineAtSc (f := .mul .f32) (by decide) hE (by omega) (by omega) (by omega))
      (OpndIs.reg ha) (OpndIs.reg hb)
  · intro x hx _
    rw [valueOf_prod d hk, prodO, hx]
    rfl
  · intro r hr
    by_cases hd : r = 1612 + k
    · exact .inl hd
    · exact .inr ⟨hd, (lc r hr).resolve_left hd⟩

/-- **The 64 products** (pcs 2262 to 2325): the first `m` of them have outcomes, or the thread is
dead. -/
theorem seg_muls (d : D) : ∀ m, m ≤ 64 →
    SegD kernel asms L g m 2262 (factsAt L g 2262 d) (2262 + m) (factsAt L g (2262 + m) d)
      (∀ j < m, (mulE false d.stg.al (d.stg.ow j)).toBool = true) := by
  intro m
  induction m with
  | zero => exact fun _ => (SegD.of_seg (Seg.refl _ _)).iff ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    intro hm
    refine ((ih (by omega)).comp (seg_mul1 d (k := m) (by omega))).iff ⟨fun h j hj => ?_,
      fun h => ⟨fun j hj => h j (by omega), h m (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact h.1 j hj
    · exact h.2

theorem live_2262_2261 : ∀ r ∈ Flow.live 2262, r ∈ Flow.live 2261 := by decide +kernel

/-- **The wait for the load of `O`** (pc 2261): the thread runs the 64 products to the barrier of
the store (pc 2326), or is dead where a product faults (`D.owOk`). -/
theorem step_waitLdO (hb : L.block % 32 = 0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hi : Inv L g d) (hs : d.site = .waitLdO) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2261 := by rw [hs]; rfl
  have hc' : kernel.code[2261]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemWait_2)
  have hlate : LateSite d.site := by rw [hs]; trivial
  have hS := seg_muls (L := L) (g := g) d 64 (le_refl 64)
  by_cases hck : d.owOk
  · refine step_seg (dn := { d with site := .bar24 }) (n := 64)
      (fun hf' => (fires_waitLd_next hb (hpc ▸ hf')).1)
      (by simp only [next, hs]; rw [if_pos hck])
      (by rw [hpc]; exact live_2262_2261) ?_
      (inv_late hi hlate (s := .bar24) trivial (fun h => absurd h (by simp))) h hf
    rw [hpc]
    exact hS.seg hck
  · refine .inr ⟨by simp only [next, hs]; rw [if_neg hck], ?_⟩
    obtain rfl := (fires_waitLd_next hb (hpc ▸ hf)).1
    have h1 : At (PTX.next t) 2262 (factsAt L g 2262 d) :=
      at_next_live (hpc ▸ h) rfl rfl live_2262_2261
    exact (hS _ h1).2 hck

/-! ### The barrier before the store and the guard (pcs 2326 and 2327) -/

/-- `mov.pred %p171, -1` (pc 2327): the guard of the store. -/
theorem seg_2327 (d : D) :
    Seg kernel asms L g 1 2327 (factsAt L g 2327 d) 2328 (factsAt L g 2328 d) := by
  intro t h
  sm_seg h

theorem live_2327_2326 : ∀ r ∈ Flow.live 2327, r ∈ Flow.live 2326 := by decide +kernel

/-- **The named barrier before the store of `O`** (pc 2326): the guard of the store is set
(pc 2327) and the store is next. -/
theorem step_bar24 {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .bar24) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2326 := by rw [hs]; rfl
  have hc' : kernel.code[2326]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_24)
  refine step_seg (dn := { d with site := .stO }) (n := 1)
    (fun hf' => fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf')
    (by simp [next, hs]) (by rw [hpc]; exact live_2327_2326) ?_
    (inv_late hi (by rw [hs]; trivial) (s := .stO) trivial (fun h => absurd h (by simp))) h hf
  rw [hpc]
  exact seg_2327 d

/-! ### The store of the products (pc 2328) -/

theorem live_2329_2328 : ∀ r ∈ Flow.live 2329, r ∈ Flow.live 2328 := by decide +kernel

/-- **The `tcgen05.st` of the rescaled words** (pc 2328, guarded by `%p171`): the event stores
the 64 words. -/
theorem step_stO {d : D} {t u : TState} {e : Event} {ins : Instr} (hi : Inv L g d)
    (hs : d.site = .stO) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 2328 := by rw [hs]; rfl
  have hc' : kernel.code[2328]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_tmemStore_1)
  have h1611 : t.regs 1611 = some (b32 ((d.stg.bw * 2097152 +
      (d.e.tm + 256) % 2 ^ 32) % 2 ^ 32)) := by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show 1611 ∈ Flow.live d.site.pc by rw [hpc]; decide +kernel))
    have e1 : valueOf L g d 1611 = b32 ((d.stg.bw * 2097152 +
        (d.e.tm + 256) % 2 ^ 32) % 2 ^ 32) := by sm_vals
    rw [e1] at this
    exact this
  have hf' := hpc ▸ hf
  obtain ⟨⟨vals, rfl⟩, hu⟩ := fires_tcSt (A := asms) h1611 (Nat.mod_lt _ (by decide)) hf'
  exact step_adv (dn := { d with site := .waitStO }) (fun _ => hu) (by simp [next, hs])
    (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_2329_2328)
    (inv_late hi (by rw [hs]; trivial) (s := .waitStO) trivial (fun h => absurd h (by simp)))
    h hf

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
