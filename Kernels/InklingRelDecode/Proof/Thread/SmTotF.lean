-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotE

@[expose] public section

/-! # The score stage's second half on any words: exponentials, selections and sum (pcs 2089-2233)

The pieces of `SmStgA` (`seg_ex2one`, `seg_selp1`) and `SmStgB` (the packs and the sum tree, the
unpack and the last sum) for any words: the registers hold Core's outcomes (`ex2E`, `movE` of a
`selp`, `packE`, `add2NE`, `unpackE`, `floatE` of `add`) on the values of the earlier pieces
(`SmTotD`, `SmTotE`). An instruction that faults kills the thread. `seg_stageT` composes the
whole stretch from the shuffle of the row maximum (pc 1838) to the shuffle of the half sums
(pc 2234) under the condition `D.s2Ok`; the read-out lemmas give the registers live at pc 2234
(`D.mnT`, `D.kpT`, `D.alT`, `D.pvT`, `D.swT`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

theorem okVal_four {E : Exec Value} (h : Four E) : (okVal (b32 0) E).bytes = 4 := by
  rcases hE : E with e | v
  · rfl
  · exact h v hE

theorem movE_four (v : Value) : Four (movE v) := by
  intro x hx
  unfold movE at hx
  split_ifs at hx with h
  · cases hx; exact h

/-! ### The 64 exponentials (pcs 2089 to 2152) -/

theorem zT_bytes (d : D) (recv : Value) (j : Nat) : (d.zT recv j).bytes = 4 :=
  okVal_four (ex2E_four _ _)

theorem valueEx_e2T_off (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {r : Nat} (j : Nat) (h : ∀ k < j, r ≠ 1287 + 2 * k) :
    valueEx B (e2T d recv j ++ ex) r = valueEx B ex r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [e2T, List.cons_append, valueEx_cons_ne _ _ (h j (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_e2T_in (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {j k : Nat} (hk : k < j) : valueEx B (e2T d recv j ++ ex) (1287 + 2 * k) = d.zT recv k := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [e2T, List.cons_append]
    by_cases h : k = j
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

theorem segEx2T1 (d : D) (recv : Value) {j : Nat} (hj : j < 64) :
    SegD kernel asms L g 1 (2089 + j)
      (factsFrom (Flow.live (2089 + j))
        (valueEx (valueOf L g d) (e2T d recv j ++ base2T d recv)))
      (2089 + j + 1)
      (factsFrom (Flow.live (2089 + j + 1))
        (valueEx (valueOf L g d) (e2T d recv (j + 1) ++ base2T d recv)))
      ((d.zTE recv j).toBool = true) := by
  obtain ⟨la, ld⟩ := live_ex2 j hj
  refine SegD.set1v (ex2At_spec (ex2_code j hj)) rfl (fun t h => ?_) ld
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_ex2 j hj
  have hp : t.pc = 2089 + j := h.1
  have ra : t.regs (1288 + 2 * j) = some (d.xT recv j) :=
    reg_of h.2.2.2.2 la (by
      rw [valueEx_e2T_off d recv _ _ j (fun k hk => by omega), base2T,
        valueEx_emT_off d recv _ _ 16 (fun k hk => by omega)]
      exact valueEx_fxT_in d recv _ _ hj)
  obtain ⟨hA, hD⟩ := approxAt_ex2 (L := L) (g := g) hE (by omega) (by omega) (by omega)
  show execLocalA asms L g t (ex2Op (1287 + 2 * j) (1288 + 2 * j)) = _
  exact exec_ex2E hA hD (OpndIs.reg ra)

/-- **The first `m` exponentials on any words.** -/
theorem segEx2TN (d : D) (recv : Value) : ∀ m, m ≤ 64 →
    SegD kernel asms L g m 2089
      (factsFrom (Flow.live 2089) (valueEx (valueOf L g d) (base2T d recv))) (2089 + m)
      (factsFrom (Flow.live (2089 + m))
        (valueEx (valueOf L g d) (e2T d recv m ++ base2T d recv)))
      (∀ j < m, (d.zTE recv j).toBool = true) := by
  intro m
  induction m with
  | zero =>
    exact fun _ => SegD.iff (SegD.of_seg (Seg.refl _ _)) ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    exact fun hm => SegD.iff ((ih (by omega)).comp (segEx2T1 d recv (j := m) (by omega)))
      ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h1 j h
        · exact h2,
       fun h => ⟨fun j hj => h j (by omega), h m (by omega)⟩⟩

/-! ### The 16 selections (pcs 2153 to 2168) -/

theorem valueOf_pick (d : D) {i : Nat} (hi : i < 16) :
    valueOf L g d (179 + i / 8) = .pred (d.pickT L g i) := by
  unfold D.pickT
  have : i / 8 = 0 ∨ i / 8 = 1 := by omega
  rcases this with h | h <;> rw [h] <;> simp
  · exact valueOf_p180 d
  · exact valueOf_p181 d

theorem sT_bytes (d : D) (recv : Value) (i : Nat) : (d.sT L g recv i).bytes = 4 :=
  okVal_four (movE_four _)

theorem valueEx_sl16T_off (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {r : Nat} (n : Nat) (h : ∀ k < n, r ≠ 508 + k) :
    valueEx B (sl16T L g d recv n ++ ex) r = valueEx B ex r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sl16T, List.cons_append, valueEx_cons_ne _ _ (h n (by omega))]
    exact ih fun k hk => h k (by omega)

theorem valueEx_sl16T_in (d : D) (recv : Value) (B : Nat → Value) (ex : List (Nat × Value))
    {n k : Nat} (hk : k < n) :
    valueEx B (sl16T L g d recv n ++ ex) (508 + k) = d.sT L g recv k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sl16T, List.cons_append]
    by_cases h : k = n
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

theorem segSelpT1 (d : D) (recv : Value) {i : Nat} (hi : i < 16) :
    SegD kernel asms L g 1 (2153 + i)
      (factsFrom (Flow.live (2153 + i))
        (valueEx (valueOf L g d) (sl16T L g d recv i ++ base3T d recv))) (2153 + i + 1)
      (factsFrom (Flow.live (2153 + i + 1))
        (valueEx (valueOf L g d) (sl16T L g d recv (i + 1) ++ base3T d recv)))
      ((d.sTE L g recv i).toBool = true) := by
  obtain ⟨la, lb, lp, ld⟩ := live_selp i hi
  have hk := colR_lt i hi
  refine SegD.set1v (selp3At_spec (selp_code i hi)) rfl (fun t h => ?_) ld
  have hE : Assumptions.emuSites.contains t.pc = false := by
    rw [h.1]; exact emu_selp i hi
  have F := h.2.2.2.2
  have ra : t.regs (1271 + i) = some (d.yT recv i) :=
    reg_of F la (by
      rw [valueEx_sl16T_off d recv _ _ i (fun k hk => by omega), base3T,
        valueEx_e2T_off d recv _ _ 64 (fun k hk => by omega)]
      exact valueEx_emT_in d recv _ _ (by omega))
  have rb : t.regs (1287 + 2 * colR i) = some (d.zT recv (colR i)) :=
    reg_of F lb (by
      rw [valueEx_sl16T_off d recv _ _ i (fun k hk => by omega), base3T]
      exact valueEx_e2T_in d recv _ _ hk)
  have rp : t.regs (179 + i / 8) = some (.pred (d.pickT L g i)) :=
    reg_of F lp (by
      rw [valueEx_sl16T_off d recv _ _ i (fun k hk => by omega), base3T,
        valueEx_e2T_off d recv _ _ 64 (fun k hk => by omega), base2T,
        valueEx_emT_off d recv _ _ 16 (fun k hk => by omega),
        valueEx_fxT_off d recv _ _ 64 (fun k hk => by omega),
        valueEx_xb10_off d recv _ (by omega), valueOf_pick d hi])
  show execLocalA asms L g t (selpOp (508 + i) (.reg (1271 + i)) (.reg (1287 + 2 * colR i))
    (179 + i / 8)) = _
  exact exec_selpE (segFree hE) rp (readValue_reg ra) (readValue_reg rb)

/-- **The first `m` selections on any words.** -/
theorem segSelpTN (d : D) (recv : Value) : ∀ m, m ≤ 16 →
    SegD kernel asms L g m 2153
      (factsFrom (Flow.live 2153) (valueEx (valueOf L g d) (base3T d recv))) (2153 + m)
      (factsFrom (Flow.live (2153 + m))
        (valueEx (valueOf L g d) (sl16T L g d recv m ++ base3T d recv)))
      (∀ i < m, (d.sTE L g recv i).toBool = true) := by
  intro m
  induction m with
  | zero =>
    exact fun _ => SegD.iff (SegD.of_seg (Seg.refl _ _)) ⟨fun _ j hj => absurd hj (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    exact fun hm => SegD.iff ((ih (by omega)).comp (segSelpT1 d recv (i := m) (by omega)))
      ⟨fun ⟨h1, h2⟩ j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
        · exact h1 j h
        · exact h2,
       fun h => ⟨fun j hj => h j (by omega), h m (by omega)⟩⟩

/-! ### The packs and the sum tree (pcs 2169 to 2231) -/

theorem psV_succ {sg : Nat → Value} {c : Nat} {i : PI} (h : psCode[c]? = some i) :
    psV sg (c + 1) = i.updV sg (psV sg c) := by
  unfold psV
  rw [List.take_succ, h]
  simp [List.foldl_append]

theorem psV_keys (sg : Nat → Value) : ∀ c, (psV sg c).map Prod.fst = (psSt c).map Prod.fst := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
    rcases h : psCode[c]? with _ | i
    · have hl : psCode.length ≤ c := List.getElem?_eq_none_iff.mp h
      have e1 : psCode.take (c + 1) = psCode.take c := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp only [psV, psSt, e1]
      exact ih
    · rw [psV_succ h, psSt_succ h]
      cases i <;> simp [PI.updV, PI.upd, ih]

theorem valueEx_psV_free {sg : Nat → Value} {c r : Nat} (B : Nat → Value)
    (ex : List (Nat × Value)) (hc : c ≤ 63) (hr : ¬ psKey r) :
    valueEx B (psV sg c ++ ex) r = valueEx B ex r := by
  unfold valueEx
  rw [lookup_append_none]
  intro hm
  rw [psV_keys] at hm
  exact hr (psSt_keys' c hc r hm)

theorem valueEx_psV_off {sg : Nat → Value} {c r : Nat} (B : Nat → Value)
    (ex : List (Nat × Value)) (hc : c ≤ 63) (hr : r < 1994) :
    valueEx B (psV sg c ++ ex) r = valueEx B ex r :=
  valueEx_psV_free B ex hc (by unfold psKey; omega)

theorem lookup_isSome_keys {β : Type} {st : List (Nat × Value)} {sm : List (Nat × β)} {r : Nat}
    (h : st.map Prod.fst = sm.map Prod.fst) (hs : (sm.lookup r).isSome = true) :
    ∃ v, st.lookup r = some v := by
  induction st generalizing sm with
  | nil =>
    cases sm with
    | nil => simp at hs
    | cons p sm => simp at h
  | cons p st ih =>
    cases sm with
    | nil => simp at h
    | cons q sm =>
      obtain ⟨k, v⟩ := p
      obtain ⟨k', m⟩ := q
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [List.lookup] at hs ⊢
      split
      · exact ⟨v, rfl⟩
      · rename_i hne
        simp only [hne] at hs
        exact ih h hs

theorem segPsT1 (d : D) (recv : Value) {c : Nat} (hc : c < 63) {i : PI}
    (hi : psCode[c]? = some i) :
    SegD kernel asms L g 1 (2169 + c)
      (factsFrom (Flow.live (2169 + c))
        (valueEx (valueOf L g d) (psV (sgT L g d recv) c ++ base4T L g d recv)))
      (2169 + c + 1)
      (factsFrom (Flow.live (2169 + c + 1))
        (valueEx (valueOf L g d) (psV (sgT L g d recv) (c + 1) ++ base4T L g d recv)))
      (i.okV (sgT L g d recv) (psV (sgT L g d recv) c) = true) := by
  have hck := ps_chk c hc
  unfold psChk at hck
  rw [hi] at hck
  rw [psV_succ hi]
  cases i with
  | pk e a b =>
    simp only [PI.chk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      List.contains_iff_mem] at hck
    obtain ⟨⟨⟨⟨⟨⟨⟨hp, hsa⟩, hsb⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩, hcol⟩ := hck
    simp only [PI.updV, PI.okV, List.cons_append]
    refine SegD.set1v (packAt_spec hp) rfl (fun t h => ?_) hsub
    have hE : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; simpa using hemu
    have F := h.2.2.2.2
    have ra : t.regs a = some (sgT L g d recv a) := reg_of F hla (by
      rw [valueEx_psV_off _ _ (by omega) (by unfold isSingle at hsa; simp at hsa; omega)])
    have rb : t.regs b = some (sgT L g d recv b) := reg_of F hlb (by
      rw [valueEx_psV_off _ _ (by omega) (by unfold isSingle at hsb; simp at hsb; omega)])
    exact exec_packE_at asms_movesSm ((segFree hE).at rfl) ra rb
  | ad e a b =>
    simp only [PI.chk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
      List.contains_iff_mem] at hck
    obtain ⟨⟨⟨⟨⟨⟨⟨hp, hsa⟩, hsb⟩, -⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩ := hck
    simp only [PI.updV, PI.okV, List.cons_append]
    refine SegD.set1v (add2At_spec hp) rfl (fun t h => ?_) hsub
    have hE : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; simpa using hemu
    have hp' : t.pc = 2169 + c := h.1
    have F := h.2.2.2.2
    obtain ⟨va, hva⟩ := lookup_isSome_keys (psV_keys (sgT L g d recv) c) hsa
    obtain ⟨vb, hvb⟩ := lookup_isSome_keys (psV_keys (sgT L g d recv) c) hsb
    have ra : t.regs a = some (lkV (psV (sgT L g d recv) c) a) := reg_of F hla (by
      unfold valueEx lkV
      rw [lookup_append_some (v := va) hva, hva]; rfl)
    have rb : t.regs b = some (lkV (psV (sgT L g d recv) c) b) := reg_of F hlb (by
      unfold valueEx lkV
      rw [lookup_append_some (v := vb) hvb, hvb]; rfl)
    show execLocalA asms L g t (.float { add2NI with
      dsts := [some e], srcs := [.reg a, .reg b] }) = _
    exact exec_add2NE (idealAtSc (L := L) (g := g) (by decide) hE)
      (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega)) ra rb

/-- **The first `m` instructions of the packs and the sum tree on any words.** -/
theorem segPsTN (d : D) (recv : Value) : ∀ m, m ≤ 63 →
    SegD kernel asms L g m 2169
      (factsFrom (Flow.live 2169) (valueEx (valueOf L g d) (base4T L g d recv))) (2169 + m)
      (factsFrom (Flow.live (2169 + m))
        (valueEx (valueOf L g d) (psV (sgT L g d recv) m ++ base4T L g d recv)))
      (PsOk (sgT L g d recv) m) := by
  intro m
  induction m with
  | zero =>
    exact fun _ => SegD.iff (SegD.of_seg (Seg.refl _ _)) ⟨fun _ c hc => absurd hc (by omega),
      fun _ => trivial⟩
  | succ m ih =>
    intro hm
    have hl : m < psCode.length := by rw [psCode_length]; omega
    have hi : psCode[m]? = some psCode[m] := List.getElem?_eq_getElem hl
    exact SegD.iff ((ih (by omega)).comp (segPsT1 d recv (c := m) (by omega) hi))
      ⟨fun ⟨h1, h2⟩ c hc i hci => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | rfl
        · exact h1 c h i hci
        · rw [hi] at hci; cases hci; exact h2,
       fun h => ⟨fun c hc i hci => h c (by omega) i hci, h m (by omega) _ hi⟩⟩

/-! ### The unpack and the last sum (pcs 2232 and 2233) -/

theorem swT_bytes (d : D) (recv : Value) : (d.swT L g recv).bytes = 4 :=
  okVal_four (floatE_add_four _ _)

/-- The overlay after the unpack. -/
abbrev xt1T (L : Launch) (g : Nat) (d : D) (recv : Value) : List (Nat × Value) :=
  (1528, (d.uT L g recv).2) :: (1527, (d.uT L g recv).1) ::
    (psV (sgT L g d recv) 63 ++ base4T L g d recv)

/-- **The overlay after the stage's second half** (at the shuffle of the half sums). -/
abbrev xtT (L : Launch) (g : Nat) (d : D) (recv : Value) : List (Nat × Value) :=
  (1529, d.swT L g recv) :: xt1T L g d recv

theorem segT1T (d : D) (recv : Value) :
    SegD kernel asms L g 1 2232
      (factsFrom (Flow.live 2232)
        (valueEx (valueOf L g d) (psV (sgT L g d recv) 63 ++ base4T L g d recv)))
      2233 (factsFrom (Flow.live 2233) (valueEx (valueOf L g d) (xt1T L g d recv)))
      ((d.uTE L g recv).toBool = true) := by
  obtain ⟨l1, l2, -, -, -, e1, -, hr⟩ := live_tail
  refine SegD.twoT (lo := 1527) (hi := 1528) Flow.code_2232 rfl (fun t h => ?_) (by decide)
    (fun x hx => ?_) (fun r hr' => ?_)
  · have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree e1
    have hsome : ((psSt 63).lookup 2345).isSome = true := by rw [hr]; rfl
    obtain ⟨v, hv⟩ := lookup_isSome_keys (psV_keys (sgT L g d recv) 63) hsome
    have ra : t.regs 2345 = some (d.rootT L g recv) := reg_of h.2.2.2.2 l1 (by
      unfold valueEx D.rootT lkV
      rw [lookup_append_some (v := v) hv, hv]; rfl)
    exact exec_unpackET hS ra
  · have hu : d.uT L g recv = x := by unfold D.uT; rw [hx]
    refine ⟨?_, ?_⟩
    · rw [valueEx_cons_ne _ _ (by decide), valueEx_cons_self, hu]
    · rw [valueEx_cons_self, hu]
  · rcases subX_cov2 l2 r hr' with rfl | rfl | ⟨h1, h2, h3⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, by rw [valueEx_cons_ne _ _ h2, valueEx_cons_ne _ _ h1]⟩)

theorem segT2T (d : D) (recv : Value) :
    SegD kernel asms L g 1 2233
      (factsFrom (Flow.live 2233) (valueEx (valueOf L g d) (xt1T L g d recv))) 2234
      (factsFrom (Flow.live 2234) (valueEx (valueOf L g d) (xtT L g d recv)))
      ((d.swTE L g recv).toBool = true) := by
  obtain ⟨-, -, l1, l2, l3, -, e2, -⟩ := live_tail
  refine SegD.set1v Flow.code_2233 rfl (fun t h => ?_) l3
  have hE : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; exact e2
  have hp : t.pc = 2233 := h.1
  have ra : t.regs 1527 = some (d.uT L g recv).1 :=
    reg_of h.2.2.2.2 l1 (by simp [valueEx, List.lookup])
  have rb : t.regs 1528 = some (d.uT L g recv).2 :=
    reg_of h.2.2.2.2 l2 (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (addOp 1529 1527 1528) = _
  exact exec_addE_at (idealAtSc (L := L) (g := g) (by decide) hE)
    (declineAtSc (L := L) (g := g) (by decide) hE (by omega) (by omega) (by omega))
    (OpndIs.reg ra) (OpndIs.reg rb)

/-! ### The whole stretch -/

/-- **The stretch from the shuffle of the row maximum to the shuffle of the half sums on any
words** (pcs 1839 to 2233): the thread reaches pc 2234 with the overlay `xtT`, or is dead where
an instruction faults. -/
theorem seg_stageT (d : D) (recv : Value) :
    ∃ n, SegD kernel asms L g n 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 2234
      (factsFrom (Flow.live 2234) (valueEx (valueOf L g d) (xtT L g d recv)))
      (d.s2Ok L g recv) := by
  have h1 := segAT (L := L) (g := g) d recv
  have h2 := segFmaTN (L := L) (g := g) d recv 64 (le_refl _)
  obtain ⟨k3, h3⟩ := segEmuTN (L := L) (g := g) d recv 16 (le_refl _)
  have h4 := segEx2TN (L := L) (g := g) d recv 64 (le_refl _)
  have h5 := segSelpTN (L := L) (g := g) d recv 16 (le_refl _)
  have h6 := segPsTN (L := L) (g := g) d recv 63 (le_refl _)
  have h7 := segT1T (L := L) (g := g) d recv
  have h8 := segT2T (L := L) (g := g) d recv
  exact ⟨_, SegD.iff (((((((h1.comp h2).comp h3).comp h4).comp h5).comp h6).comp h7).comp h8)
    ⟨fun ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, i⟩, j⟩, k⟩ => ⟨a, b, c, e, f, i, j, k⟩,
     fun ⟨a, b, c, e, f, i, j, k⟩ => ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, i⟩, j⟩, k⟩⟩⟩

/-! ### The registers live at the shuffle of the half sums -/

theorem pvT_bytes (d : D) (recv : Value) (k : Nat) : (d.pvT L g recv k).bytes = 4 := by
  unfold D.pvT
  split
  · exact sT_bytes d recv _
  · exact zT_bytes d recv _

theorem selIdx_colR : ∀ i < 16, selIdx (colR i) = some i := by decide +kernel

theorem selIdx_pair : ∀ q < 24, selIdx (2 * pairW q) = none ∧ selIdx (2 * pairW q + 1) = none :=
  by decide +kernel

theorem pvT_colR (d : D) (recv : Value) {i : Nat} (hi : i < 16) :
    d.pvT L g recv (colR i) = d.sT L g recv i := by
  unfold D.pvT; rw [selIdx_colR i hi]

/-- The pack of the pair register `%rd(46 + q)` is the last write of its key. -/
def pkLast (q : Nat) : Bool :=
  match psCode.reverse.find? (fun i => i.dst == 1994 + q) with
  | some (.pk d a b) => d == 1994 + q && a == 1287 + 2 * (2 * pairW q) &&
      b == 1287 + 2 * (2 * pairW q + 1)
  | _ => false

theorem pkLast_all : ∀ q < 24, pkLast q = true := by decide +kernel

theorem lookup_fold_pk (sg : Nat → Value) {r a b : Nat} :
    ∀ (is : List PI) (st0 : List (Nat × Value)),
      is.reverse.find? (fun i => i.dst == r) = some (.pk r a b) →
      (is.foldl (fun st i => i.updV sg st) st0).lookup r =
        some (okVal (b32 0) (packE (sg a) (sg b))) := by
  intro is
  induction is using List.reverseRecOn with
  | nil => intro st0 h; simp at h
  | append_singleton l x ih =>
    intro st0 h
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      List.find?_cons] at h
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hx : x.dst = r
    · simp only [hx, beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp [PI.updV]
    · simp only [beq_false_of_ne hx] at h
      have := ih st0 h
      cases x with
      | pk d a' b' =>
        have hne : r ≠ d := fun e => hx (e ▸ rfl)
        simp only [PI.updV, List.lookup, beq_false_of_ne hne]
        exact this
      | ad d a' b' =>
        have hne : r ≠ d := fun e => hx (e ▸ rfl)
        simp only [PI.updV, List.lookup, beq_false_of_ne hne]
        exact this

theorem psV_pair (sg : Nat → Value) {q : Nat} (hq : q < 24) :
    (psV sg 63).lookup (1994 + q) = some (okVal (b32 0)
      (packE (sg (1287 + 2 * (2 * pairW q))) (sg (1287 + 2 * (2 * pairW q + 1))))) := by
  have h := pkLast_all q hq
  unfold pkLast at h
  have htake : psCode.take 63 = psCode := List.take_of_length_le (by rw [psCode_length])
  unfold psV
  rw [htake]
  split at h
  · rename_i d a b hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact lookup_fold_pk sg psCode [] hf
  · cases h

/-! ### The read-out at pc 2234 -/

section
variable (d : D) (recv : Value) (B : Nat → Value)

theorem xtT_free {r : Nat} (h : ovFree r) : valueEx B (xtT L g d recv) r = B r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  simp only [xtT, xt1T, base4T, base3T, base2T]
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega), valueEx_psV_free _ _ (le_refl _) h1,
    valueEx_sl16T_off d recv _ _ 16 (fun k hk => by omega),
    valueEx_e2T_off d recv _ _ 64 (fun k hk => by omega),
    valueEx_emT_off d recv _ _ 16 (fun k hk => by omega),
    valueEx_fxT_off d recv _ _ 64 (fun k hk => by omega),
    valueEx_xb10_off d recv _ (by omega)]

theorem xtT_xb10 {r : Nat} (h1 : ¬ psKey r) (h2 : ¬ (508 ≤ r ∧ r < 524))
    (h3 : ¬ (1269 ≤ r ∧ r < 1415)) (h4 : ¬ (1527 ≤ r ∧ r < 1530)) :
    valueEx B (xtT L g d recv) r = valueEx B (xb10 d recv) r := by
  simp only [xtT, xt1T, base4T, base3T, base2T]
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega), valueEx_psV_free _ _ (le_refl _) h1,
    valueEx_sl16T_off d recv _ _ 16 (fun k hk => by omega),
    valueEx_e2T_off d recv _ _ 64 (fun k hk => by omega),
    valueEx_emT_off d recv _ _ 16 (fun k hk => by omega),
    valueEx_fxT_off d recv _ _ 64 (fun k hk => by omega)]

theorem xtT_1522 : valueEx B (xtT L g d recv) 1522 = d.mnT recv := by
  rw [xtT_xb10 d recv B (by unfold psKey; omega) (by omega) (by omega) (by omega)]
  simp [valueEx, List.lookup]

theorem xtT_168 : valueEx B (xtT L g d recv) 168 = .pred (d.kpT recv) := by
  rw [xtT_xb10 d recv B (by unfold psKey; omega) (by omega) (by omega) (by omega)]
  simp [valueEx, List.lookup]

theorem xtT_507 : valueEx B (xtT L g d recv) 507 = d.alT recv := by
  rw [xtT_xb10 d recv B (by unfold psKey; omega) (by omega) (by omega) (by omega)]
  simp [valueEx, List.lookup]

theorem xtT_1529 : valueEx B (xtT L g d recv) 1529 = d.swT L g recv := by
  simp [valueEx, List.lookup]

theorem xtT_single {k : Nat} (hk : k < 16) :
    valueEx B (xtT L g d recv) (508 + k) = d.pvT L g recv (colR k) := by
  simp only [xtT, xt1T, base4T]
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega), valueEx_psV_off _ _ (le_refl _) (by omega),
    valueEx_sl16T_in d recv _ _ hk, pvT_colR d recv hk]

theorem sgT_col (k : Nat) (hk : k < 64) :
    sgT L g d recv (1287 + 2 * k) = d.zT recv k := by
  simp only [sgT, base4T]
  rw [valueEx_sl16T_off d recv _ _ 16 (fun j hj => by omega)]
  exact valueEx_e2T_in d recv _ _ hk

theorem xtT_pair {q : Nat} (hq : q < 24) :
    valueEx B (xtT L g d recv) (1994 + q) =
      joinValue (d.pvT L g recv (2 * pairW q)) (d.pvT L g recv (2 * pairW q + 1)) := by
  have hw := pairW_lt q hq
  obtain ⟨n1, n2⟩ := selIdx_pair q hq
  simp only [xtT, xt1T]
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega)]
  unfold valueEx
  rw [lookup_append_some (psV_pair (sgT L g d recv) hq), Option.getD_some,
    sgT_col d recv _ (by omega), sgT_col d recv _ hw]
  have e1 : d.pvT L g recv (2 * pairW q) = d.zT recv (2 * pairW q) := by
    unfold D.pvT; rw [n1]
  have e2 : d.pvT L g recv (2 * pairW q + 1) = d.zT recv (2 * pairW q + 1) := by
    unfold D.pvT; rw [n2]
  rw [e1, e2, okVal_of_ok (show packE _ _ = _ by
    unfold packE; rw [if_pos ⟨zT_bytes d recv _, zT_bytes d recv _⟩])]

end

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
