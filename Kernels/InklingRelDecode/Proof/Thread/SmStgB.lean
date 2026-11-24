-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmStgA
public import Lemmas.Flow.ArithCore

@[expose] public section

/-! # The packs and the sum of the probabilities (pcs 2169-2233)

After the 16 selections the thread holds the 64 probabilities of its columns as `%r47 …` (the
selected columns) and `%r(826 + 2 j)` (the others). 32 packs (`mov.b64`) make pairs of them, 31
`add.f32x2` add the pairs into one pair `%rd397`, whose halves are added (`%r1068`) after the
unpack.

A pair register holds the sums of two sets of columns. The sets are tracked as 64-bit masks
(`PI`, `psCode`, `psSt`: an abstract instruction list checked against the program by
`decide +kernel`, as for the row maximum in `SmMax`); the facts after `c` instructions are the live
registers valued by an overlay of the written pairs (`psEx`), each the pair of the sums `smask`
of its two sets. That the root `%rd397` holds all 64 columns once, as two disjoint sets, is
`decide +kernel`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Softmax
open Classical

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat}

/-! ### Sums over masks -/

/-- The probability of column `k`. -/
def D.pk (d : D) (rE : EReal) (k : Nat) : ℝ := Softmax.pow2 (d.xE rE k)

/-- The sum of the probabilities of the columns whose bit is set in `m`. -/
def D.smask (d : D) (rE : EReal) (m : Nat) : ℝ :=
  ((Finset.range 64).filter fun k => m.testBit k).sum (d.pk rE)

theorem smask_pow (d : D) (rE : EReal) {k : Nat} (hk : k < 64) :
    d.smask rE (2 ^ k) = d.pk rE k := by
  unfold D.smask
  have : (Finset.range 64).filter (fun j => (2 ^ k).testBit j) = {k} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.testBit_two_pow]
    constructor
    · rintro ⟨-, h⟩
      exact (of_decide_eq_true h).symm
    · rintro rfl
      exact ⟨hk, by simp⟩
  rw [this, Finset.sum_singleton]

theorem smask_or (d : D) (rE : EReal) {a b : Nat} (h : a &&& b = 0) :
    d.smask rE (a ||| b) = d.smask rE a + d.smask rE b := by
  unfold D.smask
  have hu : (Finset.range 64).filter (fun k => (a ||| b).testBit k) =
      (Finset.range 64).filter (fun k => a.testBit k) ∪
        (Finset.range 64).filter (fun k => b.testBit k) := by
    ext k
    simp [Nat.testBit_or, and_or_left]
  have hd : Disjoint ((Finset.range 64).filter fun k => a.testBit k)
      ((Finset.range 64).filter fun k => b.testBit k) := by
    rw [Finset.disjoint_left]
    intro k hka hkb
    simp only [Finset.mem_filter] at hka hkb
    have := congrArg (fun n => n.testBit k) h
    simp [Nat.testBit_and, hka.2, hkb.2] at this
  rw [hu, Finset.sum_union hd]

theorem smask_full (d : D) (rE : EReal) :
    d.smask rE (2 ^ 64 - 1) = ((List.range 64).map (d.pk rE)).sum := by
  unfold D.smask
  have : (Finset.range 64).filter (fun k => (2 ^ 64 - 1).testBit k) = Finset.range 64 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_two_pow_sub_one,
      decide_eq_true_eq]
    tauto
  rw [this, ← List.toFinset_range, List.sum_toFinset _ List.nodup_range]

theorem psCode_length : psCode.length = 63 := by decide +kernel

/-- The register-mask list after the first `c` instructions. -/
def psSt (c : Nat) : List (Nat × (Nat × Nat)) :=
  (psCode.take c).foldl (fun st i => i.upd st) []

theorem psSt_succ {c : Nat} {i : PI} (h : psCode[c]? = some i) :
    psSt (c + 1) = i.upd (psSt c) := by
  unfold psSt
  rw [List.take_succ, h]
  simp [List.foldl_append]

/-- `add.f32x2 d, a, b` over registers (no rounding modifier). -/
def add2In (d a b : Nat) : FloatInstr :=
  { op := .add, ty := ⟨.f32, 2⟩, dsts := [some d], srcs := [.reg a, .reg b] }

/-- The instruction at `pc` is `add.f32x2 d, a, b` over registers. -/
def add2At (pc d a b : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .float f⟩ => f == add2In d a b
  | _ => false

theorem add2At_spec {pc d a b : Nat} (h : add2At pc d a b = true) :
    kernel.code[pc]? = some ⟨none, .float (add2In d a b)⟩ := by
  unfold add2At at h
  split at h
  · rename_i f hc
    rw [hc, beq_iff_eq.mp h]
  · cases h

/-- What instruction `i` at `pc` must satisfy. -/
def PI.chk (pc : Nat) (st : List (Nat × (Nat × Nat))) : PI → Bool
  | .pk d a b => packAt pc d a b 64 && isSingle a && isSingle b && (Flow.live pc).contains a &&
      (Flow.live pc).contains b && subX (Flow.live (pc + 1)) (Flow.live pc) [d] &&
      !(Assumptions.emuSites.contains pc) && decide (colOfReg a < 64 ∧ colOfReg b < 64)
  | .ad d a b => add2At pc d a b && (st.lookup a).isSome && (st.lookup b).isSome &&
      decide ((lkp st a).1 &&& (lkp st b).1 = 0 ∧ (lkp st a).2 &&& (lkp st b).2 = 0) &&
      (Flow.live pc).contains a && (Flow.live pc).contains b &&
      subX (Flow.live (pc + 1)) (Flow.live pc) [d] && !(Assumptions.emuSites.contains pc)

def psChk (c : Nat) : Bool :=
  match psCode[c]? with
  | some i => i.chk (2169 + c) (psSt c)
  | none => false

theorem ps_chk : ∀ c < 63, psChk c = true := by decide +kernel

/-- The root of the tree holds the two disjoint halves of all 64 columns. -/
theorem ps_root : lkp (psSt 63) (1948 + 397) = ((lkp (psSt 63) (1948 + 397)).1,
    (lkp (psSt 63) (1948 + 397)).2) ∧
    (lkp (psSt 63) (1948 + 397)).1 &&& (lkp (psSt 63) (1948 + 397)).2 = 0 ∧
    (lkp (psSt 63) (1948 + 397)).1 ||| (lkp (psSt 63) (1948 + 397)).2 = 2 ^ 64 - 1 := by
  decide +kernel

/-! ### The local steps -/

theorem exec_add2N {t : TState} {d a b : Nat} {x0 x1 y0 y1 : ℝ}
    (hI : IdealAt asms .addRnF32x2 L g t)
    (ha : t.regs a = some (.pair (.float .f32 x0) (.float .f32 x1)))
    (hb : t.regs b = some (.pair (.float .f32 y0) (.float .f32 y1))) :
    execLocalA asms L g t (.float (add2In d a b)) =
      .ok (PTX.next (setReg t d (.pair (.float .f32 (x0 + y0)) (.float .f32 (x1 + y1))))) := by
  have hf : FloatForm.ofOp (.float (add2In d a b)) = some .addRnF32x2 := by
    simp [FloatForm.ofOp, add2In]
  have pa := pairRead_of (v := .pair (.float .f32 x0) (.float .f32 x1)) (valFloat_float x0)
    (valFloat_float x1)
  have pb := pairRead_of (v := .pair (.float .f32 y0) (.float .f32 y1)) (valFloat_float y0)
    (valFloat_float y1)
  have hex : execIdealFloat L g t (.float (add2In d a b)) =
      some (.ok (PTX.next (setReg t d (.pair (.float .f32 (x0 + y0))
        (.float .f32 (x1 + y1)))))) := by
    simp only [execIdealFloat, add2In, readERealPair_reg_val (L := L) (g := g) ha,
      readERealPair_reg_val (L := L) (g := g) hb, pa, pb, bindRead, addEReal_coe, erealValue_coe,
      pure, Except.pure]
  rw [hI _ hf _ hex]

/-- The value of a pair register: the sums of its two masks. -/
def D.pv (d : D) (rE : EReal) (p : Nat × Nat) : Value :=
  .pair (.float .f32 (d.smask rE p.1)) (.float .f32 (d.smask rE p.2))

/-- The overlay after `c` instructions: each written pair holds the sums of its masks. -/
def psEx (d : D) (rE : EReal) (c : Nat) : List (Nat × Value) :=
  (psSt c).map fun q => (q.1, d.pv rE q.2)

theorem lookup_psEx (d : D) (rE : EReal) (st : List (Nat × (Nat × Nat))) (r : Nat) :
    (st.map fun q => (q.1, d.pv rE q.2)).lookup r = (st.lookup r).map (d.pv rE) := by
  induction st with
  | nil => rfl
  | cons p st ih =>
    obtain ⟨k, m⟩ := p
    simp only [List.map_cons, List.lookup]
    split
    · rfl
    · exact ih

theorem psSt_keys : ∀ c ≤ 63, ∀ k ∈ (psSt c).map Prod.fst, 1994 ≤ k := by decide +kernel

theorem lookup_none_of_keys {α : Type} {r : Nat} : ∀ l : List (Nat × α),
    (∀ k ∈ l.map Prod.fst, r ≠ k) → l.lookup r = none
  | [], _ => rfl
  | p :: l, h => by
    obtain ⟨k, v⟩ := p
    have h1 : r ≠ k := h k (by simp)
    simp only [List.lookup, beq_false_of_ne h1]
    exact lookup_none_of_keys l fun k' hk' => h k' (List.mem_cons_of_mem _ hk')

theorem valueEx_ps_off {d : D} {rE : EReal} {c r : Nat} (B : Nat → Value)
    (ex : List (Nat × Value)) (hc : c ≤ 63) (hr : r < 1994) :
    valueEx B (psEx d rE c ++ ex) r = valueEx B ex r := by
  unfold valueEx
  rw [lookup_append_none]
  intro hm
  simp only [psEx, List.map_map, Function.comp_def, List.mem_map] at hm
  obtain ⟨q, hq, hqr⟩ := hm
  have := psSt_keys c hc r (List.mem_map.mpr ⟨q, hq, hqr⟩)
  omega

theorem valueEx_ps_in {d : D} {rE : EReal} {c r : Nat} {p : Nat × Nat} (B : Nat → Value)
    (ex : List (Nat × Value)) (h : (psSt c).lookup r = some p) :
    valueEx B (psEx d rE c ++ ex) r = d.pv rE p := by
  unfold valueEx psEx
  rw [lookup_append_some (v := d.pv rE p)]
  · rfl
  · rw [lookup_psEx, h]; rfl

theorem valueEx_sl16_in (d : D) (rE : EReal) (B : Nat → Value) (ex : List (Nat × Value))
    {n k : Nat} (hk : k < n) : valueEx B (sl16 d rE n ++ ex) (508 + k) =
      Value.float .f32 (Softmax.pow2 (d.xE rE (colR k))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sl16, List.cons_append]
    by_cases h : k = n
    · subst h; exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

/-- The overlay of the facts after the selections. -/
abbrev base4 (d : D) (recv : Value) : List (Nat × Value) :=
  sl16 d (eOf recv) 16 ++ base3 d recv

theorem valueEx_single (d : D) (recv : Value) (B : Nat → Value) {r : Nat}
    (hr : isSingle r = true) : valueEx B (base4 d recv) r =
      Value.float .f32 (d.pk (eOf recv) (colOfReg r)) := by
  unfold isSingle at hr
  simp only [decide_eq_true_eq] at hr
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨k, rfl⟩ : ∃ k, r = 508 + k := ⟨r - 508, by omega⟩
    have hk : k < 16 := by omega
    rw [base4, valueEx_sl16_in d _ _ _ hk]
    simp [colOfReg, D.pk, show 508 ≤ 508 + k ∧ 508 + k < 524 from ⟨by omega, by omega⟩]
  · obtain ⟨k, rfl⟩ : ∃ k, r = 1287 + 2 * k := ⟨(r - 1287) / 2, by omega⟩
    have hk : k < 64 := by omega
    rw [base4, valueEx_sl16_off d _ _ _ 16 (fun j hj => by omega), base3,
      valueEx_e2_in d _ _ _ hk]
    have : colOfReg (1287 + 2 * k) = k := by
      simp only [colOfReg]
      rw [if_neg (by omega)]
      omega
    rw [this]
    rfl

theorem seg_ps_pk {d : D} {recv : Value} {c a b e : Nat} (hi : psCode[c]? = some (.pk e a b))
    (hck : (PI.pk e a b).chk (2169 + c) (psSt c) = true) (hc : c < 63) :
    Seg kernel asms L g 1 (2169 + c)
      (factsFrom (Flow.live (2169 + c))
        (valueEx (valueOf L g d) (psEx d (eOf recv) c ++ base4 d recv)))
      (2169 + c + 1)
      (factsFrom (Flow.live (2169 + c + 1))
        (valueEx (valueOf L g d) (psEx d (eOf recv) (c + 1) ++ base4 d recv))) := by
  simp only [PI.chk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.contains_iff_mem] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hsa⟩, hsb⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩, hcol⟩ := hck
  have hrw : psEx d (eOf recv) (c + 1) = (e, d.pv (eOf recv) (2 ^ colOfReg a, 2 ^ colOfReg b)) ::
      psEx d (eOf recv) c := by
    unfold psEx
    rw [psSt_succ hi]
    rfl
  rw [hrw]
  refine Seg.set1 (K := kernel) (packAt_spec hp) rfl (fun t h => ?_) (subX_sound hsub)
  have hS : Assumption.SegFreePc asms t.pc := by
    rw [h.1]; exact segFree (by simpa using hemu)
  have F := h.2.2.2.2
  have ra : t.regs a = some (Value.float .f32 (d.pk (eOf recv) (colOfReg a))) := reg_of F hla (by
    rw [valueEx_ps_off _ _ (by omega) (by unfold isSingle at hsa; simp at hsa; omega)]
    exact valueEx_single d recv _ hsa)
  have rb : t.regs b = some (Value.float .f32 (d.pk (eOf recv) (colOfReg b))) := reg_of F hlb (by
    rw [valueEx_ps_off _ _ (by omega) (by unfold isSingle at hsb; simp at hsb; omega)]
    exact valueEx_single d recv _ hsb)
  rw [exec_pack hS (Or.inr rfl) ra rb rfl rfl]
  have e1 : d.smask (eOf recv) (2 ^ colOfReg a) = d.pk (eOf recv) (colOfReg a) :=
    smask_pow d _ hcol.1
  have e2 : d.smask (eOf recv) (2 ^ colOfReg b) = d.pk (eOf recv) (colOfReg b) :=
    smask_pow d _ hcol.2
  simp only [D.pv, e1, e2]
  rfl

theorem seg_ps_ad {d : D} {recv : Value} {c a b e : Nat} (hi : psCode[c]? = some (.ad e a b))
    (hck : (PI.ad e a b).chk (2169 + c) (psSt c) = true) (hc : c < 63) :
    Seg kernel asms L g 1 (2169 + c)
      (factsFrom (Flow.live (2169 + c))
        (valueEx (valueOf L g d) (psEx d (eOf recv) c ++ base4 d recv)))
      (2169 + c + 1)
      (factsFrom (Flow.live (2169 + c + 1))
        (valueEx (valueOf L g d) (psEx d (eOf recv) (c + 1) ++ base4 d recv))) := by
  simp only [PI.chk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    List.contains_iff_mem] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨hp, hsa⟩, hsb⟩, ⟨hd1, hd2⟩⟩, hla⟩, hlb⟩, hsub⟩, hemu⟩ := hck
  obtain ⟨pa, hpa⟩ := Option.isSome_iff_exists.mp hsa
  obtain ⟨pb, hpb⟩ := Option.isSome_iff_exists.mp hsb
  have hla' : lkp (psSt c) a = pa := by simp [lkp, hpa]
  have hlb' : lkp (psSt c) b = pb := by simp [lkp, hpb]
  rw [hla', hlb'] at hd1 hd2
  have hrw : psEx d (eOf recv) (c + 1) =
      (e, d.pv (eOf recv) (pa.1 ||| pb.1, pa.2 ||| pb.2)) :: psEx d (eOf recv) c := by
    unfold psEx
    rw [psSt_succ hi]
    simp only [PI.upd, hla', hlb', List.map_cons]
  rw [hrw]
  refine Seg.set1 (K := kernel) (add2At_spec hp) rfl (fun t h => ?_) (subX_sound hsub)
  have F := h.2.2.2.2
  have ra : t.regs a = some (.pair (.float .f32 (d.smask (eOf recv) pa.1))
      (.float .f32 (d.smask (eOf recv) pa.2))) :=
    reg_of F hla (valueEx_ps_in _ _ hpa)
  have rb : t.regs b = some (.pair (.float .f32 (d.smask (eOf recv) pb.1))
      (.float .f32 (d.smask (eOf recv) pb.2))) :=
    reg_of F hlb (valueEx_ps_in _ _ hpb)
  have hE' : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; simpa using hemu
  rw [exec_add2N (idealAtSc (L := L) (g := g) (by decide) hE') ra rb, D.pv,
    smask_or d _ hd1, smask_or d _ hd2]

/-- **One instruction of the packs and the sum tree.** -/
theorem seg_ps1 {d : D} {recv : Value} {c : Nat} (hc : c < 63) :
    Seg kernel asms L g 1 (2169 + c)
      (factsFrom (Flow.live (2169 + c))
        (valueEx (valueOf L g d) (psEx d (eOf recv) c ++ base4 d recv)))
      (2169 + c + 1)
      (factsFrom (Flow.live (2169 + c + 1))
        (valueEx (valueOf L g d) (psEx d (eOf recv) (c + 1) ++ base4 d recv))) := by
  have hck := ps_chk c hc
  have hi : psCode[c]? = some psCode[c] :=
    List.getElem?_eq_getElem (by rw [psCode_length]; exact hc)
  generalize psCode[c] = ins at hi
  unfold psChk at hck
  rw [hi] at hck
  cases ins with
  | pk e a b => exact seg_ps_pk hi hck hc
  | ad e a b => exact seg_ps_ad hi hck hc

/-- **The first `m` instructions of the packs and the sum tree.** -/
theorem seg_psN {d : D} {recv : Value} : ∀ m, m ≤ 63 →
    Seg kernel asms L g m 2169
      (factsFrom (Flow.live 2169) (valueEx (valueOf L g d) (base4 d recv))) (2169 + m)
      (factsFrom (Flow.live (2169 + m))
        (valueEx (valueOf L g d) (psEx d (eOf recv) m ++ base4 d recv))) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => (ih (by omega)).comp (seg_ps1 (d := d) (recv := recv) (c := m) (by omega))

/-! ### The unpack and the last sum (pcs 2232 and 2233) -/

/-- `add.f32 d, a, b` (no rounding modifier). -/
abbrev addOp (d a b : Nat) : Op :=
  .float { op := .add, ty := ty1 .f32, dsts := [some d], srcs := [.reg a, .reg b] }

theorem exec_addEE {t : TState} {d a b : Nat} {x y : ℝ}
    (hI : IdealAt asms (.add .f32) L g t) (ha : t.regs a = some (.float .f32 x))
    (hb : t.regs b = some (.float .f32 y)) :
    execLocalA asms L g t (addOp d a b) =
      .ok (PTX.next (setReg t d (.float .f32 (x + y)))) := by
  have hop : FloatForm.ofOp (addOp d a b) = some (.add .f32) := by simp [FloatForm.ofOp]
  have hx := readEReal_of_valFloat (valFloat_float x)
  have hy := readEReal_of_valFloat (valFloat_float y)
  have hex : execIdealFloat L g t (addOp d a b) =
      some (.ok (PTX.next (setReg t d (.float .f32 (x + y))))) := by
    simp only [execIdealFloat, readERealOpnd_reg ha, readERealOpnd_reg hb, hx, hy, bindRead,
      addEReal_coe, erealValue_coe, Option.map_some, pure, Except.pure]
  rw [hI _ hop _ hex]

/-- The root pair's two masks. -/
def rootM : Nat × Nat := lkp (psSt 63) (1948 + 397)

/-- The overlay after the unpack of the root pair. -/
abbrev xt1 (d : D) (recv : Value) : List (Nat × Value) :=
  (1528, Value.float .f32 (d.smask (eOf recv) rootM.2)) ::
    (1527, Value.float .f32 (d.smask (eOf recv) rootM.1)) :: (psEx d (eOf recv) 63 ++ base4 d recv)

/-- The overlay after the last sum. -/
abbrev xt2 (d : D) (recv : Value) : List (Nat × Value) :=
  (1529, Value.float .f32 (d.smask (eOf recv) rootM.1 + d.smask (eOf recv) rootM.2)) :: xt1 d recv

theorem live_tail : (2345 ∈ Flow.live 2232) ∧
    subX (Flow.live 2233) (Flow.live 2232) [1527, 1528] = true ∧
    (1527 ∈ Flow.live 2233) ∧ (1528 ∈ Flow.live 2233) ∧
    subX (Flow.live 2234) (Flow.live 2233) [1529] = true ∧
    Assumptions.emuSites.contains 2232 = false ∧ Assumptions.emuSites.contains 2233 = false ∧
    (psSt 63).lookup 2345 = some rootM := by
  decide +kernel

theorem seg_t1 {d : D} {recv : Value} :
    Seg kernel asms L g 1 2232
      (factsFrom (Flow.live 2232) (valueEx (valueOf L g d) (psEx d (eOf recv) 63 ++ base4 d recv)))
      2233 (factsFrom (Flow.live 2233) (valueEx (valueOf L g d) (xt1 d recv))) := by
  obtain ⟨l1, l2, -, -, -, e1, -, hr⟩ := live_tail
  refine Seg.set2 (K := kernel) Flow.code_2232 rfl (by decide) (fun t h => ?_) (subX_cov2 l2)
  have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree e1
  have ra : t.regs 2345 = some (.pair (.float .f32 (d.smask (eOf recv) rootM.1))
      (.float .f32 (d.smask (eOf recv) rootM.2))) :=
    reg_of h.2.2.2.2 l1 (valueEx_ps_in _ _ hr)
  exact exec_unpack hS ra rfl rfl

theorem seg_t2 {d : D} {recv : Value} :
    Seg kernel asms L g 1 2233
      (factsFrom (Flow.live 2233) (valueEx (valueOf L g d) (xt1 d recv))) 2234
      (factsFrom (Flow.live 2234) (valueEx (valueOf L g d) (xt2 d recv))) := by
  obtain ⟨-, -, l1, l2, l3, -, e2, -⟩ := live_tail
  refine Seg.set1 (K := kernel) Flow.code_2233 rfl (fun t h => ?_) (subX_sound l3)
  have hE : Assumptions.emuSites.contains t.pc = false := by rw [h.1]; exact e2
  have ra : t.regs 1527 = some (.float .f32 (d.smask (eOf recv) rootM.1)) :=
    reg_of h.2.2.2.2 l1 (by simp [valueEx, List.lookup])
  have rb : t.regs 1528 = some (.float .f32 (d.smask (eOf recv) rootM.2)) :=
    reg_of h.2.2.2.2 l2 (by simp [valueEx, List.lookup])
  show execLocalA asms L g t (addOp 1529 1527 1528) = _
  rw [exec_addEE (idealAtSc (L := L) (g := g) (by decide) hE) ra rb]

/-! ### From the overlay to the table of the state after the shuffle -/

theorem keys_X (d : D) : ∀ r ∈ (valuesX L g d).map Prod.fst, XKey r := by
  intro r hm
  simp only [valuesX, List.map_append, List.mem_append] at hm
  rcases hm with hm | hm | hm
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
    unfold XKey; omega
  · simp only [valuesXt, List.map_append, List.map_map, List.mem_append, List.mem_map,
      List.mem_range, Function.comp_apply] at hm
    rcases hm with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
      unfold XKey <;> omega
  · have := keys_Xs _ _ _ r hm
    unfold XKey; omega

/-- A register that is no register of the table's last section has the same value in two states
that agree on everything but the last section's inputs. -/
theorem valueOf_nonX {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) {r : Nat} (hr : ¬ XKey r)
    (hb : d'.stg.bw = d.stg.bw := by rfl):
    valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hb]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hb]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  have nX : ∀ x : D, (valuesX L g x).lookup r = none := fun x =>
    lookup_none_of_not_mem _ (fun hm => hr (keys_X x r hm))
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, nX]

/-- The probability of a score word: `pow2` of its exponent. -/
theorem pk_eq {d : D} {rE : EReal} (hr : (0 : ℝ) < slOf d.e) {k : Nat}
    (hw : ScoreWord (d.stg.fsv k).1) :
    d.pk rE k = pOfV (slOf d.e) (d.mUse rE) (d.stg.fsv k).1 := by
  rcases hw with ⟨x, hx⟩ | hx
  · have hxE : d.xE rE k = ((x * slOf d.e + d.mUse rE * -(slOf d.e) : ℝ) : EReal) := by
      unfold D.xE
      rw [hx]
      simp only [eOf]
      push_cast
      rfl
    unfold D.pk
    rw [hxE, hx]
    unfold Softmax.pow2
    rw [if_neg (EReal.coe_ne_bot _), EReal.toReal_coe]
    rfl
  · have hxE : d.xE rE k = ⊥ := by
      unfold D.xE
      rw [hx]
      have : eOf infB = ⊥ := rfl
      rw [this, EReal.bot_mul_coe_of_pos hr, EReal.bot_add]
    unfold D.pk
    rw [hxE, hx]
    simp [pOfV, Softmax.pow2]
    rfl

/-- **The stretch from the shuffle of the row maximum to the shuffle of the half sums**
(pcs 1839 to 2233): from the facts after the first shuffle (`%r1060` holds what it received,
`xa0`) to the facts before the second, in terms of the overlay of the written registers. -/
theorem seg_stageB {d : D} {recv : Value} (hA : StA d recv) :
    Seg kernel asms L g 235 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) 2234
      (factsFrom (Flow.live 2234) (valueEx (valueOf L g d) (xt2 d recv))) := by
  have h1 := seg_a (L := L) (g := g) (d := d) (recv := recv) hA
  have h2 := seg_fmaXs (L := L) (g := g) hA 64 (le_refl _)
  have h3 := seg_emuN (L := L) (g := g) hA 16 (le_refl _)
  have h4 := seg_ex2N (L := L) (g := g) hA 64 (le_refl _)
  have h5 := seg_selpN (L := L) (g := g) hA 16 (le_refl _)
  have h6 := seg_psN (L := L) (g := g) (d := d) (recv := recv) 63 (le_refl _)
  have h7 := seg_t1 (L := L) (g := g) (d := d) (recv := recv)
  have h8 := seg_t2 (L := L) (g := g) (d := d) (recv := recv)
  exact Seg.of_len (((((((h1.comp h2).comp h3).comp h4).comp h5).comp h6).comp h7).comp h8) rfl

/-! ### The registers of the overlay -/

/-- The registers of the packs and the sum tree. -/
def psKey (r : Nat) : Prop := (1994 ≤ r ∧ r < 2018) ∨ (2307 ≤ r ∧ r < 2346)

instance : DecidablePred psKey := fun r => by unfold psKey; infer_instance
instance : DecidablePred XKey := fun r => by unfold XKey; infer_instance

theorem psSt_keys' : ∀ c ≤ 63, ∀ k ∈ (psSt c).map Prod.fst, psKey k := by decide +kernel

theorem valueEx_ps_free {d : D} {rE : EReal} {c r : Nat} (B : Nat → Value)
    (ex : List (Nat × Value)) (hc : c ≤ 63) (hr : ¬ psKey r) :
    valueEx B (psEx d rE c ++ ex) r = valueEx B ex r := by
  unfold valueEx
  rw [lookup_append_none]
  intro hm
  simp only [psEx, List.map_map, Function.comp_def, List.mem_map] at hm
  obtain ⟨q, hq, hqr⟩ := hm
  exact hr (psSt_keys' c hc r (List.mem_map.mpr ⟨q, hq, hqr⟩))

/-- The registers the stretch writes and the table does not hold unchanged. -/
def ovFree (r : Nat) : Prop :=
  ¬ psKey r ∧ ¬ (1269 ≤ r ∧ r < 1415) ∧ ¬ (1521 ≤ r ∧ r < 1530) ∧ ¬ (508 ≤ r ∧ r < 524) ∧
    r ≠ 507 ∧ r ≠ 167 ∧ r ≠ 168

instance : DecidablePred ovFree := fun r => by unfold ovFree; infer_instance

theorem live_2234_cases : ∀ r ∈ Flow.live 2234, (ovFree r ∧ (¬ XKey r ∨ r = 506)) ∨ r = 1529 ∨
    (1994 ≤ r ∧ r < 2018) ∨ (508 ≤ r ∧ r < 524) ∨ r = 507 ∨ r = 1522 ∨ r = 168 := by
  decide +kernel

theorem valueEx_xt2_free (d : D) (recv : Value) (B : Nat → Value) {r : Nat} (h : ovFree r) :
    valueEx B (xt2 d recv) r = B r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have e1 : r ≠ 1529 := by omega
  have e2 : r ≠ 1528 := by omega
  have e3 : r ≠ 1527 := by omega
  simp only [xt2, xt1, base4, base3, base2]
  rw [valueEx_cons_ne _ _ e1, valueEx_cons_ne _ _ e2, valueEx_cons_ne _ _ e3,
    valueEx_ps_free _ _ (le_refl _) h1,
    valueEx_sl16_off d _ _ _ 16 (fun k hk => by omega),
    valueEx_e2_off d _ _ _ 64 (fun k hk => by omega),
    valueEx_em_off d _ _ _ 16 (fun k hk => by omega),
    valueEx_fx_off d _ _ _ 64 (fun k hk => by omega),
    valueEx_xa10_off d recv _ (by omega)]

theorem valueOf_r1070 (d : D) : valueOf L g d 1529 = d.stg.sw := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem valueOf_r45 (d : D) : valueOf L g d 506 = b32 (r45 d.stg.bw) := by
  rw [valueOf_X d (by unfold XKey; omega)]
  simp [valuesX, List.lookup]

theorem ps_lk : ∀ q < 24, (psSt 63).lookup (1994 + q) =
    some (2 ^ (2 * pairW q), 2 ^ (2 * pairW q + 1)) := by decide +kernel

theorem pairW_lt : ∀ q < 24, 2 * pairW q + 1 < 64 := by decide +kernel

theorem valueEx_xt2_xa10 (d : D) (recv : Value) (B : Nat → Value) {r : Nat}
    (h1 : ¬ psKey r) (h2 : ¬ (508 ≤ r ∧ r < 524)) (h3 : ¬ (1269 ≤ r ∧ r < 1415))
    (h4 : ¬ (1527 ≤ r ∧ r < 1530)) : valueEx B (xt2 d recv) r = valueEx B (xa10 d recv) r := by
  simp only [xt2, xt1, base4, base3, base2]
  rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
    valueEx_cons_ne _ _ (by omega), valueEx_ps_free _ _ (le_refl _) h1,
    valueEx_sl16_off d _ _ _ 16 (fun k hk => by omega),
    valueEx_e2_off d _ _ _ 64 (fun k hk => by omega),
    valueEx_em_off d _ _ _ 16 (fun k hk => by omega),
    valueEx_fx_off d _ _ _ 64 (fun k hk => by omega)]

theorem afterMax_pf {d : D} {recv : Value} (hA : StA d recv) {k : Nat} (hk : k < 64) :
    (d.afterMax recv).pf k = d.pk (eOf recv) k :=
  (pk_eq (sl_pos hA.ok) (hA.w k hk)).symm

theorem sumP_eq {d : D} {recv : Value} (hA : StA d recv) :
    (d.afterMax recv).sumP = d.smask (eOf recv) rootM.1 + d.smask (eOf recv) rootM.2 := by
  obtain ⟨-, hdis, hor⟩ := ps_root
  have hdis' : rootM.1 &&& rootM.2 = 0 := hdis
  have hor' : rootM.1 ||| rootM.2 = 2 ^ 64 - 1 := hor
  have h1 : d.smask (eOf recv) rootM.1 + d.smask (eOf recv) rootM.2 =
      d.smask (eOf recv) (2 ^ 64 - 1) := by
    rw [← smask_or d _ hdis', hor']
  rw [h1, smask_full]
  unfold D.sumP
  congr 1
  refine List.map_congr_left fun k hk => ?_
  exact afterMax_pf hA (List.mem_range.mp hk)

theorem ovB_eq {d : D} {recv : Value} (hA : StA d recv) :
    ∀ r ∈ Flow.live 2234, valueEx (valueOf L g d) (xt2 d recv) r =
      valueOf L g (d.afterMax recv) r := by
  intro r hr
  rcases live_2234_cases r hr with ⟨hf, hx⟩ | h1532 | ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩ | h508 | h1525 | h168
  · rw [valueEx_xt2_free d recv _ hf]
    rcases hx with hx | rfl
    · exact (valueOf_nonX (L := L) (g := g) (d := d) (d' := d.afterMax recv) rfl rfl rfl rfl rfl
        rfl hx).symm
    · rw [valueOf_r45, valueOf_r45]
      simp only [D.afterMax]
  · subst h1532
    rw [valueOf_r1070]
    show _ = Value.float .f32 (d.afterMax recv).sumP
    rw [sumP_eq hA]
    simp [valueEx, List.lookup]
  · obtain ⟨q, rfl⟩ : ∃ q, r = 1994 + q := ⟨r - 1994, by omega⟩
    have hq : q < 24 := by omega
    have e1 : valueEx (valueOf L g d) (xt2 d recv) (1994 + q) =
        d.pv (eOf recv) (2 ^ (2 * pairW q), 2 ^ (2 * pairW q + 1)) := by
      simp only [xt2, xt1]
      rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
        valueEx_cons_ne _ _ (by omega)]
      exact valueEx_ps_in _ _ (ps_lk q hq)
    rw [e1, valueOf_rd _ hq]
    show _ = joinValue (Value.float .f32 ((d.afterMax recv).pf (2 * pairW q)))
      (Value.float .f32 ((d.afterMax recv).pf (2 * pairW q + 1)))
    rw [D.pv, smask_pow d _ (by have := pairW_lt q hq; omega),
      smask_pow d _ (pairW_lt q hq), afterMax_pf hA (by have := pairW_lt q hq; omega),
      afterMax_pf hA (pairW_lt q hq)]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, r = 508 + k := ⟨r - 508, by omega⟩
    have hk : k < 16 := by omega
    have e1 : valueEx (valueOf L g d) (xt2 d recv) (508 + k) =
        Value.float .f32 (Softmax.pow2 (d.xE (eOf recv) (colR k))) := by
      simp only [xt2, xt1, base4]
      rw [valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
        valueEx_cons_ne _ _ (by omega), valueEx_ps_free _ _ (le_refl _) (by unfold psKey; omega)]
      exact valueEx_sl16_in d _ _ _ hk
    rw [e1, valueOf_rP _ hk]
    show _ = Value.float .f32 ((d.afterMax recv).pf (colR k))
    rw [afterMax_pf hA (colR_lt k hk)]
    rfl
  · subst h508
    rw [valueEx_xt2_xa10 d recv _ (by unfold psKey; omega) (by omega) (by omega) (by omega)]
    have : valueOf L g (d.afterMax recv) 507 = (d.afterMax recv).stg.al := valueOf_r46 _
    rw [this]
    simp only [D.afterMax, D.alV]
    rw [← hA.aE_eq]
    simp [valueEx, List.lookup]
  · subst h1525
    rw [valueEx_xt2_xa10 d recv _ (by unfold psKey; omega) (by omega) (by omega) (by omega)]
    have : valueOf L g (d.afterMax recv) 1522 = (d.afterMax recv).stg.mn := valueOf_r1063 _
    rw [this]
    simp [D.afterMax, valueEx, List.lookup]
  · subst h168
    rw [valueEx_xt2_xa10 d recv _ (by unfold psKey; omega) (by omega) (by omega) (by omega)]
    have : valueOf L g (d.afterMax recv) 168 = .pred (d.afterMax recv).stg.kp := valueOf_p168 _
    rw [this]
    simp only [D.afterMax, D.keepB]
    rw [← hA.aE_eq]
    simp [valueEx, List.lookup]

/-! ### The step of the row maximum's shuffle -/

/-- The value of an extended real other than `+inf` is a score word. -/
theorem scoreWord_erealValue {E : EReal} (h : E ≠ ⊤) : ScoreWord (erealValue .f32 E) := by
  induction E using EReal.rec with
  | bot => exact Or.inr erealValue_bot'
  | coe y => exact Or.inl ⟨y, erealValue_coe .f32 y⟩
  | top => exact absurd rfl h

/-- The invariant does not mention the stage's numbers. -/
theorem inv_stg_al {d : D} (hi : Inv L g d) (s : Stg) (pf : Nat → ℝ)
    (hal : s.re = true → RealSt s d.m pf) (h4 : s.Four)
    (hb : s.bw = d.stg.bw := by rfl) :
    Inv L g { d with stg := s, pf := pf } :=
  ⟨hi.tid, hi.ok, hi.i, hi.cwPre, hi.cwNxt, hi.loop, hi.wb, hi.vb, hi.start, hi.late, hi.lead,
    hal, hi.lb, h4, by show s.bw = 0 ∨ s.bw = g % L.block / 32; rw [hb]; exact hi.bw,
    hi.wf, hi.vf⟩

/-- The invariant does not mention the stage's numbers other than `alpha` and the four-byte
words: where the new numbers keep `alpha` and its real value and have four-byte words, it
holds. -/
theorem inv_stg {d : D} (hi : Inv L g d) (s : Stg) (pf : Nat → ℝ) (h4 : s.Four)
    (ha : s.al = d.stg.al := by rfl) (har : s.alr = d.stg.alr := by rfl)
    (hb : s.bw = d.stg.bw := by rfl) (hmn : s.mn = d.stg.mn := by rfl)
    (hpv : s.pv = d.stg.pv := by rfl) (hsw : s.sw = d.stg.sw := by rfl)
    (hre : s.re = d.stg.re := by rfl) (hpf : pf = d.pf := by rfl) :
    Inv L g { d with stg := s, pf := pf } :=
  inv_stg_al hi s pf (fun hr => by
    have R := hi.re (hre ▸ hr)
    exact ⟨by rw [ha, har]; exact R.al, R.m, by rw [hmn]; exact R.mn,
      by rw [hpv, hpf]; exact R.pv, by rw [hsw, hpf]; exact R.sw⟩) h4 hb

theorem live_1839_1838 : ∀ r ∈ Flow.live 1839, r = 1521 ∨ r ∈ Flow.live 1838 := by
  decide +kernel

theorem holds_xa0 {d : D} {recv : Value} {R : Nat → Option Value}
    (h : Holds R ((1521, recv) :: factsAt L g 1838 d)) :
    Holds R (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) := by
  refine holds_of_pointwise fun r hr => ?_
  rcases live_1839_1838 r hr with rfl | hl
  · have := holds_mem h (List.mem_cons_self ..)
    simpa [valueEx, List.lookup] using this
  · have hne : r ≠ 1521 := by
      intro he
      subst he
      exact absurd hl (by decide +kernel)
    have := holds_mem h (List.mem_cons_of_mem _ (Flow.mem_factsFrom (val := valueOf L g d) hl))
    simpa [valueEx, List.lookup, beq_false_of_ne hne] using this

/-- `alpha`'s register reads as the number the stage records for it. -/
theorem readEReal_alV (d : D) (rE : EReal) :
    readEReal .f32 (d.alV rE) = some (.ok ((d.alR rE : ℝ) : EReal)) := by
  unfold D.alV D.alR
  split_ifs
  · exact readEReal_of_valFloat valFloat_one
  · exact readEReal_of_valFloat (valFloat_float _)

/-- **The shuffle of the row maximum on score words** (pc 1838): where the running maximum, the
received maximum and the 64 words are score words, the thread runs to the shuffle of the half
sums (pc 2234) and the registers are the table of the state `D.afterMax`. The other words are
followed by `SmTotG.step_shfl5`. -/
theorem step_shfl5R (hi : Inv L g d) (hs : d.site = .shfl5) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u))
    (hR : ∀ av bv cv recv ok, e = ⟨Flow.shfl_5, .shfl .bfly av bv cv recv ok⟩ →
      ScoreWord d.m ∧ ScoreWord recv ∧ ∀ k < 64, ScoreWord (d.stg.fsv k).1) :
    Step L g d e u := by
  have hpc : d.site.pc = 1838 := by rw [hs]; rfl
  have hc' : kernel.code[1838]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_shfl_5)
  have h' : At t 1838 (factsAt L g 1838 d) := hpc ▸ h
  have hf' := hpc ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf'
  simp only [Option.elim] at hu
  subst hu
  have hlate : LateSite d.site := by rw [hs]; trivial
  have hck := hR av bv cv recv ok rfl
  · have hA : StA d recv := ⟨hck.1, hck.2.1, hck.2.2, hi.ok⟩
    have hn : next L g d ⟨Flow.shfl_5, .shfl .bfly av bv cv recv ok⟩ =
        some (some (d.afterMax recv)) := by
      simp only [next, hs]
      rw [if_pos (show d.RealIn recv from hck)]
    have h1 := At.set (r := 1521) (v := recv) h' (facts_ne (by decide +kernel))
    have h1' : At (PTX.next (setReg t 1521 recv)) 1839
        (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) :=
      h1.mono (holds_xa0 h1.2.2.2.2)
    obtain ⟨t', hr, ht'⟩ := (seg_stageB (L := L) (g := g) hA).rtg h1'
    have hat : At t' (d.afterMax recv).site.pc (facts L g (d.afterMax recv)) :=
      ht'.mono (holds_of_pointwise fun r hr' => by
        rw [holds_mem ht'.2.2.2.2 (Flow.mem_factsFrom (val := valueEx (valueOf L g d)
          (xt2 d recv)) hr')]
        exact congrArg some (ovB_eq hA r hr'))
    exact .inl (.inr ⟨d.afterMax recv, t', hn, hr, hat,
      inv_stg_al (inv_late hi hlate (s := .shfl6) trivial (fun h => absurd h (by simp))) _ _
        (fun _ => ⟨readEReal_alV d (eOf recv), hA.m, scoreWord_erealValue hA.E_ne_top,
          fun _ => rfl, rfl⟩)
          (by exact ⟨readEReal_alV d (eOf recv), hi.four.cm1, hi.four.cm2,
            hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, rfl⟩)⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
