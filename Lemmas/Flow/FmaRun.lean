-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FloatRun

@[expose] public section

/-! # Runs of packed products by fixed pairs

A proof tool, for code that computes `a · c + z` elementwise for many packed pairs `a` with the
same pairs `c` and `z` (`fma.rn.f32x2 q, a, c, z`), as a softmax computes the exponent arguments
`s · scale - scale · max`. Each item is the product, optionally after the pack of its source
pair (`mov.b64 a, {lo, hi}`), followed by the unpack of the product (`mov.b64 {x, y}, q`).
`Seg.fmas` takes the whole run as one piece, under the ideal reading of `fma.rn.f32x2`: when
the elements of each source pair, of `c` and of `z` read as numbers, each item writes its
product pair and the two products. Evaluation could not take these steps when `c` holds the
bits of a parameter, whose number is not computable. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- One product of a run: the optional pack `a ← {lo, hi}`, then `q ← a · c + z` and the unpack
`{x, y} ← q`. -/
structure FmaItem where
  pk : Option (Nat × Nat)
  a : Nat
  q : Nat
  x : Nat
  y : Nat
  deriving DecidableEq

namespace FmaItem

/-- The number of instructions. -/
def len (it : FmaItem) : Nat := if it.pk.isSome then 3 else 2

/-- The registers the item writes. -/
def writes (it : FmaItem) : List Nat :=
  (match it.pk with | some _ => [it.a] | none => []) ++ [it.q, it.x, it.y]

/-- The registers the item reads besides `c` and `z`. -/
def reads (it : FmaItem) : List Nat :=
  match it.pk with
  | some (lo, hi) => [lo, hi]
  | none => [it.a]

/-- The source pair, from the values `v` of the registers it reads. -/
def src (v : Nat → Value) (it : FmaItem) : Value :=
  match it.pk with
  | some (lo, hi) => joinValue (v lo) (v hi)
  | none => v it.a

/-- The pack's sources have four bytes. -/
def packOk (v : Nat → Value) (it : FmaItem) : Bool :=
  match it.pk with
  | some (lo, hi) => (v lo).bytes == 4 && (v hi).bytes == 4
  | none => true

/-- The product pair of source elements `p` with `c = (c0, c1)` and `z = (z0, z1)`. -/
def prod (cz : ℝ × ℝ × ℝ × ℝ) (p : ℝ × ℝ) : Value :=
  .pair (.float .f32 (p.1 * cz.1 + cz.2.2.1)) (.float .f32 (p.2 * cz.2.1 + cz.2.2.2))

/-- The registers the item writes with their values, the unpacked products first. -/
def vals (v : Nat → Value) (cz : ℝ × ℝ × ℝ × ℝ) (it : FmaItem) (p : ℝ × ℝ) :
    List (Nat × Value) :=
  [(it.x, .float .f32 (p.1 * cz.1 + cz.2.2.1)), (it.y, .float .f32 (p.2 * cz.2.1 + cz.2.2.2)),
    (it.q, prod cz p)] ++ (match it.pk with | some _ => [(it.a, it.src v)] | none => [])

/-- The item's instructions are at `pc`. -/
def codeB (K : Kernel) (c z pc : Nat) (it : FmaItem) : Bool :=
  (match it.pk with
    | some (lo, hi) => match K.code[pc]? with
      | some ⟨none, .move ⟨.pack, .int .b 64, [some d], [.reg a, .reg b]⟩⟩ =>
        d == it.a && a == lo && b == hi
      | _ => false
    | none => true) &&
  (match K.code[pc + (it.len - 2)]? with
    | some ⟨none, .float
        ⟨.fma, ⟨.f32, 2⟩, [], none, some .rn, .ieee, false, false, false, false, false,
          false, false, [some d], [.reg a, .reg b, .reg e]⟩⟩ =>
      d == it.q && a == it.a && b == c && e == z
    | _ => false) &&
  (match K.code[pc + (it.len - 1)]? with
    | some ⟨none, .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩⟩ =>
      lo == it.x && hi == it.y && a == it.q
    | _ => false)

end FmaItem

/-- The items' instructions follow each other from `pc`. -/
def fmaCodeB (K : Kernel) (c z : Nat) : Nat → List FmaItem → Bool
  | _, [] => true
  | pc, it :: its => it.codeB K c z pc && fmaCodeB K c z (pc + it.len) its

/-- The number of instructions of the items. -/
def fmaLen : List FmaItem → Nat
  | [] => 0
  | it :: its => it.len + fmaLen its

/-- The written registers with their values. -/
def fmaVals (v : Nat → Value) (cz : ℝ × ℝ × ℝ × ℝ) : List FmaItem → List (ℝ × ℝ) →
    List (Nat × Value)
  | it :: its, p :: ps => it.vals v cz p ++ fmaVals v cz its ps
  | _, _ => []

variable {K : Kernel} {L : Launch} {g : Nat}

/-- `fma.rn.f32x2 d, a, b, e`: the elementwise product-sum of the pairs `a · b + e`. -/
def fma2Op (d a b e : Nat) : Op :=
  .float { op := .fma, ty := ⟨.f32, 2⟩, rnd := some .rn, dsts := [some d],
           srcs := [.reg a, .reg b, .reg e] }

/-- No assumption of `A` names the unpack of a packed pair into two 32-bit halves. -/
def NoUnpack64 (A : List Assumption) : Prop :=
  ∀ (lo hi src : Nat) (L : Launch) (g : Nat) (t : TState), ∀ a ∈ A,
    a.localRule L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg src]⟩) = none

/-- A head ideal-real assumption names no pack form: the packs of `A'` are still no pack. -/
theorem noPack_idealReal {name why : String} {s : IdealScope} {A' : List Assumption}
    (h : NoPack A') : NoPack (idealReal name s why :: A') := by
  intro d a b L g t a' ha'
  rcases List.mem_cons.mp ha' with rfl | ha'
  · exact idealReal_localRule_none (fun f hf => by simp [FloatForm.ofOp] at hf)
  · exact h d a b L g t a' ha'

/-- A head ideal-real assumption names no unpack form: the unpacks of `A'` are still no unpack. -/
theorem noUnpack64_idealReal {name why : String} {s : IdealScope} {A' : List Assumption}
    (h : NoUnpack64 A') : NoUnpack64 (idealReal name s why :: A') := by
  intro lo hi src L g t a' ha'
  rcases List.mem_cons.mp ha' with rfl | ha'
  · exact idealReal_localRule_none (fun f hf => by simp [FloatForm.ofOp] at hf)
  · exact h lo hi src L g t a' ha'

/-- The two single-precision numbers of a packed pair, low half first (§9.7.3); the first half that
is not a number stops the reading. -/
def f32x2Elems (v : Value) : Exec (ℝ × ℝ) :=
  match valFloat .f32 (splitValue 64 v).1, valFloat .f32 (splitValue 64 v).2 with
  | .ok x0, .ok x1 => .ok (x0, x1)
  | .error f, _ => .error f
  | .ok _, .error f => .error f

theorem f32x2Elems_read {v : Value} {q : ℝ × ℝ} (h : f32x2Elems v = .ok q) :
    valFloat .f32 (splitValue 64 v).1 = .ok q.1 ∧
      valFloat .f32 (splitValue 64 v).2 = .ok q.2 := by
  cases h0 : valFloat .f32 (splitValue 64 v).1 with
  | error f => simp [f32x2Elems, h0] at h
  | ok x0 =>
    cases h1 : valFloat .f32 (splitValue 64 v).2 with
    | error f => simp [f32x2Elems, h0, h1] at h
    | ok x1 =>
      simp only [f32x2Elems, h0, h1, Except.ok.injEq] at h
      obtain rfl : q = (x0, x1) := h.symm
      simp

/-! ### The steps of an item -/

theorem exec_unpack64 {A : List Assumption} {t : TState} {lo hi a : Nat} {x y : Value}
    (h : t.regs a = some (.pair x y)) (hx : x.bytes = 4) (hy : y.bytes = 4)
    (hS : SegFreePc A t.pc) (hN : NoUnpack64 A) :
    execLocalA A L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩) =
      .ok (PTX.next (setReg (setReg t lo x) hi y)) := by
  simp [hS.exec, execLocalRule_of_none (hN lo hi a L g t), execLocal, Op.rule, MoveInstr.rule,
    DType.width, execMove, readValue, readReg, h, Value.bytes, splitValue, hx, hy, bind,
    Except.bind, pure, Except.pure]

/-- **The ideal step of a packed product sum**: with all six elements as single-precision numbers,
the local step is their elementwise product and sum. -/
theorem exec_fma2 {name why : String} {s : IdealScope} {A' : List Assumption} {t : TState}
    {d a b e : Nat} {va vb ve : Value} {x0 x1 y0 y1 z0 z1 : ℝ}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hS : SegFreePc A' t.pc)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (he : t.regs e = some ve)
    (hxa : f32x2Elems va = .ok (x0, x1)) (hxb : f32x2Elems vb = .ok (y0, y1))
    (hxe : f32x2Elems ve = .ok (z0, z1)) :
    execLocalA (idealReal name s why :: A') L g t (fma2Op d a b e) =
      .ok (PTX.next (setReg t d (.pair (.float .f32 (x0 * y0 + z0))
        (.float .f32 (x1 * y1 + z1))))) := by
  obtain ⟨hxa0, hxa1⟩ := f32x2Elems_read hxa
  obtain ⟨hxb0, hxb1⟩ := f32x2Elems_read hxb
  obtain ⟨hxe0, hxe1⟩ := f32x2Elems_read hxe
  have hra := readERealPair_reg (L := L) (g := g) ha hxa0 hxa1
  have hrb := readERealPair_reg (L := L) (g := g) hb hxb0 hxb1
  have hrz := readERealPair_reg (L := L) (g := g) he hxe0 hxe1
  have hm0 : Assumption.mulEReal (x0 : EReal) (y0 : EReal) = some ((x0 * y0 : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hm1 : Assumption.mulEReal (x1 : EReal) (y1 : EReal) = some ((x1 * y1 : ℝ) : EReal) := by
    rw [Assumption.mulEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have ha0 : Assumption.addEReal ((x0 * y0 : ℝ) : EReal) (z0 : EReal) =
      some ((x0 * y0 + z0 : ℝ) : EReal) := by
    rw [Assumption.addEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have ha1 : Assumption.addEReal ((x1 * y1 : ℝ) : EReal) (z1 : EReal) =
      some ((x1 * y1 + z1 : ℝ) : EReal) := by
    rw [Assumption.addEReal, ite_eq_right (by simp)]
    push_cast
    ring
  have hf0 : (Assumption.mulEReal (x0 : EReal) (y0 : EReal)).bind
      (fun p => Assumption.addEReal p (z0 : EReal)) = some ((x0 * y0 + z0 : ℝ) : EReal) := by
    rw [hm0]
    exact ha0
  have hf1 : (Assumption.mulEReal (x1 : EReal) (y1 : EReal)).bind
      (fun p => Assumption.addEReal p (z1 : EReal)) = some ((x1 * y1 + z1 : ℝ) : EReal) := by
    rw [hm1]
    exact ha1
  have hv0 : Assumption.erealValue .f32 ((x0 * y0 + z0 : ℝ) : EReal) =
      .float .f32 (x0 * y0 + z0) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x0 * y0 + z0)),
      ite_eq_right (EReal.coe_ne_bot (x0 * y0 + z0))]
    rfl
  have hv1 : Assumption.erealValue .f32 ((x1 * y1 + z1 : ℝ) : EReal) =
      .float .f32 (x1 * y1 + z1) := by
    unfold Assumption.erealValue
    rw [ite_eq_right (EReal.coe_ne_top (x1 * y1 + z1)),
      ite_eq_right (EReal.coe_ne_bot (x1 * y1 + z1))]
    rfl
  have hex : Assumption.execIdealFloat L g t (fma2Op d a b e) = some (.ok (PTX.next (setReg t d
      (.pair (Assumption.erealValue .f32 ((x0 * y0 + z0 : ℝ) : EReal))
        (Assumption.erealValue .f32 ((x1 * y1 + z1 : ℝ) : EReal)))))) := by
    simp only [fma2Op, Assumption.execIdealFloat, hra, hrb, hrz, Assumption.bindRead, hf0, hf1,
      pure, Except.pure]
  rw [execLocalA_idealReal (f := .fmaRnF32x2) (by simp [fma2Op, FloatForm.ofOp]) hs hS hex, hv0,
    hv1]

/-- One local step from `t` to `t1`. -/
theorem run_step {A : List Assumption} {t t1 : TState} {op : Op} {n : Nat}
    (hc : K.code[t.pc]? = some ⟨none, op⟩) (hl : op.isLocal = true) (hf : t.fault = none)
    (he : execLocalA A L g t op = .ok t1) : run K A L g (n + 1) t = run K A L g n t1 := by
  simp only [run, tauStep, out, hf, hc, guardHolds, hl, ↓reduceIte, he]
  rfl

theorem FmaItem.code_of {c z pc : Nat} {it : FmaItem} (h : it.codeB K c z pc = true) :
    (∀ lo hi, it.pk = some (lo, hi) →
      K.code[pc]? = some ⟨none, .move ⟨.pack, .int .b 64, [some it.a], [.reg lo, .reg hi]⟩⟩) ∧
    K.code[pc + (it.len - 2)]? = some ⟨none, fma2Op it.q it.a c z⟩ ∧
    K.code[pc + (it.len - 1)]? =
      some ⟨none, .move ⟨.unpack, .int .b 64, [some it.x, some it.y], [.reg it.q]⟩⟩ := by
  simp only [FmaItem.codeB, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun lo hi hp => ?_, ?_, ?_⟩
  · rw [hp] at h1
    simp only at h1
    split at h1
    · rename_i d a b hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      rw [hc, h1.1.1, h1.1.2, h1.2]
    · cases h1
  · split at h2
    · rename_i d a b e hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      rw [hc, h2.1.1.1, h2.1.1.2, h2.1.2, h2.2, fma2Op]
    · cases h2
  · split at h3
    · rename_i lo hi a hc
      simp only [Bool.and_eq_true, beq_iff_eq] at h3
      rw [hc, h3.1.1, h3.1.2, h3.2]
    · cases h3

theorem segFree_ideal {name why : String} {s : IdealScope} {A' : List Assumption} {pc : Nat}
    (h : SegFreePc A' pc) : SegFreePc (idealReal name s why :: A') pc :=
  SegFreePc.cons (fun _ _ _ _ => rfl) h

theorem pair_bytes (x y : ℝ) :
    (Value.float .f32 x).bytes = 4 ∧ (Value.float .f32 y).bytes = 4 :=
  ⟨rfl, rfl⟩

/-- The product and the unpack of an item, from the state after its pack (if any). -/
theorem fma_tail {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hu : NoUnpack64 (idealReal name s why :: A'))
    {c z q x y a : Nat} {t : TState} {va vc vz : Value}
    {cz : ℝ × ℝ × ℝ × ℝ} {p : ℝ × ℝ}
    (h1 : K.code[t.pc]? = some ⟨none, fma2Op q a c z⟩)
    (h2 : K.code[t.pc + 1]? =
      some ⟨none, .move ⟨.unpack, .int .b 64, [some x, some y], [.reg q]⟩⟩) (hf : t.fault = none)
    (ha : t.regs a = some va) (hc : t.regs c = some vc) (hz : t.regs z = some vz)
    (hsrc : f32x2Elems va = .ok p) (hcv : f32x2Elems vc = .ok (cz.1, cz.2.1))
    (hzv : f32x2Elems vz = .ok cz.2.2) (hS0 : SegFreePc A' t.pc)
    (hS1 : SegFreePc A' (t.pc + 1)) :
    run K (idealReal name s why :: A') L g 2 t = some (PTX.next (setReg (setReg
      (PTX.next (setReg t q (FmaItem.prod cz p))) x (.float .f32 (p.1 * cz.1 + cz.2.2.1))) y
      (.float .f32 (p.2 * cz.2.1 + cz.2.2.2)))) := by
  obtain ⟨p0, p1⟩ := p
  obtain ⟨c0, c1, z0, z1⟩ := cz
  rw [run_step h1 rfl hf (exec_fma2 hs hS0 ha hc hz hsrc hcv hzv)]
  let t1 := PTX.next (setReg t q (FmaItem.prod (c0, c1, z0, z1) (p0, p1)))
  have hc1 : K.code[t1.pc]? =
      some ⟨none, .move ⟨.unpack, .int .b 64, [some x, some y], [.reg q]⟩⟩ := h2
  have hq : t1.regs q =
      some (.pair (.float .f32 (p0 * c0 + z0)) (.float .f32 (p1 * c1 + z1))) := by
    simp [t1, PTX.next, setReg, FmaItem.prod]
  show run K _ L g 1 t1 = _
  rw [run_step (n := 0) hc1 rfl hf (exec_unpack64 hq rfl rfl (segFree_ideal hS1) hu)]
  rfl

/-- **One item**: its instructions write the registers of `it.vals`, and keep every other
register. -/
theorem fma_item {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') (hu : NoUnpack64 A')
    {c z : Nat} {it : FmaItem} {t : TState}
    {v : Nat → Value} {vc vz : Value} {cz : ℝ × ℝ × ℝ × ℝ} {p : ℝ × ℝ}
    (hcode : it.codeB K c z t.pc = true) (hf : t.fault = none)
    (hr : ∀ r ∈ it.reads, t.regs r = some (v r)) (hc : t.regs c = some vc)
    (hz : t.regs z = some vz) (hcz : ∀ w ∈ it.writes, w ≠ c ∧ w ≠ z) (hnd : it.writes.Nodup)
    (hpk : it.packOk v = true) (hsrc : f32x2Elems (it.src v) = .ok p)
    (hcv : f32x2Elems vc = .ok (cz.1, cz.2.1)) (hzv : f32x2Elems vz = .ok cz.2.2)
    (hS : ∀ k < it.len, SegFreePc A' (t.pc + k)) :
    ∃ t', run K (idealReal name s why :: A') L g it.len t = some t' ∧
      t'.pc = t.pc + it.len ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
      (∀ r, r ∉ it.writes → t'.regs r = t.regs r) ∧
      (∀ r ∈ it.writes, t'.regs r = (it.vals v cz p).lookup r) := by
  obtain ⟨hpack, hfma, hun⟩ := FmaItem.code_of hcode
  obtain ⟨pk, a, q, x, y⟩ := it
  cases pk with
  | none =>
    simp only [FmaItem.len, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfma hun hS ⊢
    simp only [FmaItem.writes, List.nil_append, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_or, List.nodup_nil] at hnd
    obtain ⟨⟨hqx, hqy⟩, hxy, -⟩ := hnd
    have ha := hr a (by simp [FmaItem.reads])
    refine ⟨_, fma_tail hs (noUnpack64_idealReal hu) hfma hun hf ha hc hz hsrc hcv hzv
      (hS 0 (by omega)) (hS 1 (by omega)), rfl, rfl, rfl, rfl, fun r hr' => ?_,
      fun r hr' => ?_⟩
    · simp only [FmaItem.writes, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        not_or] at hr'
      simp [PTX.next, setReg, Function.update_of_ne hr'.1, Function.update_of_ne hr'.2.1,
        Function.update_of_ne hr'.2.2]
    · simp only [FmaItem.writes, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · simp [PTX.next, setReg, FmaItem.vals, List.lookup, Function.update_of_ne hqx,
          Function.update_of_ne hqy, beq_false_of_ne hqx, beq_false_of_ne hqy]
      · simp [PTX.next, setReg, FmaItem.vals, Function.update_of_ne hxy]
      · simp [PTX.next, setReg, FmaItem.vals, List.lookup, beq_false_of_ne (Ne.symm hxy)]
  | some lh =>
    obtain ⟨lo, hi⟩ := lh
    simp only [FmaItem.len, Option.isSome_some, ↓reduceIte] at hfma hun hS ⊢
    simp only [FmaItem.writes, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil] at hnd
    obtain ⟨⟨haq, hax, hay⟩, ⟨hqx, hqy⟩, hxy, -⟩ := hnd
    have hca := hcz a (by simp [FmaItem.writes])
    have hlo := hr lo (by simp [FmaItem.reads])
    have hhi := hr hi (by simp [FmaItem.reads])
    simp only [FmaItem.packOk, Bool.and_eq_true, beq_iff_eq] at hpk
    have hex := exec_pack (A := idealReal name s why :: A') (noPack_idealReal hN) (L := L)
      (g := g) (d := a) hlo hhi (segFree_ideal (hS 0 (by omega)))
    simp only [hpk, and_self, ↓reduceIte] at hex
    let t0 := PTX.next (setReg t a (joinValue (v lo) (v hi)))
    have h0 : K.code[t.pc]? =
        some ⟨none, .move ⟨.pack, .int .b 64, [some a], [.reg lo, .reg hi]⟩⟩ := by
      simpa using hpack lo hi rfl
    have hfma' : K.code[t0.pc]? = some ⟨none, fma2Op q a c z⟩ := hfma
    have hun' : K.code[t0.pc + 1]? =
        some ⟨none, .move ⟨.unpack, .int .b 64, [some x, some y], [.reg q]⟩⟩ := by
      simpa [t0, PTX.next, setReg, Nat.add_assoc] using hun
    have ha0 : t0.regs a = some (joinValue (v lo) (v hi)) := by simp [t0, PTX.next, setReg]
    have hc0 : t0.regs c = some vc := by
      simp [t0, PTX.next, setReg, Function.update_of_ne (Ne.symm hca.1), hc]
    have hz0 : t0.regs z = some vz := by
      simp [t0, PTX.next, setReg, Function.update_of_ne (Ne.symm hca.2), hz]
    have hS1 : SegFreePc A' t0.pc := hS 1 (by omega)
    have hS2 : SegFreePc A' (t0.pc + 1) := by
      simpa [t0, PTX.next, setReg, Nat.add_assoc] using hS 2 (by omega)
    have hr0 := fma_tail (name := name) (why := why) (L := L) (g := g) hs
      (noUnpack64_idealReal hu) hfma' hun' hf ha0 hc0 hz0 hsrc hcv hzv hS1 hS2
    refine ⟨_, (run_step h0 rfl hf hex).trans hr0, ?_, rfl, rfl, rfl, fun r hr' => ?_,
      fun r hr' => ?_⟩
    · simp only [t0, PTX.next, setReg]
    · simp only [FmaItem.writes, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, not_or] at hr'
      simp [t0, PTX.next, setReg, Function.update_of_ne hr'.1, Function.update_of_ne hr'.2.1,
        Function.update_of_ne hr'.2.2.1, Function.update_of_ne hr'.2.2.2]
    · simp only [FmaItem.writes, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl
      · simp [t0, PTX.next, setReg, FmaItem.vals, FmaItem.src, List.lookup, beq_false_of_ne haq,
          beq_false_of_ne hax, beq_false_of_ne hay, Function.update_of_ne haq,
          Function.update_of_ne hax, Function.update_of_ne hay]
      · simp [t0, PTX.next, setReg, FmaItem.vals, List.lookup, beq_false_of_ne hqx,
          beq_false_of_ne hqy, Function.update_of_ne hqx, Function.update_of_ne hqy]
      · simp [t0, PTX.next, setReg, FmaItem.vals, Function.update_of_ne hxy]
      · simp [t0, PTX.next, setReg, FmaItem.vals, List.lookup, beq_false_of_ne (Ne.symm hxy)]

theorem FmaItem.keys_iff {v : Nat → Value} {cz : ℝ × ℝ × ℝ × ℝ} {p : ℝ × ℝ} {it : FmaItem}
    {r : Nat} : r ∈ (it.vals v cz p).map Prod.fst ↔ r ∈ it.writes := by
  obtain ⟨pk, a, q, x, y⟩ := it
  cases pk <;> simp [FmaItem.vals, FmaItem.writes] <;> tauto

theorem fmaVals_keys {v : Nat → Value} {cz : ℝ × ℝ × ℝ × ℝ} {r : Nat} :
    ∀ (items : List FmaItem) (ps : List (ℝ × ℝ)), items.length = ps.length →
      (r ∈ (fmaVals v cz items ps).map Prod.fst ↔ r ∈ items.flatMap FmaItem.writes)
  | [], [], _ => by simp [fmaVals]
  | it :: its, p :: ps, hl => by
    simp only [fmaVals, List.map_append, List.mem_append, List.flatMap_cons,
      FmaItem.keys_iff, fmaVals_keys its ps (by simpa using hl)]
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- **A run of items**: the instructions write the registers of `fmaVals` and keep every
other register. -/
theorem fmas_run {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') (hu : NoUnpack64 A')
    {c z : Nat} {v : Nat → Value} {vc vz : Value}
    {cz : ℝ × ℝ × ℝ × ℝ} (hcv : f32x2Elems vc = .ok (cz.1, cz.2.1))
    (hzv : f32x2Elems vz = .ok cz.2.2) :
    ∀ (items : List FmaItem) (ps : List (ℝ × ℝ)) (t : TState),
      fmaCodeB K c z t.pc items = true → t.fault = none →
      (∀ it ∈ items, ∀ r ∈ it.reads, t.regs r = some (v r)) → t.regs c = some vc →
      t.regs z = some vz →
      (∀ it ∈ items, ∀ w ∈ it.writes, w ≠ c ∧ w ≠ z ∧ ∀ it' ∈ items, w ∉ it'.reads) →
      (items.flatMap FmaItem.writes).Nodup → items.all (FmaItem.packOk v) = true →
      items.map (fun it => f32x2Elems (it.src v)) = ps.map Except.ok →
      (∀ k < fmaLen items, SegFreePc A' (t.pc + k)) →
      ∃ t', run K (idealReal name s why :: A') L g (fmaLen items) t = some t' ∧
        t'.pc = t.pc + fmaLen items ∧ t'.sub = t.sub ∧ t'.acc = t.acc ∧ t'.fault = t.fault ∧
        (∀ r, r ∉ items.flatMap FmaItem.writes → t'.regs r = t.regs r) ∧
        (∀ r ∈ items.flatMap FmaItem.writes, t'.regs r = (fmaVals v cz items ps).lookup r)
  | [], _, t, _, _, _, _, _, _, _, _, _, _ =>
    ⟨t, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => by simp at h⟩
  | _ :: _, [], _, _, _, _, _, _, _, _, _, hel, _ => by simp at hel
  | it :: its, p :: ps, t, hcode, hf, hr, hc, hz, hdis, hnd, hpk, hel, hS => by
    simp only [fmaCodeB, Bool.and_eq_true] at hcode
    simp only [List.all_cons, Bool.and_eq_true] at hpk
    simp only [List.map_cons, List.cons.injEq] at hel
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨t1, hr1, hpc1, hsub1, hacc1, hf1, hfr1, hw1⟩ := fma_item (name := name) (why := why)
      (L := L) (g := g) (A' := A') hs hN hu hcode.1 hf (hr it (by simp)) hc hz
      (fun w hw => ⟨(hdis it (by simp) w hw).1, (hdis it (by simp) w hw).2.1⟩) hnd.1 hpk.1 hel.1
      hcv hzv (fun k hk => hS k (by simp only [fmaLen]; omega))
    have hkeep : ∀ it' ∈ its, ∀ r ∈ it'.reads, r ∉ it.writes := fun it' hit' r hr' hw =>
      (hdis it (by simp) r hw).2.2 it' (by simp [hit']) hr'
    have hcw : c ∉ it.writes := fun hw => (hdis it (by simp) c hw).1 rfl
    have hzw : z ∉ it.writes := fun hw => (hdis it (by simp) z hw).2.1 rfl
    obtain ⟨t2, hr2, hpc2, hsub2, hacc2, hf2, hfr2, hw2⟩ := fmas_run hs hN hu hcv hzv its ps t1
      (by rw [hpc1]; exact hcode.2) (hf1.trans hf)
      (fun it' hit' r hr' => (hfr1 r (hkeep it' hit' r hr')).trans (hr it' (by simp [hit']) r hr'))
      ((hfr1 c hcw).trans hc) ((hfr1 z hzw).trans hz)
      (fun it' hit' w hw => ⟨(hdis it' (by simp [hit']) w hw).1,
        (hdis it' (by simp [hit']) w hw).2.1,
        fun it'' hit'' => (hdis it' (by simp [hit']) w hw).2.2 it'' (by simp [hit''])⟩)
      hnd.2.1 hpk.2 hel.2 (fun k hk => by
        rw [hpc1, Nat.add_assoc]; exact hS _ (by simp only [fmaLen]; omega))
    refine ⟨t2, run_comp hr1 hr2, by rw [hpc2, hpc1, fmaLen, Nat.add_assoc],
      hsub2.trans hsub1, hacc2.trans hacc1, hf2.trans hf1, fun r hr' => ?_, fun r hr' => ?_⟩
    · simp only [List.flatMap_cons, List.mem_append, not_or] at hr'
      rw [hfr2 r hr'.2, hfr1 r hr'.1]
    · simp only [fmaVals]
      rcases List.mem_append.mp (by simpa only [List.flatMap_cons] using hr') with h1 | h2
      · have hn : r ∉ its.flatMap FmaItem.writes := fun h => hnd.2.2 r h1 r h rfl
        rw [hfr2 r hn, hw1 r h1]
        obtain ⟨w, hw⟩ := lookup_of_mem_keys (FmaItem.keys_iff.mpr h1 :
          r ∈ (it.vals v cz p).map Prod.fst)
        rw [hw, lookup_append_some hw]
      · have hn : r ∉ it.writes := fun h => hnd.2.2 r h r h2 rfl
        rw [hw2 r h2, lookup_append_none (fun h => hn (FmaItem.keys_iff.mp h))]

/-- **A run of items, as a piece**: from facts with explicit values, the products and their
packs in front. -/
theorem Seg.fmas {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') (hu : NoUnpack64 A')
    {pc c z : Nat} {liveS liveT : List Nat}
    {base : Nat → Value} {ex : List (Nat × Value)} {items : List FmaItem}
    {ps : List (ℝ × ℝ)} {cz : ℝ × ℝ × ℝ × ℝ}
    (hcode : fmaCodeB K c z pc items = true)
    (hreads : ∀ it ∈ items, ∀ r ∈ it.reads, r ∈ liveS) (hc : c ∈ liveS) (hz : z ∈ liveS)
    (hdis : ∀ it ∈ items, ∀ w ∈ it.writes, w ≠ c ∧ w ≠ z ∧ ∀ it' ∈ items, w ∉ it'.reads)
    (hnd : (items.flatMap FmaItem.writes).Nodup)
    (hpk : items.all (FmaItem.packOk (valueEx base ex)) = true)
    (hel : items.map (fun it => f32x2Elems (it.src (valueEx base ex))) = ps.map Except.ok)
    (hcv : f32x2Elems (valueEx base ex c) = .ok (cz.1, cz.2.1))
    (hzv : f32x2Elems (valueEx base ex z) = .ok cz.2.2)
    (hS : ∀ k < fmaLen items, SegFreePc A' (pc + k))
    (hcov : ∀ r ∈ liveT, r ∈ items.flatMap FmaItem.writes ∨
      (r ∉ items.flatMap FmaItem.writes ∧ r ∈ liveS)) :
    Seg K (idealReal name s why :: A') L g (fmaLen items) pc (factsFrom liveS (valueEx base ex))
      (pc + fmaLen items)
      (factsFrom liveT (valueEx base (fmaVals (valueEx base ex) cz items ps ++ ex))) := by
  intro t h
  have hR := h.2.2.2.2
  have hlen : items.length = ps.length := by simpa using congrArg List.length hel
  obtain ⟨t', hr, hpc, hsub, hacc, hf, hfr, hw⟩ := fmas_run (name := name) (why := why)
    (L := L) (g := g) (A' := A') hs hN hu hcv hzv items ps t (by rw [h.1]; exact hcode)
    h.2.2.2.1
    (fun it hit r hr' => holds_mem hR (mem_factsFrom (hreads it hit r hr')))
    (holds_mem hR (mem_factsFrom hc)) (holds_mem hR (mem_factsFrom hz)) hdis hnd hpk hel
    (fun k hk => by rw [h.1]; exact hS k hk)
  refine ⟨t', hr, by rw [hpc, h.1], hsub.trans h.2.1, hacc.trans h.2.2.1,
    hf.trans h.2.2.2.1, ?_⟩
  refine holds_ext (W := items.flatMap FmaItem.writes) hR hfr
    (fun r hr' => hw r ((fmaVals_keys items ps hlen).mp hr')) (fun r hr' => ?_)
  rcases hcov r hr' with h1 | h2
  · exact .inl ((fmaVals_keys items ps hlen).mpr h1)
  · exact .inr h2

end
end PTX.Flow
