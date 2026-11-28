-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TypedDeclH

@[expose] public section

/-! # The segments of the declining forms

`segQ_decl` is the segment of one local instruction that writes the datum of tag `tg` to `d`
when the ideal rule does not decline there (`hnd`, a fact of the states of `TauAll R`); the five
forms `add`, `sub`, `mul` (one lane) and `add`, `mul` (`.f32x2`) are its instances. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Assumption

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem segQ_decl {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {tg : TagF} {op : Op}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hst : ∀ t : TState, TypedF (qt pc) t → t.pc = pc → R t →
      ∃ v, execLocalA A L g t op = .ok (PTX.next (setReg t d v)) ∧ tg.ok (some v))
    (hq : afterF qt pc [(d, tg)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G := by
  refine SegQ.local1 hc hl hG fun t ht ⟨hQ, hT⟩ => ?_
  have hty : TypedF (qt pc) t := by simpa [QTF, ht.1] using hQ
  obtain ⟨v, hex, hdv⟩ := hst t hty ht.1 (hT t .refl)
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := tg) hdv
  refine ⟨_, hex, by simp [PTX.next, setReg, ht.1], rfl, rfl, rfl,
    fun p hp => by simp [setReg, PTX.next, hd p hp],
    fun hu => ⟨QTF.after1 hQ ht.1 (by simp [PTX.next, setReg, ht.1]) hw1 hw2 hq,
      fun w hw => hT w (.head hu hw)⟩⟩

/-- `add.f32 d, a, b` (no rounding modifier) where the ideal rule does not decline. -/
theorem segQ_addD {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {fz : Bool} {a b : Opnd}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, scalarOp .add fz d a b⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.add .f32) L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t → execIdealFloat L g t (scalarOp .add fz d a b) ≠ none)
    (ha : d32o (qt pc) a = true) (hb : d32o (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat32)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_decl hc rfl (fun t hty hp hr => by
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hty
    obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) hb hty
    obtain ⟨v, hv, hdv⟩ := addD_step (hI t hp) hva hvb hda hdb (hnd t hp hr)
    exact ⟨v, hv, _, rfl, hdv⟩) hq hG hd

/-- `sub.f32 d, a, b` (no rounding modifier) where the ideal rule does not decline. -/
theorem segQ_subD {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {fz : Bool} {a b : Opnd}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, scalarOp .sub fz d a b⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.subRn .f32) L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t → execIdealFloat L g t (scalarOp .sub fz d a b) ≠ none)
    (ha : d32o (qt pc) a = true) (hb : d32o (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat32)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_decl hc rfl (fun t hty hp hr => by
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hty
    obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) hb hty
    obtain ⟨v, hv, hdv⟩ := subD_step (hI t hp) hva hvb hda hdb (hnd t hp hr)
    exact ⟨v, hv, _, rfl, hdv⟩) hq hG hd

/-- `mul.f32 d, a, b` (no rounding modifier) where the ideal rule does not decline. -/
theorem segQ_mulD' {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {fz : Bool} {a b : Opnd}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, scalarOp .mul fz d a b⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A (.mul .f32) L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t → execIdealFloat L g t (scalarOp .mul fz d a b) ≠ none)
    (ha : d32o (qt pc) a = true) (hb : d32o (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat32)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_decl hc rfl (fun t hty hp hr => by
    obtain ⟨va, hva, hda⟩ := d32o_is (L := L) (g := g) ha hty
    obtain ⟨vb, hvb, hdb⟩ := d32o_is (L := L) (g := g) hb hty
    obtain ⟨v, hv, hdv⟩ := mulD_step' (hI t hp) hva hvb hda hdb (hnd t hp hr)
    exact ⟨v, hv, _, rfl, hdv⟩) hq hG hd

/-- `add.f32x2 d, a, b` (no rounding modifier) where the ideal rule does not decline. -/
theorem segQ_add2D {qt : Nat → EnvF} {R : TState → Prop} {pc d a b : Nat}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, pairOp .add d a b⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A .addRnF32x2 L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t → execIdealFloat L g t (pairOp .add d a b) ≠ none)
    (ha : d64 (qt pc) a = true) (hb : d64 (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat64)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_decl hc rfl (fun t hty hp hr => by
    obtain ⟨va, hva, hda⟩ := d64_ok ha hty
    obtain ⟨vb, hvb, hdb⟩ := d64_ok hb hty
    obtain ⟨v, hv, hdv⟩ := add2D_step (hI t hp) hva hvb hda hdb (hnd t hp hr)
    exact ⟨v, hv, _, rfl, hdv⟩) hq hG hd

/-- `mul.f32x2 d, a, b` (no rounding modifier) where the ideal rule does not decline. -/
theorem segQ_mul2D {qt : Nat → EnvF} {R : TState → Prop} {pc d a b : Nat}
    {F G : List (Nat × Value)} (hc : K.code[pc]? = some ⟨none, pairOp .mul d a b⟩)
    (hI : ∀ t : TState, t.pc = pc → IdealAt A .mulF32x2 L g t)
    (hnd : ∀ t : TState, t.pc = pc → R t → execIdealFloat L g t (pairOp .mul d a b) ≠ none)
    (ha : d64 (qt pc) a = true) (hb : d64 (qt pc) b = true)
    (hq : afterF qt pc [(d, .dat64)] = true) (hG : ∀ p ∈ G, p ∈ F) (hd : ∀ p ∈ G, p.1 ≠ d) :
    SegQ K A L g (fun t => QTF qt t ∧ TauAll K A L g R t) pc F (pc + 1) G :=
  segQ_decl hc rfl (fun t hty hp hr => by
    obtain ⟨va, hva, hda⟩ := d64_ok ha hty
    obtain ⟨vb, hvb, hdb⟩ := d64_ok hb hty
    obtain ⟨v, hv, hdv⟩ := mul2D_step (hI t hp) hva hvb hda hdb (hnd t hp hr)
    exact ⟨v, hv, _, rfl, hdv⟩) hq hG hd

end
end PTX.Flow.TyG
