-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FmaRun
public import Lemmas.Flow.SegDead

@[expose] public section

/-! # Runs of packed products from raw words

`FmaRun` takes a run of `fma.rn.f32x2` products when every source pair reads as two numbers.
When the source pairs are raw words (a load returned them), the run continues exactly when
each item's pack accepts its words and its source pair reads as two numbers (`FmaItem.Ok`);
otherwise it either faults or reads an infinity. The three cases are distinct: a NaN or an
infinity element is no fault. The ideal rule declines a NaN operand (`readEReal` has no value for
it), so the Core rule runs the product sum and writes a NaN pair without faulting, and an
infinity reads as that infinity. So a run the items do not all accept is not necessarily dead:

* `FmaRun`'s `fmas_run` writes the products when every item is `Ok` (`Seg.fmas` is the run as a
  piece in that case);
* `fmas_dead` kills the thread when some item's pack rejects its words or a pair it reads has no
  value (`FmaFault`, the list-wise `fmasFaults`), the items before it reading as numbers.

`f32x2Read` is the reading of a raw pair, which a pair that reads as numbers has. -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- The two numbers a pair reads as (`0` for an element that does not read). -/
def f32x2Read (u : Value) : ℝ × ℝ := (rd32 (splitValue 64 u).1, rd32 (splitValue 64 u).2)

theorem f32x2Read_eq_of_f32x2Elems {u : Value} {q : ℝ × ℝ} (h : f32x2Elems u = .ok q) :
    q = f32x2Read u := by
  unfold f32x2Elems at h
  unfold f32x2Read rd32
  generalize splitValue 64 u = p at h ⊢
  obtain ⟨v0, v1⟩ := p
  cases h0 : valFloat .f32 v0 <;> cases h1 : valFloat .f32 v1 <;> simp_all [Except.toOption]

/-- An item continues: its pack accepts its words and its source pair reads as numbers. -/
def FmaItem.Ok (v : Nat → Value) (it : FmaItem) : Prop :=
  it.packOk v = true ∧ ∃ p, f32x2Elems (it.src v) = .ok p

/-- A packed product sum the run cannot pass: the first pair whose read has no value, the reads
before it having one. A NaN or an infinity operand is no such case: the ideal rule declines a
NaN, so the Core rule applies, and reads an infinity as that infinity. -/
def FmaFault (w c z : Value) : Prop :=
  (∃ f, pairRead w = some (.error f)) ∨
    (∃ p, pairRead w = some (.ok p)) ∧ ((∃ f, pairRead c = some (.error f)) ∨
      (∃ q, pairRead c = some (.ok q)) ∧ ∃ f, pairRead z = some (.error f))

namespace FmaItem

/-- An item the run cannot pass: its pack rejects its words, or a pair it reads faults. -/
def Faults (v : Nat → Value) (vc vz : Value) (it : FmaItem) : Prop :=
  it.packOk v = false ∨ FmaFault (it.src v) vc vz

end FmaItem

/-- Some item of the run is rejected (`FmaItem.Faults`), the ones before it reading as numbers:
the run is dead from there. -/
def fmasFaults (v : Nat → Value) (vc vz : Value) : List FmaItem → Prop
  | [] => False
  | it :: its => it.Faults v vc vz ∨ (it.Ok v ∧ fmasFaults v vc vz its)

variable {K : Kernel} {L : Launch} {g : Nat}

theorem exec_fma2_error {name why : String} {s : IdealScope} {A' : List Assumption}
    {t : TState} {d a b e : Nat} {va vb ve : Value}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hS : SegFreePc A' t.pc)
    (ha : t.regs a = some va) (hb : t.regs b = some vb) (he : t.regs e = some ve)
    (hbad : FmaFault va vb ve) :
    ∃ f, execLocalA (idealReal name s why :: A') L g t (fma2Op d a b e) = .error f := by
  have hop : FloatForm.ofOp (fma2Op d a b e) = some .fmaRnF32x2 := by
    simp [fma2Op, FloatForm.ofOp]
  have hra := readERealPair_reg_val (L := L) (g := g) ha
  have hrb := readERealPair_reg_val (L := L) (g := g) hb
  have hrz := readERealPair_reg_val (L := L) (g := g) he
  rcases hbad with ⟨f, hf⟩ | ⟨⟨p, hp⟩, hrest⟩
  · refine ⟨f, ?_⟩
    have hex : Assumption.execIdealFloat L g t (fma2Op d a b e) = some (.error f) := by
      simp only [fma2Op, Assumption.execIdealFloat, hra, hf, Assumption.bindRead]
    rw [execLocalA_idealReal (f := .fmaRnF32x2) hop hs hS hex]
  rcases hrest with ⟨f, hf⟩ | ⟨⟨q, hq⟩, f, hf⟩
  · refine ⟨f, ?_⟩
    have hex : Assumption.execIdealFloat L g t (fma2Op d a b e) = some (.error f) := by
      simp only [fma2Op, Assumption.execIdealFloat, hra, hrb, hp, hf, Assumption.bindRead]
    rw [execLocalA_idealReal (f := .fmaRnF32x2) hop hs hS hex]
  · refine ⟨f, ?_⟩
    have hex : Assumption.execIdealFloat L g t (fma2Op d a b e) = some (.error f) := by
      simp only [fma2Op, Assumption.execIdealFloat, hra, hrb, hrz, hp, hq, hf,
        Assumption.bindRead]
    rw [execLocalA_idealReal (f := .fmaRnF32x2) hop hs hS hex]

/-- An item the run rejects kills the thread. -/
theorem fma_item_dead {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') {c z : Nat} {it : FmaItem}
    {t : TState} {v : Nat → Value} {vc vz : Value}
    (hcode : it.codeB K c z t.pc = true) (hf : t.fault = none)
    (hr : ∀ r ∈ it.reads, t.regs r = some (v r)) (hc : t.regs c = some vc)
    (hz : t.regs z = some vz) (hca : ∀ lh, it.pk = some lh → it.a ≠ c ∧ it.a ≠ z)
    (hbad : it.Faults v vc vz)
    (hS : ∀ k < it.len, SegFreePc A' (t.pc + k)) :
    Machine.Dead (K := K) (A := idealReal name s why :: A') (L := L) (g := g) t := by
  obtain ⟨hpack, hfma, -⟩ := FmaItem.code_of hcode
  obtain ⟨pk, a, q, x, y⟩ := it
  cases pk with
  | none =>
    simp only [FmaItem.len, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfma hS
    have ha := hr a (by simp [FmaItem.reads])
    have hF : FmaFault (v a) vc vz := by
      rcases hbad with hpk | hF
      · simp [FmaItem.packOk] at hpk
      · simpa [FmaItem.src] using hF
    obtain ⟨f, hfl⟩ := exec_fma2_error (name := name) (why := why) (A' := A') hs
      (by simpa using hS 0 (by omega)) ha hc hz hF
    exact dead_of_error (f := f) (by simpa using hfma) rfl hf hfl
  | some lh =>
    have hca := hca lh rfl
    obtain ⟨lo, hi⟩ := lh
    simp only [FmaItem.len, Option.isSome_some, ↓reduceIte] at hfma hS
    have hlo := hr lo (by simp [FmaItem.reads])
    have hhi := hr hi (by simp [FmaItem.reads])
    have h0 : K.code[t.pc]? =
        some ⟨none, .move ⟨.pack, .int .b 64, [some a], [.reg lo, .reg hi]⟩⟩ := by
      simpa using hpack lo hi rfl
    have hex := exec_pack (A := idealReal name s why :: A') (noPack_idealReal hN) (L := L)
      (g := g) (d := a) hlo hhi (segFree_ideal (hS 0 (by omega)))
    by_cases h4 : (v lo).bytes = 4 ∧ (v hi).bytes = 4
    · simp only [h4, and_self, ↓reduceIte] at hex
      let t0 := PTX.next (setReg t a (joinValue (v lo) (v hi)))
      have hfma' : K.code[t0.pc]? = some ⟨none, fma2Op q a c z⟩ := hfma
      have ha0 : t0.regs a = some (joinValue (v lo) (v hi)) := by simp [t0, PTX.next, setReg]
      have hc0 : t0.regs c = some vc := by
        simp [t0, PTX.next, setReg, Function.update_of_ne (Ne.symm hca.1), hc]
      have hz0 : t0.regs z = some vz := by
        simp [t0, PTX.next, setReg, Function.update_of_ne (Ne.symm hca.2), hz]
      have hF : FmaFault (joinValue (v lo) (v hi)) vc vz := by
        rcases hbad with hpk | hF
        · simp [FmaItem.packOk, h4] at hpk
        · exact hF
      obtain ⟨f, hfl⟩ := exec_fma2_error (name := name) (why := why) (A' := A') hs
        (hS 1 (by omega)) ha0 hc0 hz0 hF
      refine Machine.dead_of_tau (tau_of_ok h0 rfl hf hex) ?_
      exact dead_of_error (f := f) hfma' rfl hf hfl
    · simp only [h4, ↓reduceIte] at hex
      exact dead_of_error h0 rfl hf hex

/-- **A run of items that the raw words reject kills the thread**: some item's pack rejects its
words or a pair it reads has no value (`fmasFaults`), the items before it reading as numbers. -/
theorem fmas_dead {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') (hu : NoUnpack64 A')
    {c z : Nat} {v : Nat → Value} {vc vz : Value}
    {cz : ℝ × ℝ × ℝ × ℝ} (hcv : f32x2Elems vc = .ok (cz.1, cz.2.1))
    (hzv : f32x2Elems vz = .ok cz.2.2) :
    ∀ (items : List FmaItem) (t : TState),
      fmaCodeB K c z t.pc items = true → t.fault = none →
      (∀ it ∈ items, ∀ r ∈ it.reads, t.regs r = some (v r)) → t.regs c = some vc →
      t.regs z = some vz →
      (∀ it ∈ items, ∀ w ∈ it.writes, w ≠ c ∧ w ≠ z ∧ ∀ it' ∈ items, w ∉ it'.reads) →
      (items.flatMap FmaItem.writes).Nodup →
      (∀ k < fmaLen items, SegFreePc A' (t.pc + k)) →
      fmasFaults v vc vz items →
      Machine.Dead (K := K) (A := idealReal name s why :: A') (L := L) (g := g) t
  | [], _, _, _, _, _, _, _, _, _, hbad => hbad.elim
  | it :: its, t, hcode, hf, hr, hc, hz, hdis, hnd, hS, hbad => by
    simp only [fmaCodeB, Bool.and_eq_true] at hcode
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    have hca : ∀ lh, it.pk = some lh → it.a ≠ c ∧ it.a ≠ z := by
      intro lh hlh
      have := hdis it (by simp) it.a (by simp [FmaItem.writes, hlh])
      exact ⟨this.1, this.2.1⟩
    rcases hbad with hbad | ⟨hok, hbad⟩
    · exact fma_item_dead hs hN hcode.1 hf (hr it (by simp)) hc hz hca hbad
        (fun k hk => hS k (by simp only [fmaLen]; omega))
    · obtain ⟨p, hp⟩ := hok.2
      obtain ⟨t1, hr1, hpc1, -, -, hf1, hfr1, -⟩ := fma_item (name := name) (why := why)
        (L := L) (g := g) (A' := A') hs hN hu hcode.1 hf (hr it (by simp)) hc hz
        (fun w hw => ⟨(hdis it (by simp) w hw).1, (hdis it (by simp) w hw).2.1⟩) hnd.1 hok.1 hp
        hcv hzv (fun k hk => hS k (by simp only [fmaLen]; omega))
      have hkeep : ∀ it' ∈ its, ∀ r ∈ it'.reads, r ∉ it.writes := fun it' hit' r hr' hw =>
        (hdis it (by simp) r hw).2.2 it' (by simp [hit']) hr'
      have hcw : c ∉ it.writes := fun hw => (hdis it (by simp) c hw).1 rfl
      have hzw : z ∉ it.writes := fun hw => (hdis it (by simp) z hw).2.1 rfl
      exact dead_of_run hr1 (fmas_dead hs hN hu hcv hzv its t1 (by rw [hpc1]; exact hcode.2)
        (hf1.trans hf)
        (fun it' hit' r hr' => (hfr1 r (hkeep it' hit' r hr')).trans
          (hr it' (by simp [hit']) r hr'))
        ((hfr1 c hcw).trans hc) ((hfr1 z hzw).trans hz)
        (fun it' hit' w hw => ⟨(hdis it' (by simp [hit']) w hw).1,
          (hdis it' (by simp [hit']) w hw).2.1,
          fun it'' hit'' => (hdis it' (by simp [hit']) w hw).2.2 it'' (by simp [hit''])⟩)
        hnd.2.1 (fun k hk => by
          rw [hpc1, Nat.add_assoc]; exact hS _ (by simp only [fmaLen]; omega)) hbad)

/-- **A run of items from raw words is dead**: from facts with explicit values, when some item's
pack rejects its words or a pair it reads has no value, the items before it reading as numbers.
A NaN or an infinity source element is no such case: it leaves the thread alive. -/
theorem fmasDead {name why : String} {s : IdealScope} {A' : List Assumption}
    (hs : FloatForm.fmaRnF32x2 ∈ s.float) (hN : NoPack A') (hu : NoUnpack64 A')
    {pc c z : Nat} {liveS : List Nat} {base : Nat → Value} {ex : List (Nat × Value)}
    {items : List FmaItem} {cz : ℝ × ℝ × ℝ × ℝ}
    (hcode : fmaCodeB K c z pc items = true)
    (hreads : ∀ it ∈ items, ∀ r ∈ it.reads, r ∈ liveS) (hc : c ∈ liveS) (hz : z ∈ liveS)
    (hdis : ∀ it ∈ items, ∀ w ∈ it.writes, w ≠ c ∧ w ≠ z ∧ ∀ it' ∈ items, w ∉ it'.reads)
    (hnd : (items.flatMap FmaItem.writes).Nodup)
    (hcv : f32x2Elems (valueEx base ex c) = .ok (cz.1, cz.2.1))
    (hzv : f32x2Elems (valueEx base ex z) = .ok cz.2.2)
    (hS : ∀ k < fmaLen items, SegFreePc A' (pc + k))
    (hbad : fmasFaults (valueEx base ex) (valueEx base ex c) (valueEx base ex z) items) :
    ∀ t, At t pc (factsFrom liveS (valueEx base ex)) →
      Machine.Dead (K := K) (A := idealReal name s why :: A') (L := L) (g := g) t := by
  intro t h
  have hR := h.2.2.2.2
  exact fmas_dead (name := name) (why := why) (L := L) (g := g) (A' := A') hs hN hu hcv hzv items t
    (by rw [h.1]; exact hcode) h.2.2.2.1
    (fun it hit r hr' => holds_mem hR (mem_factsFrom (hreads it hit r hr')))
    (holds_mem hR (mem_factsFrom hc)) (holds_mem hR (mem_factsFrom hz)) hdis hnd
    (fun k hk => by rw [h.1]; exact hS k hk) hbad

/-- An item's condition reads only the registers it reads. -/
theorem FmaItem.ok_congr {v v' : Nat → Value} {it : FmaItem} (h : ∀ r ∈ it.reads, v r = v' r) :
    it.Ok v ↔ it.Ok v' := by
  obtain ⟨pk, a, q, x, y⟩ := it
  cases pk with
  | none =>
    have ha := h a (by simp [FmaItem.reads])
    simp [FmaItem.Ok, FmaItem.packOk, FmaItem.src, ha]
  | some lh =>
    obtain ⟨lo, hi⟩ := lh
    have hl := h lo (by simp [FmaItem.reads])
    have hh := h hi (by simp [FmaItem.reads])
    simp [FmaItem.Ok, FmaItem.packOk, FmaItem.src, hl, hh]

/-- The items' conditions on facts with explicit values that name none of their reads. -/
theorem FmaItem.ok_valueEx {base : Nat → Value} {ex : List (Nat × Value)} {keys : List Nat}
    {items : List FmaItem} (hk : ex.map Prod.fst = keys)
    (hr : ∀ it ∈ items, ∀ r ∈ it.reads, r ∉ keys) :
    (∀ it ∈ items, it.Ok (valueEx base ex)) ↔ ∀ it ∈ items, it.Ok base := by
  refine forall₂_congr fun it hit => FmaItem.ok_congr fun r hr' => ?_
  have hn : r ∉ ex.map Prod.fst := hk ▸ hr it hit r hr'
  have hl : ex.lookup r = none := by
    simpa using lookup_append_none (ys := ex) (ex := []) hn
  simp [valueEx, hl]

end
end PTX.Flow
