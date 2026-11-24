-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmTotF
public import Lemmas.Flow.MulIdeal

@[expose] public section

/-! # The shuffle of the row maximum on any words (pc 1838)

Where the running maximum, the received word and the 64 words of the columns are score words, the
successor is the state of the real numbers (`D.afterMax`, `step_shfl5R` in `SmStgB`). For the other
words this file prepares a successor: `D.afterMaxT` records the registers the stage's second half
writes as Core's outcomes (the values of `SmTotV`) and clears the flag `Stg.re`. It proves that
the facts at the shuffle of the half sums are the table of `D.afterMaxT` (`ovMT_eq`), the invariant
there, and the run (`run_afterMaxT`: the thread reaches the shuffle of the half sums where no
instruction of pcs 1839 to 2233 faults, `D.s2Ok`, and is dead otherwise). `SmTotH` proves that the
P store's packed pairs then have conversions.

`Sm.next` does not use `D.afterMaxT` yet: it stops following (`some none`) where a word is not a
score word (`step_shfl5`), because the layers above read the real numbers of every softmax state
(the development notes, "Total machines, part 9"). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Classical

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### The facts at the shuffle of the half sums -/

/-! ### `alpha` reads as a real number on any words -/

theorem readEReal_top : readEReal .f32 (erealValue .f32 ⊤) = some (.ok ⊤) := by
  simp [erealValue, FVal.toValue, readEReal, readEReal.ofDatum, classify, Value.bitPattern,
    Value.bytes, FloatFmt.bytes, FloatFmt.layout, Layout.infPattern, Layout.decode, Layout.width]
  rfl

theorem readEReal_ereal (x : EReal) : readEReal .f32 (erealValue .f32 x) = some (.ok x) := by
  by_cases h : x = ⊤
  · subst h; exact readEReal_top
  · exact readEReal_erealValue h

theorem alrOf_eq {v : Value} {a : ℝ} (h : readEReal .f32 v = some (.ok (a : EReal))) :
    alrOf v = a := by
  simp [alrOf, h]

/-- **`alpha` reads as a real number** wherever the scalars of the stage have outcomes:
`alpha_log2` (`%r809`, a `mul.f32` without rounding modifier) is the value of an extended real
`r`; where `r ≥ -8` (also `r = +inf`) `alpha` is the pattern `1.0`, otherwise `r` is not `+inf`
and `alpha` is the exact `2 ^ r`. -/
theorem alT_read {d : D} {recv : Value} (h : d.okA recv) :
    readEReal .f32 (d.alT recv) = some (.ok ((alrOf (d.alT recv) : ℝ) : EReal)) := by
  suffices hx : ∃ a : ℝ, readEReal .f32 (d.alT recv) = some (.ok (a : EReal)) by
    obtain ⟨a, ha⟩ := hx
    rw [alrOf_eq ha]; exact ha
  have h5 : (d.t5E recv).toBool = true := h.1.1.1.1.1.2
  obtain ⟨v5, hv5⟩ : ∃ v, d.t5E recv = .ok v := by
    rcases hE : d.t5E recv with e | v
    · rw [hE] at h5; cases h5
    · exact ⟨v, rfl⟩
  obtain ⟨-, -, r, -, -, -, rfl⟩ := mulE_ok hv5
  have ht5 : d.t5 recv = erealValue .f32 r := by simp [D.t5, hv5, okVal]
  have ht6 : d.t6 recv = decide (r ≥ ((-8 : ℝ) : EReal)) := by
    simp only [D.t6, D.t6E, ht5, setpE, idealSetp, fcmpBase, readEReal_ereal, readEReal_m8,
      bindRead, okB, pure, Except.pure, erealCompare]
  have h8 : d.alT recv = okVal (b32 0)
      (movE (if d.t6 recv then imm32 1065353216 else d.t7 recv)) := rfl
  by_cases hr : r ≥ ((-8 : ℝ) : EReal)
  · refine ⟨1, ?_⟩
    have : d.alT recv = imm32 1065353216 := by
      rw [h8, ht6, decide_eq_true hr]
      rfl
    rw [this]
    exact readEReal_of_valFloat valFloat_one
  · have hne : r ≠ ⊤ := fun e => hr (by rw [e]; exact le_top)
    refine ⟨Softmax.pow2 r, ?_⟩
    have h7 : d.t7 recv = .float .f32 (Softmax.pow2 r) := by
      simp [D.t7, D.t7E, ht5, ex2E_ereal hne, okVal]
    have : d.alT recv = .float .f32 (Softmax.pow2 r) := by
      rw [h8, ht6, decide_eq_false hr, h7]
      rfl
    rw [this]
    simp [readEReal, pure, Except.pure]


theorem ovMT_eq (d : D) (recv : Value) :
    ∀ r ∈ Flow.live 2234, valueEx (valueOf L g d) (xtT L g d recv) r =
      valueOf L g (d.afterMaxT L g recv) r := by
  intro r hr
  rcases live_2234_cases r hr with ⟨hf, hx⟩ | h1532 | ⟨hp1, hp2⟩ | ⟨hs1, hs2⟩ | h508 | h1525 |
    h168
  · rw [xtT_free d recv _ hf]
    rcases hx with hx | rfl
    · exact (valueOf_nonX (L := L) (g := g) (d := d) (d' := d.afterMaxT L g recv) rfl rfl rfl
        rfl rfl rfl hx).symm
    · rw [valueOf_r45, valueOf_r45]
      rfl
  · subst h1532
    rw [xtT_1529, valueOf_r1070]
    rfl
  · obtain ⟨q, rfl⟩ : ∃ q, r = 1994 + q := ⟨r - 1994, by omega⟩
    rw [xtT_pair d recv _ (by omega), valueOf_rd _ (by omega)]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, r = 508 + k := ⟨r - 508, by omega⟩
    rw [xtT_single d recv _ (by omega), valueOf_rP _ (by omega)]
    rfl
  · subst h508
    rw [xtT_507, valueOf_r46]
    rfl
  · subst h1525
    rw [xtT_1522, valueOf_r1063]
    rfl
  · subst h168
    rw [xtT_168, valueOf_p168]
    rfl

/-- **The invariant after the stage on any words**: the flag is cleared, so the real readings
are not claimed; `alpha` reads as a real number and the sum is a four-byte word. -/
theorem inv_afterMaxT (hi : Inv L g d) (hl : LateSite d.site) (recv : Value) (hok : d.okA recv) :
    Inv L g (d.afterMaxT L g recv) :=
  inv_stg_al (inv_late hi hl (s := .shfl6) trivial (fun h => absurd h (by simp))) _ d.pf
    (fun h => absurd h (by simp))
    ⟨alT_read hok, hi.four.cm1, hi.four.cm2, hi.four.cm3, hi.four.cm4, hi.four.ld,
      hi.four.m2, swT_bytes d recv⟩

/-! ### The run on any words and the step -/

/-- **The stage's second half on any words, from the facts after the shuffle of the row maximum**:
where no instruction of pcs 1839 to 2233 faults the thread reaches the shuffle of the half sums
with the table and the invariant of `D.afterMaxT`, and otherwise it is dead. -/
theorem run_afterMaxT (hi : Inv L g d) (hs : d.site = .shfl5) (recv : Value) {t : TState}
    (h1 : At t 1839 (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv)))) :
    (d.s2Ok L g recv → ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' (d.afterMaxT L g recv).site.pc (facts L g (d.afterMaxT L g recv)) ∧
      Inv L g (d.afterMaxT L g recv)) ∧
    (¬ d.s2Ok L g recv → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  have hlate : LateSite d.site := by rw [hs]; trivial
  obtain ⟨n, hseg⟩ := seg_stageT (L := L) (g := g) d recv
  obtain ⟨hyes, hno⟩ := hseg _ h1
  refine ⟨fun hok => ?_, hno⟩
  obtain ⟨t', hr, ht'⟩ := hyes hok
  refine ⟨t', run_rtg hr, ht'.mono (holds_of_pointwise fun r hr' => ?_),
    inv_afterMaxT hi hlate recv hok.1⟩
  rw [holds_mem ht'.2.2.2.2 (Flow.mem_factsFrom (val := valueEx (valueOf L g d)
    (xtT L g d recv)) hr')]
  exact congrArg some (ovMT_eq d recv r hr')

/-- **The shuffle of the row maximum** (pc 1838): on score words the real successor
(`step_shfl5R`); on other words the successor of Core's outcomes (`run_afterMaxT`), or the
thread is dead where an instruction of the stage's second half faults. -/
theorem step_shfl5 (hi : Inv L g d) (hs : d.site = .shfl5) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1838 := by rw [hs]; rfl
  have hc' : kernel.code[1838]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_shfl_5)
  have h' : At t 1838 (factsAt L g 1838 d) := hpc ▸ h
  have hf' := hpc ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, hu⟩ := fires_shfl (p := none) hf'
  simp only [Option.elim] at hu
  subst hu
  by_cases hck : d.RealIn recv
  · exact step_shfl5R hi hs h hc hf (fun _ _ _ _ _ he => by cases he; exact hck)
  have h1 := At.set (r := 1521) (v := recv) h' (facts_ne (by decide +kernel))
  have h1' : At (PTX.next (setReg t 1521 recv)) 1839
      (factsFrom (Flow.live 1839) (valueEx (valueOf L g d) (xa0 recv))) :=
    h1.mono (holds_xa0 h1.2.2.2.2)
  obtain ⟨hyes, hno⟩ := run_afterMaxT hi hs recv h1'
  by_cases hok : d.s2Ok L g recv
  · obtain ⟨t', hr, hat, hinv⟩ := hyes hok
    refine .inl (.inr ⟨d.afterMaxT L g recv, t', ?_, hr, hat, hinv⟩)
    simp only [next, hs, hck, hok, ↓reduceIte]
  · refine .inr ⟨?_, hno hok⟩
    simp only [next, hs, hck, hok, ↓reduceIte]

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
