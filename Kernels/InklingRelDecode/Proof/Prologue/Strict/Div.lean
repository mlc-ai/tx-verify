-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Qt
public import Kernels.InklingRelDecode.Proof.Lib.IntStep
public import Kernels.InklingRelDecode.Proof.Lib.RawArith
public import Kernels.InklingRelDecode.Proof.Lib.RulesFrame
public import Lemmas.Flow.SegQOps
public import Lemmas.Flow.Arith32Word
public import Kernels.InklingRelDecode.Proof.Prologue.Control.Route
import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # A signed division of two non-negative facts is a strict piece

The core has no rule for a signed quotient of a negative inexact division or of a zero divisor
(`intDiv`). The prologue divides non-negative numerators by positive divisors. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Arith32

theorem intDiv_s_ok {a b : BitVec 64} (hn : 0 ≤ intOf .s 32 (r32 a))
    (hp : 0 < intOf .s 32 (r32 b)) :
    intDiv .s 32 (r32 a) (r32 b) = .ok ((intOf .s 32 (r32 a)).tdiv (intOf .s 32 (r32 b))) := by
  have hlt : intOf .s 32 (r32 a) < 2 ^ 31 := by
    simp only [intOf, ite_true, toSigned]
    split <;> omega
  simp only [intDiv]
  generalize intOf .s 32 (r32 a) = A at *
  generalize intOf .s 32 (r32 b) = B at *
  have h1 : ¬ B = 0 := by omega
  have h2 : ¬ (¬A.tmod B = 0 ∧ ¬(A < 0 ↔ B < 0)) := by
    intro ⟨_, h⟩; apply h; omega
  have h3 : ¬ 2147483648 ≤ A.tdiv B := by
    have := Int.tdiv_le_self (a := A) (b := B) hn
    omega
  simp [h1, h2, h3, pure, Except.pure]

theorem div_s_piece {L : Launch} {g pc dst x y : Nat} {a b : BitVec 64}
    {F G : List (Nat × Value)}
    (fetch : kernel.code[pc]? = some ⟨none, .int ⟨.div, .int .s 32, false, [some dst],
      [.reg x, .reg y]⟩⟩)
    (hs : Assumptions.emuSites.contains pc = false)
    (hx : ∀ R, Holds R F → R x = some (.bits 32 a))
    (hy : ∀ R, Holds R F → R y = some (.bits 32 b))
    (hw : ∀ R, Holds R F → Holds (Function.update R dst (some (.bits 32
      (intBits 32 ((intOf .s 32 (r32 a)).tdiv (intOf .s 32 (r32 b))))))) G)
    (hn : 0 ≤ intOf .s 32 (r32 a)) (hp : 0 < intOf .s 32 (r32 b))
    (hB : dst ∉ (proQt (pc + 1)).map Prod.fst)
    (hq : tagsIn (proQt (pc + 1)) (proQt pc) = true) :
    SegQ kernel Assumptions.all L g (QT proQt) pc F (pc + 1) G := by
  intro t ht hQ
  obtain ⟨hpc, hsub, hacc, hf, hF⟩ := ht
  have heval := Lib.workerInt (ii := ⟨.div, .int .s 32, false, [some dst], [.reg x, .reg y]⟩)
    (L := L) (g := g) rfl hpc hs
  have readX := readBits_regBits (L := L) (g := g) (w := 32) (hx _ hF) (by rfl)
  have readY := readBits_regBits (L := L) (g := g) (w := 32) (hy _ hF) (by rfl)
  have lanes : (DType.int .s 32).intLanes? = some (.s, 32, 1) := rfl
  have he := heval
  simp only [execInt, intResult, DType.width, lanes, readX, readY, bind, Except.bind,
    intDiv_s_ok hn hp, pure, Except.pure] at he
  have tau := tau_of_ok (K := kernel) (hpc ▸ fetch) rfl hf he
  refine ⟨_, .single tau, ⟨congrArg (· + 1) hpc, hsub, hacc, hf, ?_⟩, ?_⟩
  · exact hw _ hF
  · have hQ' : Typed (proQt pc) t := by simpa [QT, hpc] using hQ
    have hT := typed_of_tagsIn hq hQ'
    intro r tg hr
    have hr' : (proQt (pc + 1)).lookup r = some tg := by simpa [PTX.next, setReg, hpc] using hr
    have hne : r ≠ dst := fun h => hB (h ▸ List.mem_map_of_mem (f := Prod.fst) (lookup_mem hr'))
    simpa [PTX.next, setReg, Function.update_of_ne hne] using hT r tg hr'

theorem div128_W {n : Nat} (h : n < 2 ^ 31) : Control.div128 (W n) = W (n / 128) := by
  unfold Control.div128
  have sign : shrs (W n) 31 = W (n / 2 ^ 31) := toNat_shrs_W h (k := 31) (by decide)
  rw [sign, Nat.div_eq_of_lt h]
  change shrs (add32 (W n) (W 0)) 7 = _
  rw [add32_W (by omega), Nat.add_zero]
  exact toNat_shrs_W h (k := 7) (by decide)

/-- The numerator of an iteration count (`splits - 1 - split + blocks`) is non-negative. -/
theorem dividend_nonneg {n s p : Nat} (hs : s < n) (hn : n + 2 ^ 24 < 2 ^ 31) (hp : p < 2 ^ 31) :
    0 ≤ intOf .s 32 (r32 (add32 (add32 (W n) (not32 (W s))) (Control.div128 (W p)))) := by
  have hd : p / 128 < 2 ^ 24 := by omega
  rw [div128_W hp, not32_add_W hs (by omega), add32_W (by omega), r32_W (by omega)]
  simp only [intOf, ite_true, toSigned_W (show n - 1 - s + p / 128 < 2 ^ 31 by omega)]
  exact Int.natCast_nonneg _

/-- A positive count below `2 ^ 31` is a positive signed divisor. -/
theorem divisor_pos {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 31) :
    0 < intOf .s 32 (r32 (BitVec.ofNat 64 (n % 2 ^ 32))) := by
  rw [Nat.mod_eq_of_lt (by omega)]
  show 0 < toSigned 32 (r32 (W n))
  rw [r32_W (by omega), toSigned_W h]
  exact_mod_cast h0

/-- The value of a table register in the facts. -/
theorem holds_tab {D : List (Nat × Value)} {rs : List Nat} {V : Nat → Value} {r : Nat}
    (h : r ∈ rs) : ∀ R, Holds R (D ++ factsFrom rs V) → R r = some (V r) :=
  fun _ hR => holds_mem hR (List.mem_append_right _ (mem_factsFrom h))

/-- A write of a register of the table, past the explicit facts that do not name it. -/
theorem holds_tab_write {D : List (Nat × Value)} {rs rs' : List Nat} {V : Nat → Value} {dst : Nat}
    (hD : ∀ q ∈ D, q.1 ≠ dst) (keys : ∀ r ∈ rs', r = dst ∨ r ∈ rs) :
    ∀ R, Holds R (D ++ factsFrom rs V) →
      Holds (Function.update R dst (some (V dst))) (D ++ factsFrom rs' V) := fun R hR => by
  rw [holds_append] at hR ⊢
  exact ⟨holds_update hR.1 hD, Lib.writeLive keys hR.2⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
