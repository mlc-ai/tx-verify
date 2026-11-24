-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputNumeric
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow PTX.Assumption
open Assumptions (idealArith approx paramPointers storeDrain)

noncomputable section

/-- First instruction of the two-slot probability calculation. -/
def probSite (i : Fin 16) : Nat := 588 + 7 * i.val + if i.val = 0 then 0 else 1

/-- The source pair produced by the peer exchange. -/
def probSource (i : Fin 16) : Nat := scoreSumRegs.getD i.val 0

/-- The packed fma result before unpacking its two exponent arguments. -/
def probFmaReg (i : Fin 16) : Nat :=
  if i.val = 0 then 3241 else if i.val = 1 then 3246 else 3243 + 4 * i.val

/-- The two unpack targets are consecutive. -/
def probArgReg (i : Fin 16) : Nat := 1164 + 2 * i.val

/-- Low exponent output; the high exponent is the next register. -/
def probExpReg (i : Fin 16) : Nat := 1116 + 3 * i.val

/-- The repacked exponent pair fed into the two running lane sums. -/
def probPackReg (i : Fin 16) : Nat :=
  ([3245, 3250, 3254, 3258, 3262, 3266, 3270, 3274, 3278, 3282, 3286, 3290, 3294, 3298,
    3302, 3307] : List Nat).getD i.val 0

/-- The packed running sum after the selected pair. -/
def probSumReg (i : Fin 16) : Nat :=
  ([3249, 3253, 3257, 3261, 3265, 3269, 3273, 3277, 3281, 3285, 3289, 3293, 3297, 3301,
    3306, 3305] : List Nat).getD i.val 0

/-- The preceding pair's sum or the explicit zero in the first pair. -/
def probSumInput (i : Fin 16) : Nat :=
  if i.val = 0 then 3244 else probSumReg ⟨i.val - 1, by have := i.isLt; omega⟩

/-- The zero initialization occurs after the first probability pair has been packed. -/
def probSumSite (i : Fin 16) : Nat := probSite i + 5 + if i.val = 0 then 1 else 0

/-- The last conversion is separated from the packed add by unpacking the final sum. -/
def probCvtSite (i : Fin 16) : Nat := probSumSite i + 1 + if i.val = 15 then 1 else 0

/-- The bf16x2 operand order stores the low score first in shared memory. -/
def probCvtOp (i : Fin 16) : Op :=
  .cvt {
    dst := .packed (.float .bf16) 2, src := .float .f32, rnd := some .rn
    d := 1115 + 3 * i.val, srcs := [.reg (probExpReg i + 1), .reg (probExpReg i)] }

/-- The actual fma, unpack, two exponentials and repack for each probability pair. -/
theorem probHead_code (i : Fin 16) :
    kernel.code[probSite i]? =
      some ⟨none, fma2Op (probFmaReg i) (probSource i) 3243 3248⟩ ∧
    kernel.code[probSite i + 1]? = some ⟨none,
      .move ⟨.unpack, .int .b 64, [some (probArgReg i), some (probArgReg i + 1)],
        [.reg (probFmaReg i)]⟩⟩ ∧
    kernel.code[probSite i + 2]? = some ⟨none,
      .float { ex2I true with dsts := [some (probExpReg i)], srcs := [.reg (probArgReg i)] }⟩ ∧
    kernel.code[probSite i + 3]? = some ⟨none,
      .float { ex2I true with
        dsts := [some (probExpReg i + 1)], srcs := [.reg (probArgReg i + 1)] }⟩ ∧
    kernel.code[probSite i + 4]? = some ⟨none,
      .move ⟨.pack, .int .b 64, [some (probPackReg i)],
        [.reg (probExpReg i), .reg (probExpReg i + 1)]⟩⟩ := by
  fin_cases i <;> refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-- The actual sum and the shared P word's conversion for each pair. -/
theorem probTail_code (i : Fin 16) :
    kernel.code[probSumSite i]? =
      some ⟨none, .float { peerAddI with
        dsts := [some (probSumReg i)], srcs := [.reg (probSumInput i), .reg (probPackReg i)] }⟩ ∧
    kernel.code[probCvtSite i]? = some ⟨none, probCvtOp i⟩ := by
  fin_cases i <;> constructor <;> kernel_rfl

private theorem option_of_except_some {α : Type} {x : Exec α} {v : α} :
    x.toOption = some v → x = .ok v := by
  cases x <;> simp [Except.toOption]

/-- Success of the abstract probability pair supplies every operand and conversion in the run. -/
theorem probPair_operands {L : Launch} {d : D} {i : Nat} {x y : ℝ}
    (h : probPair L d i = some (x, y)) :
    ∃ a lo hi pl ph,
      fma2E (d.scoreSums i) (probScale L) (joinValue (fl (-reference d)) (fl (-reference d))) =
        .ok a ∧ unpackE 64 a = .ok (lo, hi) ∧
      ex2E true lo = .ok pl ∧ ex2E true hi = .ok ph ∧
      valFloat .f32 pl = .ok x ∧ valFloat .f32 ph = .ok y := by
  simp only [probPair, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨a, ha, z, hz, h⟩ := h
  rcases z with ⟨lo, hi⟩
  obtain ⟨pl, hpl, ph, hph, re, hre, im, him, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨a, lo, hi, pl, ph, option_of_except_some ha, option_of_except_some hz,
    option_of_except_some hpl, option_of_except_some hph, option_of_except_some hre,
    option_of_except_some him⟩

/-- The six registers changed by the exponent calculation for one pair. -/
def probHeadWrites (i : Fin 16) : List Nat :=
  [probFmaReg i, probArgReg i, probArgReg i + 1, probExpReg i, probExpReg i + 1, probPackReg i]

private theorem none_probMove {L : Launch} {g : Nat} {t : TState} (m : MoveInstr)
    (h : 579 ≤ t.pc ∧ t.pc ≤ 703) : ∀ a ∈ asms, a.localRule L g t (.move m) = none := by
  have hp : t.pc ∉ paramAdds := by simp [paramAdds]; omega
  have ht : t.pc ∉ prefetchTensorMapSites := by simp [prefetchTensorMapSites]; omega
  have hd : Assumptions.deadPackWords t.pc = none := by
    unfold Assumptions.deadPackWords
    split <;> first | rfl | omega
  exact Thread.asms_localRule_move hp ht hd

private theorem prob_exec_unpack {L : Launch} {g : Nat} {t : TState} {r lo hi : Nat}
    {v vl vh : Value} (hsite : 579 ≤ t.pc ∧ t.pc ≤ 703)
    (hr : t.regs r = some v) (hval : unpackE 64 v = .ok (vl, vh)) :
    execLocalA asms L g t (.move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg r]⟩) =
      .ok (PTX.next (setReg (setReg t lo vl) hi vh)) := by
  let m : MoveInstr := ⟨.unpack, .int .b 64, [some lo, some hi], [.reg r]⟩
  have hh := none_probMove (L := L) (g := g) m hsite
  rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hh,
    execLocal_move (by rfl)]
  unfold unpackE at hval
  split at hval
  · rename_i hwidth
    obtain ⟨hsize, hlo, hhi⟩ := hwidth
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hval).symm
    simp [m, execMove, DType.width, readValue, readReg, hr, hsize, hlo, hhi,
      bind, Except.bind, pure, Except.pure]
    rfl
  · contradiction

section
variable {L : Launch} {g : Nat}

private theorem prob_exec_pack {t : TState} {r lo hi : Nat} {vl vh : Value}
    (hsite : 579 ≤ t.pc ∧ t.pc ≤ 703) (hl : t.regs lo = some vl) (hh : t.regs hi = some vh)
    (hsl : vl.bytes = 4) (hsh : vh.bytes = 4) :
    execLocalA asms L g t (.move ⟨.pack, .int .b 64, [some r], [.reg lo, .reg hi]⟩) =
      .ok (PTX.next (setReg t r (joinValue vl vh))) := by
  let m : MoveInstr := ⟨.pack, .int .b 64, [some r], [.reg lo, .reg hi]⟩
  have hnone := none_probMove (L := L) (g := g) m hsite
  rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hnone,
    execLocal_move (by rfl)]
  simp [m, execMove, DType.width, readValue, readReg, hl, hh, hsl, hsh,
    bind, Except.bind, pure, Except.pure]

/-- Execute the actual packed product, split, exponentials and repack as one local segment. -/
theorem run_probHead (i : Fin 16) (hI : ∀ t : TState, IdealAt asms .fmaRnF32x2 L g t)
    (hD : ∀ t : TState, DeclineAt asms .fmaRnF32x2 L g t)
    (hA : ∀ t : TState, ApproxAt asms (.ex2 .f32) L g t)
    (hAD : ∀ t : TState, ApproxDeclineAt asms (.ex2 .f32) L g t) {t : TState}
    {F : List (Nat × Value)} {v scale bias a lo hi pl ph : Value} (hat : At t (probSite i) F)
    (hr : t.regs (probSource i) = some v) (hs : t.regs 3243 = some scale)
    (hb : t.regs 3248 = some bias) (hfma : fma2E v scale bias = .ok a)
    (hargs : unpackE 64 a = .ok (lo, hi)) (hlo : ex2E true lo = .ok pl)
    (hhi : ex2E true hi = .ok ph) (hframe : ∀ q ∈ F, q.1 ∉ probHeadWrites i) :
    ∃ u, run kernel asms L g 5 t = some u ∧ At u (probSite i + 5)
      ((probPackReg i, joinValue pl ph) :: (probExpReg i, pl) ::
        (probExpReg i + 1, ph) :: F) := by
  have hcode := probHead_code i
  have hpc : 588 ≤ probSite i ∧ probSite i ≤ 694 := by fin_cases i <;> decide
  let t₁ := PTX.next (setReg t (probFmaReg i) a)
  have hr₁ : run kernel asms L g 1 t = some t₁ := by
    refine run_local (K := kernel) hcode.1 rfl hat ?_
    rw [exec_fma2E (hI t) (hD t) hr hs hb, hfma]
    rfl
  have hat₁ : At t₁ (probSite i + 1) [] :=
    ⟨congrArg (·+1) hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, trivial⟩
  have hra : t₁.regs (probFmaReg i) = some a := by
    simp [t₁, PTX.next, setReg]
  let t₂ := PTX.next (setReg (setReg t₁ (probArgReg i) lo) (probArgReg i+1) hi)
  have hr₂ : run kernel asms L g 1 t₁ = some t₂ := by
    refine run_local (K := kernel) hcode.2.1 rfl hat₁ ?_
    have hp := hat₁.1
    exact prob_exec_unpack (by omega) hra hargs
  have hat₂ : At t₂ (probSite i + 2) [] :=
    ⟨congrArg (·+1) hat₁.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, trivial⟩
  have hralo : t₂.regs (probArgReg i) = some lo := by
    simp [t₂, PTX.next, setReg]
  let t₃ := PTX.next (setReg t₂ (probExpReg i) pl)
  have hr₃ : run kernel asms L g 1 t₂ = some t₃ := by
    refine run_local (K := kernel) hcode.2.2.1 rfl hat₂ ?_
    rw [exec_ex2E (hA t₂) (hAD t₂) (OpndIs.reg hralo), hlo]
    rfl
  have hat₃ : At t₃ (probSite i + 3) [] :=
    ⟨congrArg (·+1) hat₂.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, trivial⟩
  have hrahi : t₃.regs (probArgReg i+1) = some hi := by
    have hne : probArgReg i+1 ≠ probExpReg i := by fin_cases i <;> decide
    simp [t₃, t₂, PTX.next, setReg, Function.update_of_ne hne]
  let t₄ := PTX.next (setReg t₃ (probExpReg i+1) ph)
  have hr₄ : run kernel asms L g 1 t₃ = some t₄ := by
    refine run_local (K := kernel) hcode.2.2.2.1 rfl hat₃ ?_
    rw [exec_ex2E (hA t₃) (hAD t₃) (OpndIs.reg hrahi), hhi]
    rfl
  have hat₄ : At t₄ (probSite i + 4) [] :=
    ⟨congrArg (·+1) hat₃.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, trivial⟩
  have hfpl : t₄.regs (probExpReg i) = some pl := by
    simp [t₄, t₃, PTX.next, setReg]
  have hfph : t₄.regs (probExpReg i+1) = some ph := by
    simp [t₄, PTX.next, setReg]
  let u := PTX.next (setReg t₄ (probPackReg i) (joinValue pl ph))
  have hrun : run kernel asms L g 1 t₄ = some u := by
    refine run_local (K := kernel) hcode.2.2.2.2 rfl hat₄ ?_
    have hp := hat₄.1
    exact prob_exec_pack (by omega) hfpl hfph (ex2E_four _ _ _ hlo) (ex2E_four _ _ _ hhi)
  refine ⟨u, run_comp (run_comp (run_comp (run_comp hr₁ hr₂) hr₃) hr₄) hrun,
    congrArg (·+1) hat₄.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · simp [u, PTX.next, setReg]
  · have hne : probExpReg i ≠ probPackReg i := by fin_cases i <;> decide
    simpa [u, PTX.next, setReg, Function.update_of_ne hne] using hfpl
  · have hne : probExpReg i+1 ≠ probPackReg i := by fin_cases i <;> decide
    simpa [u, PTX.next, setReg, Function.update_of_ne hne] using hfph
  · induction F with
    | nil => trivial
    | cons q F ih =>
      obtain ⟨r, vv⟩ := q
      have hn := hframe (r, vv) (by simp)
      simp only [probHeadWrites, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨h₁, h₂⟩ := hat.2.2.2.2
      refine ⟨?_, ?_⟩
      · simpa [u, t₁, t₂, t₃, t₄, PTX.next, setReg, Function.update_apply, hn] using h₁
      · exact ih (hat.mono h₂) (fun q hq => hframe q (List.mem_cons_of_mem _ hq))

private theorem exp_scoreHalf {a v : Value} {x : ℝ}
    (he : ex2E true a = .ok v) (hx : valFloat .f32 v = .ok x) :
    Assumptions.scoreHalf v := by
  unfold ex2E at he
  split at he
  · rename_i e hp
    subst e
    obtain ⟨_, _, h⟩ := bindRead_ok (by simpa only [ex2Val] using hp)
    obtain rfl := Except.ok.inj (Option.some.inj h).symm
    trivial
  · simp only [coreFloat, ex2I, ty1, show List.range 1 = [0] from rfl, List.mapM_cons,
      List.mapM_nil, bind, Except.bind, pure, Except.pure] at he
    generalize classify .f32 (floatLane (ty1 .f32) a 0) = c at he
    cases c with
    | error err => cases he
    | ok u =>
      dsimp only at he
      generalize hv : (ex2I true).lane [u] = out at he
      cases out with
      | none => cases he
      | some out =>
        cases out with
        | pred b => cases he
        | val w =>
          obtain rfl := Except.ok.inj he
          have happ : (ex2I true).approx [u] = some w := by
            change FOut.val <$> (ex2I true).approx [u] = some (.val w) at hv
            generalize (ex2I true).approx [u] = inner at hv ⊢
            cases inner with
            | none => cases hv
            | some wn => exact congrArg some (FOut.val.inj (Option.some.inj hv))
          let z := ((ex2I true).flushIn [u]).headD (.zero false)
          have hflush : (ex2I true).flushIn [u] = [z] := rfl
          rw [FloatInstr.approx, hflush] at happ
          change (ex2Table.lookup (ACls.of FloatFmt.f32.layout z)).bind
            (fun a => some a.val) = some w at happ
          generalize ACls.of FloatFmt.f32.layout z = cls at happ
          cases cls <;> first
            | contradiction
            | (have e := Option.some.inj happ; subst w
               trivial)

private theorem peerAddE_fin {va vb : Value} {a b x y : ℝ}
    (ha : pairRead va = some (.ok ((a : EReal), (b : EReal))))
    (hb : pairRead vb = some (.ok ((x : EReal), (y : EReal)))) :
    peerAddE va vb = .ok (.pair (fl (a+x)) (fl (b+y))) := by
  simp only [peerAddE, idealAdd2, ha, hb, bindRead, addEReal_coe, erealValue_coe, fl,
    pure, Except.pure]

private theorem prob_exec_cvt {t : TState} {i : Fin 16} {vl vh : Value} {x y : ℝ}
    (hl : t.regs (probExpReg i) = some vl) (hh : t.regs (probExpReg i + 1) = some vh)
    (hxl : valFloat .f32 vl = .ok x) (hxh : valFloat .f32 vh = .ok y) :
    execLocalA asms L g t (probCvtOp i) =
      .ok (PTX.next (setReg t (1115 + 3 * i.val) (Assumptions.bf16Pair x y))) := by
  have hc : Assumptions.cvtBf16x2.localRule L g t (probCvtOp i) =
      some (.ok (PTX.next (setReg t (1115 + 3 * i.val) (Assumptions.bf16Pair x y)))) := by
    simp [Assumptions.cvtBf16x2, probCvtOp, Assumptions.f32ValueOf, readValue, readReg, hl, hh,
      pure, Except.pure, hxl, hxh, Except.toOption]
  rw [execLocalA_noSegment (Proof.asms_segment_free t)]
  change (match [idealArith, approx, Assumptions.mulBf16x2, Assumptions.cvtBf16x2,
    Assumptions.cvtUe8m0, Assumptions.lg2Exact, Assumptions.ncReadOnly, paramPointers, storeDrain,
    Assumptions.sharedBits].findSome? (fun h => h.localRule L g t (probCvtOp i)) with
    | some r => r
    | none => execLocal L g t (probCvtOp i)) = _
  simp only [List.findSome?_cons,
    show idealArith.localRule L g t (probCvtOp i) = none from rfl,
    show approx.localRule L g t (probCvtOp i) = none from rfl,
    show Assumptions.mulBf16x2.localRule L g t (probCvtOp i) = none from rfl, hc]

private def probNegOp : Op := .float {
  op := .neg, ty := ty1 .f32, ftz := true, dsts := [some 1163], srcs := [.reg 2950] }

/-- The emitted scalar negation and pack supply the common bias to every score pair. -/
theorem run_probBias {t : TState} {F : List (Nat × Value)} {d : D}
    (hI : IdealAt asms (.neg .f32) L g t) (hat : At t 586 F) (hm : t.regs 2950 = some (miVal d))
    (hframe : ∀ q ∈ F, q.1 ≠ 1163 ∧ q.1 ≠ 3248) :
    ∃ u, run kernel asms L g 2 t = some u ∧ At u 588
      ((3248, joinValue (fl (-reference d)) (fl (-reference d))) :: F) := by
  let a := fl (-reference d)
  let v := PTX.next (setReg t 1163 a)
  have hv : run kernel asms L g 1 t = some v := by
    refine run_local (K := kernel) (op := probNegOp) Flow.code_586 rfl hat ?_
    apply hI _ (by rfl)
    have hm' := (OpndIs.reg (L := L) (g := g) hm).2
    rw [readEReal_of_valFloat (valFloat_miVal d)] at hm'
    simp [probNegOp, execIdealFloat, ty1, hm', bindRead, pure, Except.pure, ← EReal.coe_neg,
      erealValue_coe, fl, a, v]
  have hav : At v 587 F :=
    ⟨congrArg (·+1) hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1,
      holds_update hat.2.2.2.2 (fun q h => (hframe q h).1)⟩
  have hr : v.regs 1163 = some a := by simp [v, PTX.next, setReg]
  let u := PTX.next (setReg v 3248 (joinValue a a))
  have hu : run kernel asms L g 1 v = some u :=
    run_local (K := kernel) Flow.code_587 rfl hav
      (prob_exec_pack (by rw [hav.1]; decide) hr hr (by rfl) (by rfl))
  exact ⟨u, run_comp hv hu, congrArg (·+1) hav.1, hat.2.1, hat.2.2.1, hat.2.2.2.1,
    by simp [u, a, PTX.next, setReg], holds_update hav.2.2.2.2 (fun q h => (hframe q h).2)⟩

/-- Destination of the BF16 pair used by the P stores. -/
def probCvtReg (i : Fin 16) : Nat := 1115 + 3 * i.val

/-- All registers overwritten in the group, including the first zero and final sum halves. -/
def probWrites (i : Fin 16) : List Nat :=
  probHeadWrites i ++ [probSumReg i, probCvtReg i] ++
    (if i.val = 0 then [3244] else []) ++ (if i.val = 15 then [1196, 1197] else [])

private theorem prob_write {t : TState} {s r : Nat} {v : Value}
    {F : List (Nat × Value)} (ha : At t s F) (hn : ∀ q ∈ F, q.1 ≠ r) :
    At (PTX.next (setReg t r v)) (s + 1) ((r, v) :: F) :=
  ⟨congrArg (·+1) ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, by simp [PTX.next, setReg],
    holds_update ha.2.2.2.2 hn⟩

private theorem prob_zero {t : TState} {F : List (Nat × Value)} (ha : At t 593 F)
    (hn : ∀ q ∈ F, q.1 ≠ 3244) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 594 ((3244, b64 0) :: F) := by
  let m : MoveInstr := ⟨.scalar, .int .b 64, [some 3244], [.imm 0]⟩
  refine ⟨PTX.next (setReg t 3244 (b64 0)), ?_, prob_write ha hn⟩
  refine run_local (K := kernel) (op := .move m) Flow.code_593 rfl ha ?_
  have hn := none_probMove (L := L) (g := g) m (by rw [ha.1]; decide)
  rw [execLocalA_noSegment (Proof.asms_segment_free t), execLocalRule_of_none hn,
    execLocal_move (by rfl)]
  simp [m, execMove, readValue, readBits, DType.width, truncBits, Value.bytes, b64, bind,
    Except.bind, pure, Except.pure]

private theorem prob_sum {i : Fin 16} {t : TState} {F : List (Nat × Value)} {a b p q : ℝ}
    {va vb : Value} (hI : IdealAt asms .addRnF32x2 L g t) (hD : DeclineAt asms .addRnF32x2 L g t)
    (ha : At t (probSumSite i) F) (hprev : t.regs (probSumInput i) = some va)
    (hpair : t.regs (probPackReg i) = some vb)
    (hrprev : pairRead va = some (.ok ((a : EReal), (b : EReal))))
    (hrpair : pairRead vb = some (.ok ((p : EReal), (q : EReal))))
    (hn : ∀ x ∈ F, x.1 ≠ probSumReg i) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (probSumSite i + 1)
      ((probSumReg i, .pair (fl (a+p)) (fl (b+q))) :: F) := by
  refine ⟨PTX.next (setReg t (probSumReg i) (.pair (fl (a+p)) (fl (b+q)))), ?_,
    prob_write ha hn⟩
  refine run_local (K := kernel) (probTail_code i).1 rfl ha ?_
  rw [exec_peerAddE hI hD hprev hpair, peerAddE_fin hrprev hrpair]
  rfl

private theorem prob_convert {i : Fin 16} {t : TState} {F : List (Nat × Value)} {p q : ℝ}
    {vl vh : Value} (ha : At t (probCvtSite i) F) (hl : t.regs (probExpReg i) = some vl)
    (hh : t.regs (probExpReg i + 1) = some vh) (hvl : valFloat .f32 vl = .ok p)
    (hvh : valFloat .f32 vh = .ok q) (hn : ∀ x ∈ F, x.1 ≠ probCvtReg i) :
    ∃ u, run kernel asms L g 1 t = some u ∧
      At u (probCvtSite i + 1) ((probCvtReg i, Assumptions.bf16Pair p q) :: F) :=
  ⟨PTX.next (setReg t (probCvtReg i) (Assumptions.bf16Pair p q)),
    run_local (K := kernel) (probTail_code i).2 rfl ha (prob_exec_cvt hl hh hvl hvh),
    prob_write ha hn⟩

private theorem prob_unpackSum {t : TState} {F : List (Nat × Value)} {a b : ℝ} (ha : At t 700 F)
    (hr : t.regs 3305 = some (.pair (fl a) (fl b))) (hn : ∀ x ∈ F, x.1 ≠ 1196 ∧ x.1 ≠ 1197) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u 701 ((1196, fl a) :: (1197, fl b) :: F) := by
  let u := PTX.next (setReg (setReg t 1196 (fl a)) 1197 (fl b))
  refine ⟨u, ?_, congrArg (·+1) ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ?_, ?_, ?_⟩
  · refine run_local (K := kernel) Flow.code_700 rfl ha ?_
    exact prob_exec_unpack (by rw [ha.1]; decide) hr
      (by simp [unpackE, fl, Value.bytes, FloatFmt.bytes, splitValue])
  · simp [u, PTX.next, setReg]
  · simp [u, PTX.next, setReg]
  · exact holds_update
      (holds_update ha.2.2.2.2 (fun x hx => (hn x hx).1)) (fun x hx => (hn x hx).2)

private def probSumFacts (i : Fin 16) (x y : ℝ) : List (Nat × Value) :=
  if i.val = 15 then [(1196, fl x), (1197, fl y)]
  else [(probSumReg i, .pair (fl x) (fl y))]

/-- Execute one complete probability group, keeping the BF16 word and its two unrounded sums. -/
private theorem run_probGroup (i : Fin 16) (hI : ∀ t, IdealAt asms .fmaRnF32x2 L g t)
    (hD : ∀ t, DeclineAt asms .fmaRnF32x2 L g t) (hA : ∀ t, ApproxAt asms (.ex2 .f32) L g t)
    (hAD : ∀ t, ApproxDeclineAt asms (.ex2 .f32) L g t) (hSI : ∀ t, IdealAt asms .addRnF32x2 L g t)
    (hSD : ∀ t, DeclineAt asms .addRnF32x2 L g t) {t : TState} {F : List (Nat × Value)} {d : D}
    {x y p q : ℝ} (ha : At t (probSite i) F) (hsource : (probSource i, d.scoreSums i.val) ∈ F)
    (hscale : (3243, probScale L) ∈ F)
    (hbias : (3248, joinValue (fl (-reference d)) (fl (-reference d))) ∈ F)
    (hprev : i.val ≠ 0 → (probSumInput i, .pair (fl x) (fl y)) ∈ F)
    (hzero : i.val = 0 → x = 0 ∧ y = 0) (hp : probPair L d i.val = some (p, q))
    (hframe : ∀ z ∈ F, z.1 ∉ probWrites i) :
    ∃ u, run kernel asms L g (if i.val = 0 ∨ i.val = 15 then 8 else 7) t = some u ∧
      At u (probCvtSite i + 1)
        ((probCvtReg i, Assumptions.bf16Pair p q) :: probSumFacts i (x+p) (y+q) ++ F) := by
  obtain ⟨a, lo, hi, pl, ph, hfma, hun, hpl, hph, hvl, hvh⟩ := probPair_operands hp
  obtain ⟨v, hv, hav⟩ := run_probHead i hI hD hA hAD ha
    (holds_mem ha.2.2.2.2 hsource) (holds_mem ha.2.2.2.2 hscale) (holds_mem ha.2.2.2.2 hbias)
    hfma hun hpl hph (fun z hz hm => hframe z hz (by simp [probWrites, hm]))
  let G : List (Nat × Value) := [(probPackReg i, joinValue pl ph), (probExpReg i, pl),
    (probExpReg i+1, ph)] ++ F
  have hav : At v (probSite i + 5) G := hav
  have hpair : pairRead (joinValue pl ph) = some (.ok ((p : EReal), (q : EReal))) := by
    have hsplit := split_join_words (exp_scoreHalf hpl hvl) (exp_scoreHalf hph hvh)
    exact pairRead_of (by rw [hsplit]; exact hvl) (by rw [hsplit]; exact hvh)
  let sumV : Value := .pair (fl (x+p)) (fl (y+q))
  have hnSumExp : ∀ r ∈ [probPackReg i, probExpReg i, probExpReg i+1], r ≠ probSumReg i := by
    exact (by decide +kernel : ∀ j : Fin 16, ∀ r ∈
      [probPackReg j, probExpReg j, probExpReg j+1], r ≠ probSumReg j) i
  have hnCvtExp : ∀ r ∈ [probPackReg i, probExpReg i, probExpReg i+1, probSumReg i],
      r ≠ probCvtReg i := by
    exact (by decide +kernel : ∀ j : Fin 16, ∀ r ∈
      [probPackReg j, probExpReg j, probExpReg j+1, probSumReg j], r ≠ probCvtReg j) i
  have hnSum : ∀ z ∈ G, z.1 ≠ probSumReg i := by
    intro z hz
    simp only [G, List.cons_append, List.nil_append, List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | hz
    · exact hnSumExp _ (by simp)
    · exact hnSumExp _ (by simp)
    · exact hnSumExp _ (by simp)
    · exact fun he => hframe z hz (by simp [probWrites, he])
  have hnCvt : ∀ z ∈ (probSumReg i, sumV) :: G, z.1 ≠ probCvtReg i := by
    intro z hz
    simp only [G, List.cons_append, List.nil_append, List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | rfl | hz
    · exact hnCvtExp _ (by simp)
    · exact hnCvtExp _ (by simp)
    · exact hnCvtExp _ (by simp)
    · exact hnCvtExp _ (by simp)
    · exact fun he => hframe z hz (by simp [probWrites, he])
  have hsum : ∃ w, run kernel asms L g (if i.val = 0 then 7 else 6) t = some w ∧
      At w (probSumSite i + 1) ((probSumReg i, sumV) :: G) := by
    by_cases hz : i.val = 0
    · have hzi : i = 0 := Fin.ext hz
      subst i
      obtain ⟨rfl, rfl⟩ := hzero rfl
      have hzeroFrame : ∀ z ∈ G, z.1 ≠ 3244 := by
        intro z hz heq
        simp only [G, List.cons_append, List.nil_append, List.mem_cons] at hz
        rcases hz with rfl | rfl | rfl | hz
        · exact (by decide : probPackReg 0 ≠ 3244) heq
        · exact (by decide : probExpReg 0 ≠ 3244) heq
        · exact (by decide : probExpReg 0 + 1 ≠ 3244) heq
        · exact hframe z hz (by simp [probWrites, heq])
      obtain ⟨w, hw, haw⟩ := prob_zero hav hzeroFrame
      have hzeroPair : pairRead (b64 0) = some (.ok ((0 : ℝ), (0 : ℝ))) := by
        have h := pairRead_of (v := b64 0) valFloat_z0 valFloat_z0
        simpa using h
      obtain ⟨w', hw', haw'⟩ := prob_sum (i := 0) (hSI w) (hSD w) haw
        haw.2.2.2.2.1 haw.2.2.2.2.2.1 hzeroPair hpair (by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · change 3244 ≠ probSumReg 0; decide
          · exact hnSum z hz)
      refine ⟨w', run_comp (run_comp hv hw) hw', haw'.mono ?_⟩
      exact ⟨haw'.2.2.2.2.1, haw'.2.2.2.2.2.2⟩
    · have hsite : probSite i + 5 = probSumSite i := by simp [probSumSite, hz]
      have hav' : At v (probSumSite i) G := hsite ▸ hav
      have hpres := holds_mem hav.2.2.2.2 (List.mem_append_right _ (hprev hz))
      have hprevPair : pairRead (.pair (fl x) (fl y)) =
          some (.ok ((x : EReal), (y : EReal))) :=
        pairRead_of valFloat_float valFloat_float
      obtain ⟨w, hw, haw⟩ := prob_sum (hSI v) (hSD v) hav' hpres
        hav.2.2.2.2.1 hprevPair hpair hnSum
      exact ⟨w, by simpa [hz] using run_comp hv hw, haw⟩
  obtain ⟨w, hw, haw⟩ := hsum
  by_cases hlast : i.val = 15
  · have hifin : i = 15 := Fin.ext hlast
    subst i
    have hn : ∀ z ∈ (probSumReg 15, sumV) :: G, z.1 ≠ 1196 ∧ z.1 ≠ 1197 := by
      intro z hz
      simp only [G, List.cons_append, List.nil_append, List.mem_cons] at hz
      rcases hz with rfl | rfl | rfl | rfl | hz
      · change probSumReg 15 ≠ 1196 ∧ probSumReg 15 ≠ 1197; decide
      · change probPackReg 15 ≠ 1196 ∧ probPackReg 15 ≠ 1197; decide
      · change probExpReg 15 ≠ 1196 ∧ probExpReg 15 ≠ 1197; decide
      · change probExpReg 15 + 1 ≠ 1196 ∧ probExpReg 15 + 1 ≠ 1197; decide
      · exact ⟨fun he => hframe z hz (by simp [probWrites, he]),
          fun he => hframe z hz (by simp [probWrites, he])⟩
    obtain ⟨w', hw', haw'⟩ := prob_unpackSum haw haw.2.2.2.2.1 hn
    have hn' : ∀ z ∈ (1196, fl (x+p)) :: (1197, fl (y+q)) :: (probSumReg 15, sumV) :: G,
        z.1 ≠ probCvtReg 15 := by
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · change 1196 ≠ probCvtReg 15; decide
      rcases List.mem_cons.mp hz with rfl | hz
      · change 1197 ≠ probCvtReg 15; decide
      exact hnCvt z hz
    obtain ⟨u, hu, hau⟩ := prob_convert (i := 15) haw'
      haw'.2.2.2.2.2.2.2.2.1 haw'.2.2.2.2.2.2.2.2.2.1 hvl hvh hn'
    refine ⟨u, run_comp (run_comp hw hw') hu, hau.mono ?_⟩
    exact ⟨hau.2.2.2.2.1, hau.2.2.2.2.2.1, hau.2.2.2.2.2.2.1,
      hau.2.2.2.2.2.2.2.2.2.2.2⟩
  · have hsite : probSumSite i + 1 = probCvtSite i := by simp [probCvtSite, hlast]
    have haw' : At w (probCvtSite i) ((probSumReg i, sumV) :: G) := hsite ▸ haw
    obtain ⟨u, hu, hau⟩ := prob_convert haw'
      haw.2.2.2.2.2.2.1 haw.2.2.2.2.2.2.2.1 hvl hvh hnCvt
    refine ⟨u, ?_, hau.mono ?_⟩
    · simp only [hlast, or_false]
      split_ifs with hz
      · exact run_comp (by simpa [hz] using hw) hu
      · exact run_comp (by simpa [hz] using hw) hu
    · simpa only [probSumFacts, hlast, ite_false, List.cons_append, List.nil_append,
        holds_cons, sumV] using
        (show u.regs (probCvtReg i) = some (Assumptions.bf16Pair p q) ∧
          u.regs (probSumReg i) = some sumV ∧ Holds u.regs F from
          ⟨hau.2.2.2.2.1, hau.2.2.2.2.2.1, hau.2.2.2.2.2.2.2.2.2⟩)

private theorem mapM_prob_at {α β : Type} {f : α → Option β}
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ys.length = xs.length ∧ ∀ (i : Nat) a, xs[i]? = some a →
      ∃ b, ys[i]? = some b ∧ f a = some b := by
  induction xs generalizing ys with
  | nil => simp_all
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, rest, hrest, rfl⟩ := h
    obtain ⟨hlen, hget⟩ := ih hrest
    refine ⟨by simpa, ?_⟩
    intro i x hx
    cases i with
    | zero =>
      have hax : a = x := Option.some.inj hx
      subst x
      exact ⟨b, rfl, hb⟩
    | succ i => simpa using hget i x (by simpa using hx)

private def probLo (ps : List (ℝ × ℝ)) (n : Nat) : ℝ := ((ps.take n).map Prod.fst).sum
private def probHi (ps : List (ℝ × ℝ)) (n : Nat) : ℝ := ((ps.take n).map Prod.snd).sum

private theorem probSum_next {ps : List (ℝ × ℝ)} {n : Nat} (hn : n < ps.length) :
    probLo ps (n+1) = probLo ps n + ps[n].1 ∧
      probHi ps (n+1) = probHi ps n + ps[n].2 := by
  simp only [probLo, probHi, List.take_succ_eq_append_getElem hn, List.map_append, List.map_cons,
    List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero, and_self]

private def probPackedFacts (ps : List (ℝ × ℝ)) (n : Nat) : List (Nat × Value) :=
  (List.range n).map fun j =>
    let v := ps.getD j (0, 0)
    (1115 + 3*j, Assumptions.bf16Pair v.1 v.2)

private def probAccum (ps : List (ℝ × ℝ)) (n : Nat) : List (Nat × Value) :=
  if n = 0 then []
  else probSumFacts (Fin.ofNat 16 (n-1)) (probLo ps n) (probHi ps n)

private def probBoundary (n : Nat) : Nat :=
  n * 7 + (if n = 0 then 0 else if n = 16 then 2 else 1)

private theorem probBoundary_site (i : Fin 16) : probSite i = 588 + probBoundary i.val := by
  fin_cases i <;> rfl

private theorem probBoundary_next (i : Fin 16) :
    probCvtSite i + 1 = 588 + probBoundary (i.val + 1) ∧
      probBoundary (i.val + 1) = probBoundary i.val +
        (if i.val = 0 ∨ i.val = 15 then 8 else 7) := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

private def probLive : List Nat := (Flow.live 586).filter tracked.contains

private def probStable (P : Params) (L : Launch) (g : Nat) (d : D) :
    List (Nat × Value) :=
  (3248, joinValue (fl (-reference d)) (fl (-reference d))) ::
    factsFrom probLive (valueOf P L g d)

private theorem probStable_value {P : Params} {L : Launch} {g : Nat} {d : D} {r : Nat}
    (hr : r ∈ probLive) : (r, valueOf P L g d r) ∈ probStable P L g d :=
  List.mem_cons_of_mem _ (mem_factsFrom hr)

private theorem probSource_val (P : Params) (L : Launch) (g : Nat) (d : D) (i : Fin 16) :
    valueOf P L g d (probSource i) = d.scoreSums i.val := by
  fin_cases i <;> rfl

private theorem probWrites_stable (i : Fin 16) :
    ∀ r ∈ 3248 :: probLive, r ∉ probWrites i :=
  (by decide +kernel : ∀ j : Fin 16, ∀ r ∈ 3248 :: probLive, r ∉ probWrites j) i

private theorem probWrites_prior (i j : Fin 16) (h : j.val < i.val) :
    probCvtReg j ∉ probWrites i :=
  (by decide +kernel : ∀ k t : Fin 16, t.val < k.val → probCvtReg t ∉ probWrites k) i j h

private theorem probAccum_frame (i : Fin 16) (ps : List (ℝ × ℝ)) {z : Nat × Value}
    (hz : z ∈ probAccum ps i.val) : z.1 ∉ probWrites i := by
  by_cases h : i.val = 0
  · simp [probAccum, h] at hz
  · have hm : (Fin.ofNat 16 (i.val-1)).val ≠ 15 := by
      have hi := i.isLt
      change (i.val-1) % 16 ≠ 15
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [probAccum, probSumFacts, h, hm, ↓reduceIte, List.mem_singleton] at hz
    subst z
    exact (by decide +kernel : ∀ j : Fin 16, j.val ≠ 0 →
      probSumReg (Fin.ofNat 16 (j.val-1)) ∉ probWrites j) i h

/-- Run the sixteen packed probability groups and preserve the two lane sums until their join. -/
private theorem run_probGroups {P : Params} {L : Launch} {g : Nat} {d : D} {t : TState}
    {ps : List (ℝ × ℝ)} (hlen : ps.length = 16)
    (hp : ∀ i : Fin 16, probPair L d i.val = some (ps.getD i.val (0, 0)))
    (ha : At t 588 (probStable P L g d)) (n : Nat) (hn : n ≤ 16) :
    ∃ u, run kernel asms L g (probBoundary n) t = some u ∧
      At u (588 + probBoundary n)
        (probAccum ps n ++ probPackedFacts ps n ++ probStable P L g d) := by
  induction n with
  | zero => exact ⟨t, rfl, ha⟩
  | succ n ih =>
    let i : Fin 16 := ⟨n, by omega⟩
    obtain ⟨v, hv, hav⟩ := ih (by omega)
    let F := probAccum ps n ++ probPackedFacts ps n ++ probStable P L g d
    have hsource : (probSource i, d.scoreSums i.val) ∈ F := by
      apply List.mem_append_right
      rw [← probSource_val P L g d]
      apply probStable_value
      exact (by decide +kernel : ∀ j : Fin 16, probSource j ∈ probLive) i
    have hscale : (3243, probScale L) ∈ F :=
      List.mem_append_right _ (probStable_value (by decide +kernel : 3243 ∈ probLive))
    have hbias : (3248, joinValue (fl (-reference d)) (fl (-reference d))) ∈ F :=
      List.mem_append_right _ (by simp [probStable])
    have hprev (hz : i.val ≠ 0) :
        (probSumInput i, .pair (fl (probLo ps n)) (fl (probHi ps n))) ∈ F := by
      have hsub : n - 1 < 16 := by omega
      have hmod : (Fin.ofNat 16 (n-1)).val = n - 1 := Nat.mod_eq_of_lt hsub
      have he : Fin.ofNat 16 (n-1) = ⟨i.val - 1, by have := i.isLt; omega⟩ := Fin.ext hmod
      have hn0 : n ≠ 0 := hz
      apply List.mem_append_left
      apply List.mem_append_left
      rw [probSumInput, ite_eq_right hz, ← he, probAccum, ite_eq_right hn0, probSumFacts, hmod,
        ite_eq_right (show n - 1 ≠ 15 by omega)]
      exact List.mem_cons_self
    have hframe : ∀ z ∈ F, z.1 ∉ probWrites i := by
      intro z hz
      simp only [F, List.mem_append] at hz
      rcases hz with (hz | hz) | hz
      · exact probAccum_frame i ps hz
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
        exact probWrites_prior i ⟨j, by have := List.mem_range.mp hj; omega⟩ (List.mem_range.mp hj)
      · apply probWrites_stable i
        simp only [probStable, List.mem_cons] at hz ⊢
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
          exact Or.inr hr
    have hat : At v (probSite i) F := (probBoundary_site i).symm ▸ hav
    let pair := ps.getD n (0, 0)
    obtain ⟨u, hu, hau⟩ := run_probGroup i
      (fun _ => vote_idealAt (by simp [voteFloatForms]))
      (fun _ => vote_declineAt (by simp [voteFloatForms]))
      (vote_ex2.1 L g) (vote_ex2.2 L g)
      (fun _ => vote_idealAt (by simp [voteFloatForms]))
      (fun _ => vote_declineAt (by simp [voteFloatForms]))
      hat hsource hscale hbias hprev (by
        intro hz
        change n = 0 at hz
        simp [hz, probLo, probHi]) (show probPair L d i.val = some (pair.1, pair.2) from hp i)
      hframe
    refine ⟨u, ?_, ?_⟩
    · have hr := run_comp hv hu
      rw [(probBoundary_next i).2]
      exact hr
    · rw [← (probBoundary_next i).1]
      apply hau.mono
      have hpacks :
          Holds u.regs (probPackedFacts ps n) ∧ Holds u.regs (probStable P L g d) := by
        have hh := (holds_append u.regs (probSumFacts i _ _) F).mp hau.2.2.2.2.2
        exact (holds_append u.regs (probAccum ps n ++ probPackedFacts ps n)
          (probStable P L g d)).mp hh.2 |>.imp_left
            (fun h => (holds_append u.regs _ _).mp h |>.2)
      have hlt : n < ps.length := by omega
      have hget : pair = ps[n] := by simp [pair, hlt]
      have hnext (i : Fin 16) : Fin.ofNat 16 (i.val+1-1) = i := by
        apply Fin.ext
        simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
      rw [holds_append, holds_append]
      refine ⟨⟨?_, ?_⟩, hpacks.2⟩
      · rw [probAccum, ite_eq_right (Nat.succ_ne_zero n),
          show n+1 = i.val+1 from rfl, hnext i, (probSum_next hlt).1, (probSum_next hlt).2,
          ← hget]
        exact ((holds_append u.regs _ _).mp hau.2.2.2.2.2).1
      · rw [probPackedFacts, List.range_succ, List.map_append, holds_append]
        exact ⟨hpacks.1, hau.2.2.2.2.1, trivial⟩

private theorem run_probFinish {d : D} {t : TState} {F : List (Nat × Value)} {x y gain : ℝ}
    (ha : At t 702 ((1196, fl x) :: (1197, fl y) :: F)) (hs : (2955, halfSumVal d) ∈ F)
    (hg : (2951, d.gainWord) ∈ F) (hv : valFloat .f32 d.gainWord = .ok gain) :
    ∃ u, run kernel asms L g 2 t = some u ∧ u.pc = 704 ∧ u.sub = 0 ∧ u.acc = [] ∧
      u.fault = none ∧ u.regs 2955 = some (fl ((if d.sumUpd then d.lh else 0)*gain + (x+y))) ∧
      ∀ r v, (r, v) ∈ F → r ≠ 1198 → r ≠ 2955 → u.regs r = some v := by
  let v := PTX.next (setReg t 1198 (fl (x+y)))
  have hrun : run kernel asms L g 1 t = some v := by
    refine run_local (K := kernel) Flow.code_702 rfl ha ?_
    rw [exec_floatE_add (fun _ _ _ => vote_idealAt (by simp [voteFloatForms]))
      (fun _ _ _ => vote_declineAt (by simp [voteFloatForms]))
      (OpndIs.reg ha.2.2.2.2.1) (OpndIs.reg ha.2.2.2.2.2.1),
      floatE_add_fin (va := fl x) (vb := fl y) valFloat_float valFloat_float]
    rfl
  have hav : At v 703 [] :=
    ⟨congrArg (·+1) ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, trivial⟩
  have hsr : v.regs 2955 = some (halfSumVal d) := by
    simpa [v, PTX.next, setReg] using holds_mem ha.2.2.2.2.2.2 hs
  have hgr : v.regs 2951 = some d.gainWord := by
    simpa [v, PTX.next, setReg] using holds_mem ha.2.2.2.2.2.2 hg
  have hxy : v.regs 1198 = some (fl (x+y)) := by simp [v, PTX.next, setReg]
  have hsval : valFloat .f32 (halfSumVal d) = .ok (if d.sumUpd then d.lh else 0) := by
    cases h : d.sumUpd <;> simp [halfSumVal, h, fl, valFloat_float, valFloat_z0]
  let u := PTX.next (setReg v 2955 (fl ((if d.sumUpd then d.lh else 0)*gain + (x+y))))
  have hru : run kernel asms L g 1 v = some u := by
    refine run_local (K := kernel) Flow.code_703 rfl hav ?_
    rw [exec_floatE_fma (fun _ _ _ => vote_idealAt (by simp [voteFloatForms]))
      (fun _ _ _ => vote_declineAt (by simp [voteFloatForms]))
      (OpndIs.reg hsr) (OpndIs.reg hgr) (OpndIs.reg hxy),
      floatE_fma_fin (vc := fl (x+y)) hsval hv valFloat_float]
    rfl
  refine ⟨u, run_comp hrun hru, congrArg (·+1) hav.1, ha.2.1, ha.2.2.1, ha.2.2.2.1,
    by simp [u, PTX.next, setReg], ?_⟩
  intro r val hm h₁ h₂
  simpa [u, v, PTX.next, setReg, Function.update_of_ne h₁, Function.update_of_ne h₂] using
    holds_mem ha.2.2.2.2.2.2 hm
end

private def probUntouched : List Nat :=
  [110, 451, 452, 459, 460, 463, 465, 467, 469, 471, 472, 474, 475, 476, 478,
   988, 989, 990, 991, 992, 993, 994, 995, 996, 1715, 2880, 2883, 2884, 2885,
   2950, 2951, 2952, 2953, 2991, 2992, 2993, 2994, 2995, 2996, 2997, 2998, 2999, 3001, 3243]

private def probResult (L : Launch) (g : Nat) (d : D) (ps : List (ℝ × ℝ)) (gain : ℝ) : D :=
  let first := 32 * half L g
  { d with
    sumUpd := true
    lh := (if d.sumUpd then d.lh else 0)*gain +
      ((ps.map Prod.fst).sum + (ps.map Prod.snd).sum)
    pw := fun h slot => if h = head L g ∧ first ≤ slot ∧ slot < first + 32 then
      let i := slot-first
      let p := ps.getD (i/2) (0, 0)
      if i % 2 = 0 then p.1 else p.2
    else d.pw h slot }

private theorem probResult_packed (L : Launch) (g : Nat) (d : D)
    (ps : List (ℝ × ℝ)) (gain : ℝ) (i : Fin 16) :
    pPacked L g (probResult L g d ps gain) i.val =
      Assumptions.bf16Pair (ps.getD i.val (0, 0)).1 (ps.getD i.val (0, 0)).2 := by
  have hi := i.isLt
  have h₁ : 32 * half L g + 2 * i.val < 32 * half L g + 32 := by omega
  have h₂ : 32 * half L g + 2 * i.val + 1 < 32 * half L g + 32 := by omega
  have h₃ : 32 * half L g ≤ 32 * half L g + 2 * i.val := by omega
  have h₄ : 32 * half L g ≤ 32 * half L g + 2 * i.val + 1 := by omega
  have h₅ : 32 * half L g + 2 * i.val - 32 * half L g = 2 * i.val := by omega
  have h₆ : 32 * half L g + 2 * i.val + 1 - 32 * half L g = 2 * i.val + 1 := by omega
  simp [pPacked, probResult, h₁, h₂, h₃, h₄, h₅, h₆,
    show (2*i.val+1) / 2 = i.val by omega, show (2*i.val+1) % 2 = 1 by omega]

private theorem probResult_untouched (P : Params) (L : Launch) (g : Nat) (d : D)
    (ps : List (ℝ × ℝ)) (gain : ℝ) {r : Nat} (hr : r ∈ probUntouched) :
    valueOf P L g { probResult L g d ps gain with
        site := .pStore 0, rescale := wantsRescale d } r = valueOf P L g d r := by
  simp only [probUntouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals rfl

/-- A successful probability transition runs the actual 118 local instructions to the P store. -/
theorem run_probabilityUpdate {P : Params} {L : Launch} {g : Nat} {d d' : D} {t : TState}
    (hp : probabilityUpdate L g d = some d')
    (hat : At t 586 (factsFrom ((Flow.live 586).filter tracked.contains) (valueOf P L g d))) :
    ∃ u, run kernel asms L g 118 t = some u ∧
      At u 704 (facts P L g { d' with site := .pStore 0, rescale := wantsRescale d' }) := by
  simp only [probabilityUpdate, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hp
  obtain ⟨ps, hps, gain, hgv, rfl⟩ := hp
  change (valFloat .f32 d.gainWord).toOption = some gain at hgv
  have hg := option_of_except_some hgv
  let d' := probResult L g d ps gain
  change ∃ u, run kernel asms L g 118 t = some u ∧
    At u 704 (facts P L g { d' with site := .pStore 0, rescale := wantsRescale d' })
  obtain ⟨hlen, hget⟩ := mapM_prob_at hps
  have hlen : ps.length = 16 := by simpa using hlen
  have hpair (i : Fin 16) : probPair L d i.val = some (ps.getD i.val (0, 0)) := by
    have hi : i.val < (List.finRange 16).length := by simp
    have he : (List.finRange 16)[i.val]? = some i := by
      rw [List.getElem?_eq_getElem hi, List.getElem_finRange]
      rfl
    obtain ⟨p, hp, h⟩ := hget i.val i he
    simpa [List.getD, hp] using h
  have hmi := holds_mem hat.2.2.2.2 (mem_factsFrom (by decide +kernel : 2950 ∈ probLive))
  obtain ⟨v, hv, hav⟩ := run_probBias (vote_idealAt (by simp [voteFloatForms])) hat hmi (by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    exact (by decide +kernel : ∀ r ∈ probLive, r ≠ 1163 ∧ r ≠ 3248) r hr)
  have hav : At v 588 (probStable P L g d) := hav
  obtain ⟨w, hw, haw⟩ := run_probGroups hlen hpair hav 16 (by decide)
  let F := probPackedFacts ps 16 ++ probStable P L g d
  have haw : At w 702 ((1196, fl (probLo ps 16)) :: (1197, fl (probHi ps 16)) :: F) := haw
  have hs : (2955, halfSumVal d) ∈ F :=
    List.mem_append_right _ (probStable_value (by decide +kernel : 2955 ∈ probLive))
  have hgv : (2951, d.gainWord) ∈ F :=
    List.mem_append_right _ (probStable_value (by decide +kernel : 2951 ∈ probLive))
  obtain ⟨u, hu, hpc, hsub, hacc, hflt, hsum, hframe⟩ := run_probFinish haw hs hgv hg
  refine ⟨u, run_comp (run_comp hv hw) hu, hpc, hsub, hacc, hflt, ?_⟩
  refine holds_of_pointwise fun r hr => ?_
  change r ∈ (Flow.live 704).filter tracked.contains at hr
  have hcases : r = 2955 ∨ r ∈ (List.finRange 16).map probCvtReg ∨
      r ∈ probUntouched ∧ r ∈ probLive ∧ r ≠ 1198 ∧ r ≠ 2955 :=
    (by decide +kernel : ∀ r ∈ (Flow.live 704).filter tracked.contains,
      r = 2955 ∨ r ∈ (List.finRange 16).map probCvtReg ∨
        r ∈ probUntouched ∧ r ∈ probLive ∧ r ≠ 1198 ∧ r ≠ 2955) r hr
  rcases hcases with rfl | hc | ⟨hc, hl, h₁, h₂⟩
  · have htake : ps.take 16 = ps := List.take_of_length_le hlen.le
    change u.regs 2955 = some (halfSumVal d')
    simpa [d', halfSumVal, probResult, probLo, probHi, htake] using hsum
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    have hvalue (d : D) : valueOf P L g d (probCvtReg i) = pPacked L g d i.val := by
      fin_cases i <;> rfl
    rw [hvalue]
    change u.regs (probCvtReg i) = some (pPacked L g d' i.val)
    rw [probResult_packed]
    apply hframe
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩
    · fin_cases i <;> decide
    · fin_cases i <;> decide
  · change u.regs r = some (valueOf P L g { d' with
      site := .pStore 0, rescale := wantsRescale d' } r)
    rw [show wantsRescale d' = wantsRescale d from rfl, probResult_untouched P L g d ps gain hc]
    exact hframe r (valueOf P L g d r) (List.mem_append_right _ (probStable_value hl)) h₁ h₂

/-- The collective reference vote is followed by the emitted probability arithmetic. -/
theorem step_rescaleVote {P : Params} {L : Launch} {g : Nat} (d : D)
    (hd : d.site = .rescaleVote) : (code P L g).StepAt d :=
  stepAt_of P L g d fun {t : TState} {e : Event} {u : TState} ins hat hi hc hf => by
    obtain ⟨r, he, hu⟩ := fires_rescaleVote hd hat hc hf
    have hsub : d.sub = 0 := by simpa [hd, Site.elems] using hi.subLt
    simp only [next, nextSite, hd, he]
    cases hr : afterReferenceVote d r with
    | none => exact .inl (.inl rfl)
    | some d₀ =>
      simp only [Option.bind_some]
      cases hp : probabilityUpdate L g { d₀ with voteTaken := r } with
      | none => exact .inl (.inl rfl)
      | some d₁ =>
        let d' := { d₁ with site := .pStore 0, rescale := wantsRescale d₁ }
        obtain ⟨v, hv, hav⟩ := run_afterReferenceVote hd hat hi hr hu
        obtain ⟨w, hw, haw⟩ := run_probabilityUpdate hp hav
        have hd₀ := afterReferenceVote_fields hr
        have hd₁ : d₁ = { d₀ with
            voteTaken := r, sumUpd := d₁.sumUpd, lh := d₁.lh, pw := d₁.pw } := by
          simp only [probabilityUpdate, bind, Option.bind_eq_some_iff, pure,
            Option.some.injEq] at hp
          obtain ⟨_, _, _, _, rfl⟩ := hp
          rfl
        have hsub' : d'.sub = 0 := by
          change d₁.sub = 0
          rw [hd₁, hd₀]
          exact hsub
        refine .inl (.inr ⟨d', w, rfl, run_rtg (run_comp hv hw), ?_, ?_⟩)
        · exact ⟨haw.1, haw.2.1.trans hsub'.symm,
            haw.2.2.1.trans (siteAcc_nil d' hsub').symm, haw.2.2.2.1, haw.2.2.2.2⟩
        · unfold d'
          rw [hd₁, hd₀]
          refine { hi with
            epilogueLast := ?_, rescaleArm := ?_, subLt := ?_, armSite := ?_
            exitWarp := ?_, preloop := ?_, rowTotal := ?_, exchangeWords := ?_ }
          all_goals simp [Site.inEpilogue, Site.inRescale, Site.elems, hsub]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
