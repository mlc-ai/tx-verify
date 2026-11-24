-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.BrEntry
public import Lemmas.Flow.Recip

@[expose] public section

/-! # The bridge from the softmax loop to the epilogue

`bridge`: from the facts of pc 2560 (`exitFacts i`, the registers the softmax loop leaves) the
thread, if neither `lg2.approx.ftz.f32` (pc 2562) nor `fma.rn.f32` (pc 2563) faults
(`In.NoFault`), reaches the epilogue's poll of `o_final` (pc 2565, an event) with the facts the
epilogue's machine needs, `entryFacts (prm i) i.skip`, where `prm i` is the epilogue's `Prm` and
`i.skip` (`%p173`, `num_iters < 1`) its flag. Every thread polls (the second kernel fix): the
branch on `%p173` is after the poll, in the epilogue (`Epi.step_wait`).

Where a float step faults, the thread is dead (`Machine.Dead`): the kernel's theorems exclude
it. The five instructions of pcs 2560-2564 are all local; the run has 5 steps.

## What the softmax region must provide

1. **The facts of pc 2560** (`At t 2560 (exitFacts i)`): the registers live there hold the values
   `valueB i` gives them: `%p3` (id 3) `.pred p3`, `%p175` (175) `.pred rv`, `%r1` (462)
   `b32 tid`, `%r2` (463) `b32 tm`, `%r3` (464) `b32 w`, `%r17` (478) `b32 b`, `%r25` (486)
   `b32 n` (`num_iters`), `%r30` (491) `b32 c0`, `%r35` (496) `b32 c`, `%r36` (497) `b32 e`,
   `%r37` (498) `sc` (`scale_log2`), `%r72` (533) `b32 a`, `%r149` (610) `b32 dd`, `%r163`
   (624) `b32 mb`, `%r1453` (1914) `mx` (the row maximum), `%r1454` (1915) `l` (the row sum),
   `%rd8` (1956) `b64 d0`, `%rd75` (2023) `b64 ob`, `%rd76` (2024) `b64 lb`. This is the
   epilogue's `Prm` (`Epi.Prm`) with `%r25`, `%r37`, `%r1453` added; `lse` is computed here,
   not inherited.
2. **`In.Ok`**: the numbers are below `2^32` (`2^64` for the `%rd`), the warp index is below 4,
   the output row index `(((a * b + c) + dd) * 12 + e)` (mod `2^32`) is below `2^24`, and the row
   sum is a four-byte value.
3. **`In.NoFault`**: neither float step of the bridge faults. `lse_fin` proves it, with
   `lse = sc * mx + log2 l`, when `l` is a positive finite number and `sc`, `mx` are finite
   numbers; `lse_empty` proves it for an empty row (`l = 0`, `mx = -inf`), and `nofault_of_row`
   combines the two. `prm_setpOk` and `prm_rcpOk` give the epilogue's premises (the zero test
   and the reciprocal do not fault) for every finite `l`, zero included.

`bridge_premises` assembles the epilogue's `Premises (prm i) i.skip`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Br
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Epi

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-! ### The numbers -/

/-- The epilogue's numbers of the bridge's state. -/
theorem prm_ok (i : In) (hok : i.Ok) : (prm i).Ok where
  tid := hok.tid
  tm := hok.tm
  w := hok.w
  c0 := hok.c0
  mb := hok.mb
  a := hok.a
  b := hok.b
  c := hok.c
  dd := hok.dd
  e := hok.e
  d0 := hok.d0
  ob := hok.ob
  lb := hok.lb
  row := hok.row
  l := hok.l
  lse := okVal_bytes (floatE_fma_four .rn false _)
  mb8 := hok.mb8
  ob4 := hok.ob4
  lb4 := hok.lb4
  c0col := hok.c0col

/-! ### The bridge -/

theorem bridge_seg (i : In) (hok : i.Ok) :
    SegD kernel asms L g 5 2560 (exitFacts i) 2565 (bfacts 2565 i) i.NoFault := by
  have s1 := SegD.seg_comp (seg_test (L := L) (g := g) i hok) (seg_lg2 i)
  have s2 := SegD.comp s1 (seg_fma i)
  have s3 := SegD.comp_seg s2 (seg_zero i)
  exact (SegD.of_len s3 rfl).iff (by simp [In.NoFault])

/-- **The bridge.** From the facts of pc 2560 the thread reaches the epilogue's poll of `o_final`
(pc 2565) with the epilogue's entry facts, whether `num_iters >= 1` or not (`i.skip` is the
epilogue's flag); where a float step of the bridge faults, the thread is dead. -/
theorem bridge (i : In) (hok : i.Ok) {t : TState} (h : At t 2560 (exitFacts i)) :
    (i.NoFault → ∃ t', Relation.ReflTransGen (Tau kernel asms L g) t t' ∧
      At t' 2565 (entryFacts (prm i) i.skip)) ∧
    (¬ i.NoFault → Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) t) := by
  obtain ⟨hrun, hdead⟩ := bridge_seg (L := L) (g := g) i hok t h
  refine ⟨fun hnf => ?_, hdead⟩
  obtain ⟨t', hr, ht'⟩ := hrun hnf
  exact ⟨t', run_rtg hr, ht'.mono (entry_of_facts i ht'.2.2.2.2)⟩

/-! ### The values on numbers -/

/-- **The log-sum-exp of numbers**: for a positive finite row sum and a finite scale and maximum
the bridge does not fault, `%r1298` is `log2 l` and `%r63` the number `sc * mx + log2 l`. -/
theorem lse_fin (i : In) {x s m : ℝ} (hx : valFloat .f32 i.l = .ok x) (hpos : 0 < x)
    (hs : valFloat .f32 i.sc = .ok s) (hm : valFloat .f32 i.mx = .ok m) :
    i.NoFault ∧ i.lg2v = .float .f32 (Real.logb 2 x) ∧
      i.lse = .float .f32 (s * m + Real.logb 2 x) := by
  have hl : lg2E i.l = .ok (.float .f32 (Real.logb 2 x)) := by
    unfold lg2E
    rw [readEReal_of_valFloat hx]
    have h1 : (0 : EReal) < (x : EReal) := EReal.coe_pos.mpr hpos
    simp [h1, EReal.coe_ne_top]
  have hv : i.lg2v = .float .f32 (Real.logb 2 x) := by simp [In.lg2v, hl, okVal]
  have hf : floatE lseI [i.sc, i.mx, i.lg2v] = .ok (.float .f32 (s * m + Real.logb 2 x)) :=
    floatE_fma_fin hs hm (hv ▸ valFloat_float)
  refine ⟨⟨by rw [hl]; rfl, by rw [hf]; rfl⟩, hv, ?_⟩
  simp [In.lse, hf, okVal]

/-- **A finite row sum** (zero included) makes the zero test a comparison of numbers, so that it
does not fault: the epilogue's `Prm.setpOk`. -/
theorem prm_setpOk (i : In) {x : ℝ} (hx : valFloat .f32 i.l = .ok x) : (prm i).setpOk = true := by
  have h3 : setpE (.unord .eq) false i.l zero32 =
      .ok (erealCompare .eq (x : EReal) ((0 : ℝ) : EReal)) :=
    setpE_fin (Or.inr rfl) hx valFloat_zero
  show (setpE (.unord .eq) false i.l zero32).toBool = true
  rw [h3]
  rfl

/-- **A finite row sum** (zero included) makes the zero test a comparison of numbers, so that the
reciprocal of the selected value does not fault: the epilogue's `Prm.rcpOk`. -/
theorem prm_rcpOk (i : In) {x : ℝ} (hx : valFloat .f32 i.l = .ok x) : (prm i).rcpOk = true := by
  have h3 : setpE (.unord .eq) false i.l zero32 =
      .ok (erealCompare .eq (x : EReal) ((0 : ℝ) : EReal)) :=
    setpE_fin (Or.inr rfl) hx valFloat_zero
  have e : i.eq0 = decide (x = 0) := by
    simp only [In.eq0, h3, erealCompare, EReal.coe_eq_coe_iff]
  show (rcpE true (if i.eq0 then one32 else i.l)).toBool = true
  by_cases h0 : x = 0
  · simp only [e, h0, decide_true, ite_true]
    rw [show one32 = .bits 32 (BitVec.ofNat 64 1065353216) from rfl,
      rcpE_fin valFloat_one one_ne_zero]
    rfl
  · simp only [e, h0, decide_false, Bool.false_eq_true, ite_false]
    rw [rcpE_fin hx h0]
    rfl

/-! ### The epilogue's entry -/

end
end PTX.Kernels.InklingRelDecode.Proof.Br
