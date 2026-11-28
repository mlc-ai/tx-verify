-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
import Kernels.InklingRelDecode.Gen.EpiPack
import Kernels.InklingRelDecode.Gen.EpiOut
public import Kernels.InklingRelDecode.Proof.Lib.WinBack
import Lemmas.Flow.OutRunCond
import Lemmas.Flow.Mul2NVal

@[expose] public section

/-! # The epilogue's products: packs and packed multiplications

From the state at pc 2609 (after the wait for the accumulator load) the 33 packs of the words and
the reciprocal and the 32 packed products reach pc 2674 with the register `2479 + m` holding the
pair of the products of the reciprocal with the words `2 m` and `2 m + 1`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib
open Softmax.Gen Epilogue.Gen

noncomputable section
variable {L : Launch} {g : Nat}

private def epkDom : List Nat := 1761 :: (List.range 64).map (1763 + ·)
private def epmDom : List Nat := (List.range 32).map (2346 + ·) ++ [2378]

private theorem epk_f0 (V : Nat → Value) : epk_facts0 V = factsFrom epkDom V := by kernel_rfl

private theorem epm_f0 (V : Nat → Value) : epm_facts0 V = factsFrom epmDom V := by kernel_rfl

private theorem epk_pair (V : Nat → Value) : ∀ j < 32,
    xFinal (lookupD (epk_facts0 V)) epk_items0 (2346 + j) =
      joinValue (V (1763 + 2 * j)) (V (1764 + 2 * j)) := by
  intro j hj
  interval_cases j <;> kernel_rfl

private theorem epk_rcp (V : Nat → Value) :
    xFinal (lookupD (epk_facts0 V)) epk_items0 2378 = joinValue (V 1761) (V 1761) := by
  kernel_rfl

private theorem epm_prod (V : Nat → Value) : ∀ m < 32,
    xFinal (lookupD (epm_facts0 V)) epm_items0 (2479 + m) =
      okVal (.bits 32 0) (fF mul2NL [.reg 2378, .reg (2346 + m)] [V 2378, V (2346 + m)]) := by
  intro m hm
  interval_cases m <;> kernel_rfl

private theorem epk_reads : xReadsB epkDom epk_items0 = true := by decide +kernel
private theorem epk_local : xLocalB epk_items0 = true := by decide +kernel
private theorem epk_req (V : Nat → Value) : xReq V epk_items0 = true := by rfl
private theorem epm_reads : xReadsB epmDom epm_items0 = true := by decide +kernel
private theorem epm_local : xLocalB epm_items0 = true := by decide +kernel
private theorem epm_req (V : Nat → Value) : xReq V epm_items0 = true := by rfl
private theorem epm_writes : ∀ m < 32, 2479 + m ∈ xWrites epm_items0 := by decide +kernel
private theorem epk_writes : ∀ j < 33, 2346 + j ∈ xWrites epk_items0 := by decide +kernel
private theorem fwd_ep : fwdAll 2567 = true := by decide +kernel

/-- The packed product of a pair of the reciprocal and a pair of two numbers. -/
private theorem mul_pairs {p q : Nat} (hpq : p ≠ q) {s x0 x1 : ℝ} :
    fF mul2NL [.reg p, .reg q] [joinValue (.float .f32 s) (.float .f32 s),
      joinValue (.float .f32 x0) (.float .f32 x1)] =
      .ok (.pair (.float .f32 (s * x0)) (.float .f32 (s * x1))) := by
  have hj := fun (a b : ℝ) => split_join_clean (clean_float a) (clean_float b)
  have e1 : lk [p, q] [joinValue (.float .f32 s) (.float .f32 s),
      joinValue (.float .f32 x0) (.float .f32 x1)] p = joinValue (.float .f32 s) (.float .f32 s) :=
    by simp [lk]
  have e2 : lk [p, q] [joinValue (.float .f32 s) (.float .f32 s),
      joinValue (.float .f32 x0) (.float .f32 x1)] q =
        joinValue (.float .f32 x0) (.float .f32 x1) := by
    have e : (q == p) = false := beq_false_of_ne (Ne.symm hpq)
    simp [lk, List.lookup, e]
  simp only [fF, regsOf, regOf, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.append_nil, List.map_cons, List.map_nil, fOpnd, e1, e2, mul2NL]
  exact floatE_mul2N_fin (by rw [hj]; exact valFloat_float) (by rw [hj]; exact valFloat_float)
    (by rw [hj]; exact valFloat_float) (by rw [hj]; exact valFloat_float)

/-- **The products of the epilogue**: the state at pc 2674 that follows a state at pc 2609 holding
the reciprocal `s` (register 1761) and the 64 words `o j` (registers `1763 + j`) holds, in the
register `2479 + m`, the pair of the products of `s` with the words `2 m` and `2 m + 1`. -/
theorem prod_run {w c : TState} {s : ℝ} {o : Nat → ℝ} (hpc : w.pc = 2609)
    (hf : w.fault = none) (h61 : w.regs 1761 = some (.float .f32 s))
    (hw : ∀ j < 64, w.regs (1763 + j) = some (.float .f32 (o j)))
    (p : TauPath L g w c) (hc : c.pc = 2674) :
    ∀ m < 32, c.regs (2479 + m) =
      some (.pair (.float .f32 (s * o (2 * m))) (.float .f32 (s * o (2 * m + 1)))) := by
  intro m hm
  let V0 : Nat → Value := fun r => (w.regs r).getD (.bits 32 0)
  have hV0 : ∀ r ∈ epkDom, w.regs r = some (V0 r) := by
    intro r hr
    simp only [epkDom, List.mem_cons, List.mem_map, List.mem_range] at hr
    rcases hr with rfl | ⟨j, hj, rfl⟩
    · simp [V0, h61]
    · simp [V0, hw j hj]
  have hd : ∀ r ∈ epkDom, w.regs r = some (lookupD (epk_facts0 V0) r) := fun r hr => by
    rw [epk_f0, lookupD_factsFrom hr]
    exact hV0 r hr
  obtain ⟨j, hj, t1, h1, h2, -, h4, -, -, h7, -, -, h10⟩ := xRun_path (K := kernel)
    (A := Assumptions.all) (L := L) (g := g) epk_items0 _ epkDom w
    (hpc ▸ (epk_at0 L g).code) hf hd epk_reads (epk_req _) epk_local
    (hpc ▸ (epk_at0 L g).rules) c p
  have hlen : epk_items0.length = 33 := by decide +kernel
  have hj33 : j = 33 := by
    rcases h2 with h2 | h2
    · omega
    · rw [h2, hpc] at h4
      omega
  subst hj33
  rw [List.take_of_length_le (by omega)] at h10
  have ht1 : t1.pc = 2642 := by omega
  have hv1 : ∀ r ∈ epmDom, t1.regs r = some (lookupD (epm_facts0 (fun r => (t1.regs r).getD
      (.bits 32 0))) r) := by
    intro r hr
    rw [epm_f0, lookupD_factsFrom hr]
    simp only [epmDom, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hr
    obtain ⟨v, hv⟩ : ∃ v, t1.regs r = some v := by
      rcases hr with ⟨i, hi, rfl⟩ | rfl
      · exact ⟨_, h10 _ (List.mem_append_left _ (epk_writes i (by omega)))⟩
      · exact ⟨_, h10 _ (List.mem_append_left _ (epk_writes 32 (by omega)))⟩
    simp [hv]
  obtain ⟨j2, hj2, t2, h1', h2', -, h4', -, -, -, -, -, h10'⟩ := xRun_path (K := kernel)
    (A := Assumptions.all) (L := L) (g := g) epm_items0 _ epmDom t1
    (ht1 ▸ (epm_at0 L g).code) (h7.trans hf) hv1 epm_reads (epm_req _) epm_local
    (ht1 ▸ (epm_at0 L g).rules) c h1
  have hlen2 : epm_items0.length = 32 := by decide +kernel
  have hj32 : j2 = 32 := by
    rcases h2' with h2' | h2'
    · omega
    · rw [h2', ht1] at h4'
      omega
  subst hj32
  rw [List.take_of_length_le (by omega)] at h10'
  have ht2 : t2.pc = 2674 := by omega
  obtain rfl : t2 = c := tau_same fwd_ep (by omega) h1' (by omega)
  have e78 : t1.regs 2378 = some (joinValue (.float .f32 s) (.float .f32 s)) := by
    rw [h10 2378 (List.mem_append_left _ (epk_writes 32 (by omega))), epk_rcp]
    simp [V0, h61]
  have ep : t1.regs (2346 + m) = some (joinValue (.float .f32 (o (2 * m)))
      (.float .f32 (o (2 * m + 1)))) := by
    rw [h10 _ (List.mem_append_left _ (epk_writes m (by omega))), epk_pair _ m hm]
    have a1 := hw (2 * m) (by omega)
    have a2 := hw (2 * m + 1) (by omega)
    rw [show 1763 + (2 * m + 1) = 1764 + 2 * m by omega] at a2
    simp [V0, a1, a2]
  rw [h10' _ (List.mem_append_left _ (epm_writes m hm)), epm_prod _ m hm]
  simp only [e78, ep, Option.getD_some, mul_pairs (show 2378 ≠ 2346 + m by omega), okVal]

end
end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
