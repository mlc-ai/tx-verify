-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Proof.Lib.WinFacts
import Kernels.InklingRelDecode.Gen.EpiZero
import Kernels.InklingRelDecode.Proof.Softmax.Export.RcpLate
import Lemmas.Flow.OutRunCond
import Lemmas.Flow.Recip
import Lemmas.Flow.SetpCore
import Lemmas.Flow.ReachFrame

@[expose] public section

/-! # The epilogue's reciprocal chain

From the row sum `l` in register 1915 (the epilogue's entry, pc 2562) the epilogue sets the
predicate 178 (`l = 0`), fills the registers 2479 to 2510 with the zero pair and, unless the launch
has no block (the predicate 173), selects `l` or `1.0` and takes its reciprocal into
register 1761. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib
open Softmax.Gen PTX.Flow.Code

noncomputable section
variable {L : Launch} {g : Nat} {X : Execution}

private def sKeep : List (Nat × Nat) := [(2562, 2846)]

private theorem keep_fwd : fwdOk sKeep [1915] = true := by decide +kernel
private theorem keep_ev : evKeep sKeep [1915] = true := by decide +kernel
private theorem keep_enter : enterOk sKeep 2562 = true := by decide +kernel
private theorem keep_pred : predOk 2562 [2561] = true := by decide +kernel
private theorem keep_zero : inS sKeep 0 = false := by decide +kernel
private theorem keep_out : evOut sKeep = true := by decide +kernel

/-- **The row sum stays in register 1915** from the epilogue's entry to its end. -/
theorem sum_kept {v : Value}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v) :
    ∀ t, Iface.LaneState L X g t → 2562 ≤ t.pc → t.pc ≤ 2846 → t.regs 1915 = some v := by
  intro t ht h1 h2
  refine win_ind (S := sKeep) (R := [1915]) (lo := 2562) (preds := [2561])
    (P := fun t => t.regs 1915 = some v) keep_fwd keep_ev keep_enter keep_pred
    keep_zero keep_out (fun t t' h hp => by rw [h 1915 (by simp)]; exact hp)
    (fun c w hc ht' _ hw => entry w (lane_tail hc ht') hw) t ht (by simp [inS, sKeep]; omega)

/-- **The state after the epilogue's wait** (pc 2566) carries the predicate 173 (`b`: the launch
has no block) and the zero register 1760. -/
def EpiWait (L : Launch) (X : Execution) (g : Nat) (b : Bool) : Prop :=
  ∀ c, Iface.LaneState L X g c → c.pc = 2566 →
    c.regs 173 = some (.pred b) ∧ c.regs 1760 = some (b32 0)

private def epzDom : List Nat := [1760, 1915]
private def sZ : List (Nat × Nat) := [(2566, 2600)]

private theorem epz_f0 (V : Nat → Value) : epz_facts0 V = factsFrom epzDom V := by kernel_rfl
private theorem epz_reads : xReadsB epzDom epz_items0 = true := by decide +kernel
private theorem epz_local : xLocalB epz_items0 = true := by decide +kernel
private theorem epz_req (V : Nat → Value) : xReq V epz_items0 = true := by rfl
private theorem epz_len : epz_items0.length = 33 := by decide +kernel
private theorem epz_w : ∀ m < 32, 2479 + m ∈ xWrites epz_items0 := by decide +kernel
private theorem epz_173 : 173 ∉ xWrites epz_items0 := by decide +kernel
private theorem epz_178 : 178 ∈ xWrites epz_items0 := by decide +kernel
private theorem z_noev : noEv sZ = true := by decide +kernel
private theorem z_enter : enterOk sZ 2566 = true := by decide +kernel
private theorem z_eventer : evEnterOk sZ 2566 = true := by decide +kernel
private theorem z_zero : inS sZ 0 = false := by decide +kernel
private theorem z_fwd : fwdAll 2567 = true := by decide +kernel
private theorem z_ev : evAtB kernel 2565 = true := by decide +kernel

private theorem epz_first (V : Nat → Value) :
    xFinal (lookupD (epz_facts0 V)) epz_items0 2479 = joinValue (V 1760) (V 1760) := by
  kernel_rfl

private theorem epz_mov (V : Nat → Value) : ∀ m < 31,
    xFinal (lookupD (epz_facts0 V)) epz_items0 (2480 + m) =
      okVal (.bits 32 0) (fF Softmax.mov64L [.reg 2479] [joinValue (V 1760) (V 1760)]) := by
  intro m hm
  interval_cases m <;> kernel_rfl

private theorem epz_setp (V : Nat → Value) :
    xFinal (lookupD (epz_facts0 V)) epz_items0 178 =
      .pred (okPred (setpE (.unord .eq) false (V 1915) (.bits 32 (BitVec.ofNat 64 0)))) := by
  kernel_rfl

private theorem zero_move : okVal (.bits 32 0) (fF Softmax.mov64L [.reg 2479]
    [joinValue (b32 0) (b32 0)]) = joinValue (b32 0) (b32 0) := by
  rfl

private theorem sum_zero {l : ℝ} : okPred (setpE (.unord .eq) false (.float .f32 l)
    (.bits 32 (BitVec.ofNat 64 0))) = decide (l = 0) := by
  rw [setpE_fin (cmp := .eq) (Or.inr rfl) valFloat_float valFloat_zero]
  simp [okPred, Assumption.erealCompare]

/-- The zero bits compare equal to zero. -/
theorem setp_zero_bits : okPred (setpE (.unord .eq) false (.bits 32 (BitVec.ofNat 64 0))
    (.bits 32 (BitVec.ofNat 64 0))) = true := by
  rw [setpE_fin (cmp := .eq) (Or.inr rfl) valFloat_zero valFloat_zero]
  simp [okPred, Assumption.erealCompare]

/-- **The zero pairs and the comparison**: at pc 2600 the registers 2479 to 2510 hold the zero pair
and the predicate 178 says whether the sum is zero. -/
theorem zero_pairs_any {v : Value} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g b) :
    ∀ c, Iface.LaneState L X g c → c.pc = 2600 → c.regs 173 = some (.pred b) ∧
      c.regs 178 = some (.pred (okPred (setpE (.unord .eq) false v
        (.bits 32 (BitVec.ofNat 64 0))))) ∧
      ∀ m < 32, c.regs (2479 + m) = some (joinValue (b32 0) (b32 0)) := by
  intro c hc hpc
  obtain ⟨w, hwl, hwpc, hp⟩ := back_entry (S := sZ) z_noev z_enter z_eventer z_zero hc
    (by simp [inS, sZ, hpc])
  obtain ⟨hw173, hw1760⟩ := wait w hwl hwpc
  rcases Relation.ReflTransGen.cases_head hp with h | ⟨w2, ht, hp2⟩
  · subst h
    omega
  obtain ⟨ins, hci, -, hk⟩ := win_cases ht
  rw [hwpc, Flow.code_2566] at hci
  obtain rfl := (Option.some.inj hci).symm
  rcases hk with ⟨-, hpc2, hreg⟩ | ⟨-, hpc2, -⟩
  swap
  · exfalso
    have em : 2566 ∉ Assumptions.emuSites := by decide +kernel
    have h65 : w2.pc = 2565 := by simpa [succs, hwpc, em] using hpc2
    rcases Relation.ReflTransGen.cases_head hp2 with h | ⟨x, hx, -⟩
    · subst h
      omega
    · exact no_tau_evAt (by rw [h65]; exact z_ev) hx
  have hw2 : w2.pc = 2567 := by omega
  have hl2 : Iface.LaneState L X g w2 := lane_tail hwl ht
  obtain ⟨x, hx, -⟩ : ∃ x, Tau kernel Assumptions.all L g w2 x ∧ True := by
    rcases Relation.ReflTransGen.cases_head hp2 with h | ⟨x, hx, -⟩
    · subst h
      omega
    · exact ⟨x, hx, trivial⟩
  obtain ⟨-, -, hf2, -⟩ := win_cases hx
  have hsum := sum_kept entry w2 hl2 (by omega) (by omega)
  let V0 : Nat → Value := fun r => (w2.regs r).getD (.bits 32 0)
  have hV0 : ∀ r ∈ epzDom, w2.regs r = some (V0 r) := by
    intro r hr
    simp only [epzDom, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [V0, hreg, hw1760]
    · simp [V0, hsum]
  have hd : ∀ r ∈ epzDom, w2.regs r = some (lookupD (epz_facts0 V0) r) := fun r hr => by
    rw [epz_f0, lookupD_factsFrom hr]
    exact hV0 r hr
  obtain ⟨j, hj, t1, h1, h2, -, h4, -, -, h7, -, h9, h10⟩ := xRun_path (K := kernel)
    (A := Assumptions.all) (L := L) (g := g) epz_items0 _ epzDom w2
    (hw2 ▸ (epz_at0 L g).code) hf2 hd epz_reads (epz_req _)
    epz_local (hw2 ▸ (epz_at0 L g).rules) c hp2
  have hj33 : j = 33 := by
    have := epz_len
    rcases h2 with h2 | h2
    · omega
    · rw [h2, hw2] at h4
      omega
  subst hj33
  have hlen := epz_len
  rw [List.take_of_length_le (by omega)] at h9 h10
  obtain rfl : t1 = c := tau_same z_fwd (by omega) h1 (by omega)
  have v1760 : V0 1760 = b32 0 := by simp [V0, hreg, hw1760]
  have v1915 : V0 1915 = v := by simp [V0, hsum]
  refine ⟨?_, ?_, fun m hm => ?_⟩
  · rw [h9 173 epz_173, hreg, hw173]
  · rw [h10 178 (List.mem_append_left _ epz_178), epz_setp, v1915]
  · rw [h10 _ (List.mem_append_left _ (epz_w m hm))]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [epz_first, v1760]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [show 2479 + (m' + 1) = 2480 + m' by omega, epz_mov _ m' (by omega), v1760, zero_move]


/-- **The zero pairs and the comparison** for a row sum that reads as a number. -/
theorem zero_pairs {l : ℝ} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (wait : EpiWait L X g b) :
    ∀ c, Iface.LaneState L X g c → c.pc = 2600 → c.regs 173 = some (.pred b) ∧
      c.regs 178 = some (.pred (decide (l = 0))) ∧
      ∀ m < 32, c.regs (2479 + m) = some (joinValue (b32 0) (b32 0)) := by
  intro c hc hpc
  obtain ⟨h1, h2, h3⟩ := zero_pairs_any entry wait c hc hpc
  exact ⟨h1, by rw [h2, sum_zero], h3⟩

private def eprDom : List Nat := [178, 1915]
private def sR : List (Nat × Nat) := [(2601, 2602)]

private theorem epr_f0 (V : Nat → Value) : epr_facts0 V = factsFrom eprDom V := by kernel_rfl
private theorem epr_reads : xReadsB eprDom epr_items0 = true := by decide +kernel
private theorem epr_local : xLocalB epr_items0 = true := by decide +kernel
private theorem epr_len : epr_items0.length = 2 := by decide +kernel
private theorem epr_w : 1761 ∈ xWrites epr_items0 := by decide +kernel
private theorem r_noev : noEv sR = true := by decide +kernel
private theorem r_enter : enterOk sR 2601 = true := by decide +kernel
private theorem r_eventer : evEnterOk sR 2601 = true := by decide +kernel
private theorem r_zero : inS sR 0 = false := by decide +kernel
private theorem r_pred : predOk 2601 [2600] = true := by decide +kernel
private theorem r_land : evLand 2601 = true := by decide +kernel

private theorem epr_req (V : Nat → Value) (h : isPred (V 178) = true) :
    xReq (lookupD (epr_facts0 V)) epr_items0 = true := by
  have e : lookupD (epr_facts0 V) 178 = V 178 := rfl
  simp [xReq, XItem.req, OItem.req, epr_items0, e, h, isRegOrF32]

private theorem epr_final (V : Nat → Value) :
    xFinal (lookupD (epr_facts0 V)) epr_items0 1761 = epr_v2602 V := by
  kernel_rfl

private theorem rcp_val {v : Value} {x : ℝ} (hx : valFloat .f32 v = .ok x) (h0 : x ≠ 0) :
    okVal (.bits 32 0) (fF (Softmax.rcpL true) [.reg 1762] [v]) = .float .f32 (1 / x) := by
  have e : fF (Softmax.rcpL true) [.reg 1762] [v] = rcpE true v := rfl
  rw [e, rcpE_fin hx h0]
  rfl

/-- **A state at pc 2603 has a block**: the launch is not the empty one (any row sum value). -/
theorem rcp_block {v : Value} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g b) :
    ∀ t, Iface.LaneState L X g t → t.pc = 2603 → b = false := by
  intro t ht hpc
  obtain ⟨c, hc, hcpc, -⟩ := Softmax.Export.rcp_pred ht hpc
  obtain ⟨w1, hw1l, hw1pc, -⟩ := back_entry (S := sR) r_noev r_enter r_eventer r_zero hc
    (by simp [inS, sR, hcpc])
  obtain ⟨c0, hc0, hc0pc, hT0⟩ := tau_before r_pred r_land (by omega) hw1l hw1pc
  have hc0pc' : c0.pc = 2600 := by simpa using hc0pc
  obtain ⟨h173, -, -⟩ := zero_pairs_any entry wait c0 hc0 hc0pc'
  have hcode := Flow.code_2600
  rw [← hc0pc'] at hcode
  rcases tau_guard hT0 hcode h173 with ⟨hg, -, -⟩ | ⟨-, -, hex⟩
  · simpa using hg
  · exfalso
    rcases localA_pc_emu hex with (h | h) | ⟨h, -⟩
    · simp [nextPc] at h
      omega
    · simp [BrxTarget] at h
    · omega

/-- **The reciprocal of the sum**: at pc 2603 the launch has a block and register 1761 holds the
reciprocal of the sum, or of `1.0` when the sum is zero. -/
theorem rcp_chain {l : ℝ} {b : Bool}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (wait : EpiWait L X g b) :
    ∀ t, Iface.LaneState L X g t → t.pc = 2603 →
      b = false ∧ t.regs 1761 = some (.float .f32 (1 / if l = 0 then 1 else l)) := by
  intro t ht hpc
  obtain ⟨c, hc, hcpc, hT⟩ := Softmax.Export.rcp_pred ht hpc
  obtain ⟨w1, hw1l, hw1pc, hp1⟩ := back_entry (S := sR) r_noev r_enter r_eventer r_zero hc
    (by simp [inS, sR, hcpc])
  obtain ⟨c0, hc0, hc0pc, hT0⟩ := tau_before r_pred r_land (by omega) hw1l hw1pc
  have hc0pc' : c0.pc = 2600 := by simpa using hc0pc
  obtain ⟨h173, h178, -⟩ := zero_pairs entry wait c0 hc0 hc0pc'
  have hcode := Flow.code_2600
  rw [← hc0pc'] at hcode
  rcases tau_guard hT0 hcode h173 with ⟨hg, hpc1, hreg⟩ | ⟨-, -, hex⟩
  swap
  · exfalso
    rcases localA_pc_emu hex with (h | h) | ⟨h, -⟩
    · simp [nextPc] at h
      omega
    · simp [BrxTarget] at h
    · omega
  have hb : b = false := by simpa using hg
  refine ⟨hb, ?_⟩
  have hsum := sum_kept entry c0 hc0 (by omega) (by omega)
  have hl1 : w1.pc = 2601 := hw1pc
  obtain ⟨x, hx, -⟩ : ∃ x, Tau kernel Assumptions.all L g w1 x ∧ True := by
    rcases Relation.ReflTransGen.cases_head hp1 with h | ⟨x, hx, -⟩
    · subst h
      omega
    · exact ⟨x, hx, trivial⟩
  obtain ⟨-, -, hf1, -⟩ := win_cases hx
  let V0 : Nat → Value := fun r => (w1.regs r).getD (.bits 32 0)
  have hV0 : ∀ r ∈ eprDom, w1.regs r = some (V0 r) := by
    intro r hr
    simp only [eprDom, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [V0, hreg, h178]
    · simp [V0, hreg, hsum]
  have hd : ∀ r ∈ eprDom, w1.regs r = some (lookupD (epr_facts0 V0) r) := fun r hr => by
    rw [epr_f0, lookupD_factsFrom hr]
    exact hV0 r hr
  have v178 : V0 178 = .pred (decide (l = 0)) := by simp [V0, hreg, h178]
  have v1915 : V0 1915 = .float .f32 l := by simp [V0, hreg, hsum]
  obtain ⟨j, hj, t1, h1, h2, -, h4, -, -, h7, -, -, h10⟩ := xRun_path (K := kernel)
    (A := Assumptions.all) (L := L) (g := g) epr_items0 _ eprDom w1
    (hl1 ▸ (epr_at0 L g).code) hf1 hd epr_reads (epr_req _ (by simp [v178, isPred])) epr_local
    (hl1 ▸ (epr_at0 L g).rules) t (hp1.tail hT)
  have hj2 : j = 2 := by
    have := epr_len
    rcases h2 with h2 | h2
    · omega
    · rw [h2, hl1] at h4
      omega
  subst hj2
  have hlen := epr_len
  rw [List.take_of_length_le (by omega)] at h10
  obtain rfl : t1 = t := tau_same z_fwd (by omega) h1 (by omega)
  rw [h10 1761 (List.mem_append_left _ epr_w), epr_final]
  simp only [epr_v2602, epr_v2601, v178, v1915, predOf]
  by_cases hl : l = 0
  · simp only [hl, decide_true, ite_true, opndVal]
    rw [rcp_val valFloat_one one_ne_zero]
  · simp only [hl, decide_false, Bool.false_eq_true, ite_false]
    rw [rcp_val valFloat_float hl]

end
end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
