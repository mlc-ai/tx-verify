-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiRcp
public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiProd
import Kernels.InklingRelDecode.Proof.Softmax.Export.EpiChain
import Kernels.InklingRelDecode.Proof.Lib.WinEvent
import Kernels.InklingRelDecode.Proof.Lib.LanePre
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section

/-! # The pairs the epilogue stores

In the window of pcs 2674 to 2846 (the addresses, the LSE store and the word stores) the registers
2479 to 2510 hold the pairs: the zero pair when the launch has no block, else the products of the
reciprocal with the words the load at pc 2607 returned.  -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat} {X : Execution}

/-- The pair in the register `2479 + m`. -/
def pairV (b : Bool) (s : ℝ) (o : Nat → ℝ) (m : Nat) : Value :=
  if b then joinValue (b32 0) (b32 0)
  else .pair (.float .f32 (s * o (2 * m))) (.float .f32 (s * o (2 * m + 1)))

private def sW : List (Nat × Nat) := [(2674, 2846)]
private def rW : List Nat := (List.range 32).map (2479 + ·)
private def sP : List (Nat × Nat) := [(2609, 2673)]

private theorem w_fwd : fwdOk sW rW = true := by decide +kernel
private theorem w_ev : evKeep sW rW = true := by decide +kernel
private theorem w_enter : enterOk sW 2674 = true := by decide +kernel
private theorem w_pred : predOk 2674 [2600, 2673] = true := by decide +kernel
private theorem w_zero : inS sW 0 = false := by decide +kernel
private theorem w_out : evOut sW = true := by decide +kernel
private theorem p_noev : noEv sP = true := by decide +kernel
private theorem p_enter : enterOk sP 2609 = true := by decide +kernel
private theorem p_eventer : evEnterOk sP 2609 = true := by decide +kernel
private theorem p_zero : inS sP 0 = false := by decide +kernel
private theorem l_pred : predOk 2609 [] = true := by decide +kernel
private theorem l_ev : evPre 2609 = true := by decide +kernel
private theorem em2600 : 2600 ∉ Assumptions.emuSites := by decide +kernel

/-- **The state after the load's wait**: the load's words are in the registers 1763 to 1826, and
the reciprocal register is the one at the shuffle of pc 2603. -/
theorem load_state {w : TState} (hw : Iface.LaneState L X g w) (hpc : w.pc = 2609) :
    ∃ k a vals sh s'', X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩ ∧ vals.length = 64 ∧
      (∀ j, j < 64 → w.regs (1763 + j) = vals[j]?) ∧ Iface.LaneState L X g s'' ∧
      s''.pc = 2603 ∧ w.regs 1761 = s''.regs 1761 := by
  obtain ⟨k, e, hk, hepc, hr⟩ := ev_before l_pred l_ev (by omega) hw hpc
  obtain ⟨s, hls, hes⟩ := lane_pre hk hr
  have hspc := EventFrame.estep_source_pc hes
  have hpost := post_pc hes
  have hs08 : s.pc = 2608 := by omega
  obtain ⟨k', a, vals, sh, s', hget, hls', hs'pc, hlen, hwords, h61⟩ :=
    Softmax.Export.after_ld hls hs08
  obtain ⟨s'', hls'', hs''pc, heq⟩ := Softmax.Export.before_ld hls' hs'pc
  have hkeep : ∀ r, w.regs r = s.regs r := fun r => by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes
    rw [hs08, Flow.code_2608] at hci
    obtain rfl := (Option.some.inj hci).symm
    exact estep_keeps hes _ (by rw [hs08, Flow.code_2608]) r
      (by simp [EventFrame.eventWrites, writesRegs])
  refine ⟨k', a, vals, sh, s'', hget, hlen, fun j hj => ?_, hls'', hs''pc, ?_⟩
  · rw [hkeep, hwords j hj]
  · rw [hkeep, h61, heq]

/-- **The pairs at pc 2674**, from the entry facts and the words of the load. -/
theorem pairs_entry {l : ℝ} {b : Bool} {o : Nat → ℝ}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (wait : EpiWait L X g b)
    (ld : ∀ k a vals sh, X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      ∀ j, j < 64 → vals[j]? = some (.float .f32 (o j))) :
    ∀ c w, Iface.LaneState L X g c → Tau kernel Assumptions.all L g c w → c.pc ∈ [2600, 2673] →
      w.pc = 2674 → ∀ m < 32,
        w.regs (2479 + m) = some (pairV b (1 / if l = 0 then 1 else l) o m) := by
  intro c w hc ht hcp hw m hm
  have hcp' : c.pc = 2600 ∨ c.pc = 2673 := by simpa using hcp
  rcases hcp' with h0 | h3
  · obtain ⟨h173, -, hz⟩ := zero_pairs entry wait c hc h0
    have hcode := Flow.code_2600
    rw [← h0] at hcode
    rcases tau_guard ht hcode h173 with ⟨-, hpc1, -⟩ | ⟨hg, -, -⟩
    · omega
    · have hb : b = true := by simpa using hg
      obtain ⟨ins, hci, -, hk⟩ := win_cases ht
      rcases hk with ⟨-, hpc1, -⟩ | ⟨-, -, hreg⟩
      · omega
      · rw [h0, Flow.code_2600] at hci
        obtain rfl := (Option.some.inj hci).symm
        rw [hreg (2479 + m) (by simp [writesRegs]) (fun h => absurd (by simpa [h0] using h) em2600),
          hz m hm]
        simp [pairV, hb]
  · obtain ⟨w0, hw0l, hw0pc, hp⟩ := back_entry (S := sP) p_noev p_enter p_eventer p_zero hc
      (by simp [inS, sP, h3])
    obtain ⟨k, a, vals, sh, s'', hget, hlen, hwords, hs'', hs''pc, h61⟩ := load_state hw0l hw0pc
    obtain ⟨hb, hs⟩ := rcp_chain entry wait s'' hs'' hs''pc
    obtain ⟨x, hx, -⟩ : ∃ x, Tau kernel Assumptions.all L g w0 x ∧ True := by
      rcases Relation.ReflTransGen.cases_head hp with h | ⟨x, hx, -⟩
      · subst h
        omega
      · exact ⟨x, hx, trivial⟩
    obtain ⟨-, -, hf0, -⟩ := win_cases hx
    have hv : ∀ j, j < 64 → w0.regs (1763 + j) = some (.float .f32 (o j)) := fun j hj => by
      rw [hwords j hj, ld k a vals sh hget j hj]
    rw [prod_run (L := L) (g := g) hw0pc hf0 (by rw [h61, hs]) hv (hp.tail ht) hw m hm]
    simp [pairV, hb]

/-- **The pairs stay in the registers 2479 to 2510** through the window of the stores. -/
theorem pairs_win {l : ℝ} {b : Bool} {o : Nat → ℝ}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some (.float .f32 l))
    (wait : EpiWait L X g b)
    (ld : ∀ k a vals sh, X.get (g, k) = some ⟨2607, .tc (.ld a vals sh)⟩ →
      ∀ j, j < 64 → vals[j]? = some (.float .f32 (o j))) :
    ∀ t, Iface.LaneState L X g t → 2674 ≤ t.pc → t.pc ≤ 2846 → ∀ m < 32,
      t.regs (2479 + m) = some (pairV b (1 / if l = 0 then 1 else l) o m) := by
  intro t ht h1 h2
  refine win_ind (S := sW) (R := rW) (lo := 2674) (preds := [2600, 2673])
    (P := fun t => ∀ m < 32, t.regs (2479 + m) = some (pairV b (1 / if l = 0 then 1 else l) o m))
    w_fwd w_ev w_enter w_pred w_zero w_out (fun t t' h hp m hm => ?_)
    (fun c w hc ht' hcp hw => pairs_entry entry wait ld c w hc ht' hcp hw) t ht
    (by simp [inS, sW]; omega)
  rw [h _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩), hp m hm]

/-- **The zero pairs at pc 2674** of a launch without a block, for any value of the row sum. -/
theorem pairs_entry_zero {v : Value}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g true) :
    ∀ c w, Iface.LaneState L X g c → Tau kernel Assumptions.all L g c w → c.pc ∈ [2600, 2673] →
      w.pc = 2674 → ∀ m < 32, w.regs (2479 + m) = some (joinValue (b32 0) (b32 0)) := by
  intro c w hc ht hcp hw m hm
  have hcp' : c.pc = 2600 ∨ c.pc = 2673 := by simpa using hcp
  rcases hcp' with h0 | h3
  · obtain ⟨h173, -, hz⟩ := zero_pairs_any entry wait c hc h0
    have hcode := Flow.code_2600
    rw [← h0] at hcode
    rcases tau_guard ht hcode h173 with ⟨-, hpc1, -⟩ | ⟨-, -, -⟩
    · omega
    · obtain ⟨ins, hci, -, hk⟩ := win_cases ht
      rcases hk with ⟨-, hpc1, -⟩ | ⟨-, -, hreg⟩
      · omega
      · rw [h0, Flow.code_2600] at hci
        obtain rfl := (Option.some.inj hci).symm
        rw [hreg (2479 + m) (by simp [writesRegs]) (fun h => absurd (by simpa [h0] using h) em2600),
          hz m hm]
  · exfalso
    obtain ⟨w0, hw0l, hw0pc, hp⟩ := back_entry (S := sP) p_noev p_enter p_eventer p_zero hc
      (by simp [inS, sP, h3])
    obtain ⟨-, -, -, -, s'', -, -, -, hs'', hs''pc, -⟩ := load_state hw0l hw0pc
    have := rcp_block entry wait s'' hs'' hs''pc
    simp at this

/-- **The zero pairs stay in the registers 2479 to 2510** for a launch without a block. -/
theorem pairs_win_zero {v : Value}
    (entry : ∀ t, Iface.LaneState L X g t → t.pc = 2562 → t.regs 1915 = some v)
    (wait : EpiWait L X g true) :
    ∀ t, Iface.LaneState L X g t → 2674 ≤ t.pc → t.pc ≤ 2846 → ∀ m < 32,
      t.regs (2479 + m) = some (joinValue (b32 0) (b32 0)) := by
  intro t ht h1 h2
  refine win_ind (S := sW) (R := rW) (lo := 2674) (preds := [2600, 2673])
    (P := fun t => ∀ m < 32, t.regs (2479 + m) = some (joinValue (b32 0) (b32 0)))
    w_fwd w_ev w_enter w_pred w_zero w_out (fun t t' h hp m hm => ?_)
    (fun c w hc ht' hcp hw => pairs_entry_zero entry wait c w hc ht' hcp hw) t ht
    (by simp [inS, sW]; omega)
  rw [h _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩), hp m hm]

end
end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
