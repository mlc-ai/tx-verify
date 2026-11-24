-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.InputIssues
public import Kernels.Fp16Gemm8192.Proof.Thread.TcSpecs
public import Kernels.Fp16Gemm8192.Proof.Thread.WarpPro

@[expose] public section

/-! # An accumulating MMA follows an MMA of its thread

The MMA at slot `s`, K step `j` of the trip at `q` accumulates unless it is a task's first
(`Mma.accumulates`). Its commits to the input empty barriers are `q + s` modulo the task's 128
blocks (`Mma.Counts.cond`). So an accumulating MMA either has a commit before it, which the
slot's four MMAs precede (`mma_batch_fact`), or is the first slot's MMA of a K step `j > 0`,
which the MMA of K step `j - 1` precedes (`mma_back`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An accumulating MMA follows an MMA of its thread.** -/
theorem mma_acc_prev_fact (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {g k : Nat} {e : Event} {d : ThreadD} {dst : Nat} {sp : TcMma.OperandSpec} {mask : List Nat}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k =
      some (some d))
    (hk : e.kind = .tc (.mma dst sp true mask)) :
    ∃ k' pc' dst' sp' acc' mask', k' < k ∧
      X.get (g, k') = some ⟨pc', .tc (.mma dst' sp' acc' mask')⟩ := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  obtain ⟨m, s, j, rfl, hs⟩ := mma_state (OpPcsFast.mem kernel_mma_pcs hc (fires_tcMma_op hfire hk))
  have hacc : Mma.accumulates m.q s.val j.val = true := by
    rw [Mma.mma_event hpre hg s j hs hat hc hfire] at hk
    simp only [Kind.tc.injEq, TcKind.mma.injEq] at hk
    exact hk.2.2.1
  have hC : Mma.Counts L g m ((X.tr g).take k) := threadCounts_run hpre hg htr k _ hσ
  have hcond := hC.cond
  have hq4 := hC.q4
  simp only [MmaCond, hs] at hcond
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  by_cases hM : mcount L g ((X.tr g).take k) = 0
  · -- the task's first slot, at a K step after the first
    have hq : m.q = 0 ∧ s.val = 0 := by rw [hM] at hcond; omega
    have hj : j.val ≠ 0 := by
      intro h0
      simp [Mma.accumulates, hq.1, hq.2, h0] at hacc
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by have := mma_state_pos hσ; omega⟩
    obtain ⟨m0, h0, hs0⟩ := mma_back (t := ⟨j.val - 1, by omega⟩) (s := s) (by omega) hσ
      (.inr ⟨by have := j.isLt; simp only; omega, by rw [hs]; congr; ext; simp only; omega⟩)
    have he0 : X.get (g, k0) = some (X.tr g)[k0] :=
      List.getElem?_eq_getElem (show k0 < (X.tr g).length by omega)
    obtain ⟨pc, dst', acc', mask', hk0⟩ := mma_site_event hpre hX hg he0 h0 hs0
    exact ⟨k0, pc, dst', _, acc', mask', by omega, he0.trans (congrArg some hk0)⟩
  · -- a commit before it, and the slot's MMAs before that
    obtain ⟨s', hs'⟩ : ∃ s' : Fin 4, 0 < ((X.tr g).take k).countP (commitsTo (emptyAt L g s')) := by
      by_contra hn
      simp only [not_exists, not_lt, Nat.le_zero] at hn
      apply hM
      unfold mcount
      exact Finset.sum_eq_zero fun s' _ => hn s'
    obtain ⟨ec, hmem, hecm⟩ := List.countP_pos_iff.mp hs'
    obtain ⟨jc, hjcl, rfl⟩ := List.getElem_of_mem hmem
    have hjc : jc < k := by simp only [List.length_take] at hjcl; omega
    have hec : (X.tr g)[jc]? = some ((X.tr g).take k)[jc] := by
      rw [← List.getElem?_take_of_lt hjc]; exact List.getElem?_eq_getElem hjcl
    set ec := ((X.tr g).take k)[jc]
    have hec' : X.get (g, jc) = some ec := hec
    obtain ⟨csp, hck, hcmb⟩ : ∃ csp, ec.kind = .tc (.commit csp) ∧ csp.mbar = emptyAt L g s' := by
      obtain ⟨pc, kd⟩ := ec
      cases kd with
      | tc op =>
        cases op with
        | commit sp => exact ⟨sp, rfl, by simpa [commitsTo] using hecm⟩
        | _ => simp [commitsTo] at hecm
      | _ => simp [commitsTo] at hecm
    obtain ⟨dc, hσc⟩ := Frame.stateAt_live (tracked hpre hX) hg hσ hjc.le
    obtain ⟨mc, rfl, -⟩ := commit_spec_fact hpre hX hg hec' hσc hck
    obtain ⟨h4, hb⟩ := mma_batch_fact hpre hX hg hec' hσc hck hcmb
    obtain ⟨pc, dst', acc', mask', hm0, -⟩ := hb 0
    exact ⟨jc - 4 + (0 : Fin 4).val, pc, dst', _, acc', mask', by simp only [Fin.val_zero]; omega,
      hm0⟩

end

end PTX.Kernels.Fp16Gemm8192.Proof
