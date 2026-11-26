-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # An accumulating MMA of the lane has an earlier MMA of the lane with its D column

-- domain: consistent

The MMAs of the MMA lane come in blocks of 24: QK MMA `k` (D at 400) at slot `k`, PV MMA `k`
(D at `128 (k % 2)`) at slot `16 + k` (the lane's count of MMA issues before an MMA is
`24 r + slot`, `mma_slot`). An MMA that accumulates is not the first of its accumulator: QK MMA
`k` with `k ≥ 1`, and PV MMA `k` with `k ≥ 2` or in a block `r ≥ 1` (the flag of PV MMA `k < 2`
is the block counter's). Its accumulator's previous MMA is the lane's MMA one slot back (QK) or
two MMA issues back (PV), found by the count (`mma_prev`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **The slot of an MMA of the lane**: block `r`, slot `k` of 24. -/
private theorem mma_slot {i pc dc : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma dc s acc mask)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ r k, k < 24 ∧ ((X.tr g).take i).countP (Mma.cls .mma) = 24 * r + k ∧
      ((k < 16 ∧ dc = 400 ∧ (acc = true → 1 ≤ k)) ∨
        (16 ≤ k ∧ dc = 128 * ((k - 16) % 2) ∧ (acc = true → 18 ≤ k ∨ 1 ≤ r))) := by
  obtain ⟨d, hR, ⟨-, hE⟩, hl, -⟩ := mma_at hp hX hFw hx (fun _ h => by cases h) hr
  have hc := hR (take_noUb hX hx)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site <;> simp [Mma.EvK, Mma.PollEv, Mma.CommitEv, Mma.MmaEv] at hE
  case leave s => exact absurd rfl (hl s)
  case qk k =>
    obtain ⟨-, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    obtain ⟨⟨hd, hacc, -⟩, -⟩ := hE
    have hk := k.isLt
    refine ⟨cnt.toNat, k.val, by omega, ?_, .inl ⟨by omega, hd, fun h => ?_⟩⟩
    · rw [hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
        show ¬ 2 + k.val ≤ 1 by omega, show 2 + k.val ≤ 18 by omega]
    · rw [h] at hacc
      simp at hacc
      omega
  case pv k =>
    obtain ⟨⟨-, -, -, -, hcnt, -⟩, hn⟩ := (Mma.core_loop (by rfl)).mp hc
    obtain ⟨⟨hd, hacc, -⟩, -⟩ := hE
    have hk := k.isLt
    refine ⟨cnt.toNat, 16 + k.val, by omega, ?_, .inr ⟨by omega, ?_, fun h => ?_⟩⟩
    · rw [hn _ (by simp)]
      simp [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn,
        show ¬ 21 + k.val ≤ 1 by omega, show ¬ 21 + k.val ≤ 18 by omega,
        show ¬ 21 + k.val ≤ 20 by omega]
      omega
    · rw [hd]
      simp only [Mma.pvCol]
      omega
    · by_cases h2 : 2 ≤ k.val
      · exact .inl (by omega)
      · refine .inr ?_
        by_contra h0
        have h00 : cnt.toNat = 0 := by omega
        have hz : cnt = 0 := BitVec.eq_of_toNat_eq (by simpa using h00)
        rw [h, hz] at hacc
        simp [Mma.pvAcc] at hacc
        rcases hacc with h3 | h3
        · omega
        · revert h3
          decide

/-- **The previous MMA of an accumulating MMA**: an MMA of the lane that accumulates has an earlier
MMA of the lane with the same D column. -/
theorem mma_prev {i pc dc : Nat} {s : TcMma.OperandSpec} {mask : List Nat}
    (hx : X.get (g, i) = some ⟨pc, .tc (.mma dc s true mask)⟩) (hr : 1850 ≤ pc ∧ pc < 2162) :
    ∃ j < i, ∃ pc' s' acc' mask', X.get (g, j) = some ⟨pc', .tc (.mma dc s' acc' mask')⟩ ∧
      (1850 ≤ pc' ∧ pc' < 2162) := by
  obtain ⟨r, k, hk, hn, hcase⟩ := mma_slot hp hX hFw hx hr
  obtain ⟨t, ht, htc⟩ : ∃ t, t < 24 * r + k ∧ ((1 ≤ k ∧ k < 16 ∧ t + 1 = 24 * r + k) ∨
      (18 ≤ k ∧ t + 2 = 24 * r + k) ∨ (16 ≤ k ∧ k < 18 ∧ t + 18 = 24 * r + k)) := by
    rcases hcase with ⟨h1, -, h3⟩ | ⟨h1, -, h3⟩
    · have := h3 rfl
      exact ⟨24 * r + k - 1, by omega, .inl ⟨by omega, h1, by omega⟩⟩
    · rcases h3 rfl with h | h
      · exact ⟨24 * r + k - 2, by omega, .inr (.inl ⟨h, by omega⟩)⟩
      · by_cases h4 : 18 ≤ k
        · exact ⟨24 * r + k - 2, by omega, .inr (.inl ⟨h4, by omega⟩)⟩
        · exact ⟨24 * r + k - 18, by omega, .inr (.inr ⟨by omega, by omega, by omega⟩)⟩
  obtain ⟨j, x, hj, hxc, hcnt⟩ := MbarRing.Slot.exists_nth_countP (Mma.cls .mma) (c := t)
    (xs := (X.tr g).take i) (by omega)
  have hji : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hji.le] at hcnt
  have hget : X.get (g, j) = some x := by
    change (X.tr g)[j]? = some x
    rw [← hj, List.getElem?_take, ite_eq_left hji]
  obtain ⟨pc', kd⟩ := x
  have hin : 1850 ≤ pc' ∧ pc' < 2162 := by
    simp only [Mma.cls, Bool.and_eq_true, Mma.inRole, decide_eq_true_eq] at hxc
    omega
  cases kd <;> try (simp [Mma.cls, Mma.kindOf] at hxc; done)
  case wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hxc
  case tc t' =>
    cases t' <;> try (simp [Mma.cls, Mma.kindOf] at hxc; done)
    case mma dc' s' acc' mask' =>
      obtain ⟨r', k', hk', hn', hcase'⟩ := mma_slot hp hX hFw hget hin
      have hd : (k < 16 ∧ dc = 400) ∨ (16 ≤ k ∧ dc = 128 * ((k - 16) % 2)) := by
        rcases hcase with ⟨a, b, -⟩ | ⟨a, b, -⟩
        · exact .inl ⟨a, b⟩
        · exact .inr ⟨a, b⟩
      have hd' : (k' < 16 ∧ dc' = 400) ∨ (16 ≤ k' ∧ dc' = 128 * ((k' - 16) % 2)) := by
        rcases hcase' with ⟨a, b, -⟩ | ⟨a, b, -⟩
        · exact .inl ⟨a, b⟩
        · exact .inr ⟨a, b⟩
      obtain rfl : dc' = dc := by omega
      exact ⟨j, hji, pc', s', acc', mask', hget, hin⟩

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
