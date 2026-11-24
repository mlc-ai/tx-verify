-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingRegisterWindow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2

@[expose] public section

/-! # Raw-loop controls independent of the values being dequantized -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

def dequantParityWord (n : Nat) : Value := .bits 16 (BitVec.ofNat 64 (n / 2 % 2))

/-- Loop entry retains the packed parity and selected raw slot. -/
def dequantHeadFacts (L : Launch) (g block : Nat) : List (Nat × Value) :=
  [(513, b32 (Wg2.idxInGroup L g)), (457, dequantParityWord block), (2988, b32 (block % 2))]

/-- The raw poll retains the slot, the phase, and the loop tail's copies of those values. -/
def dequantPollFacts (L : Launch) (g block : Nat) : List (Nat × Value) :=
  [(2458, sb L (Wg2.rawReadyOff (block % 2))), (2459, b32 (block / 2 % 2)),
    (351, dequantParityWord block), (2789, b32 (4294967295 - block % 2)),
    (2788, sb L (8 * (block % 2)))] ++ dequantHeadFacts L g block

/-- The opening local instructions build the actual address and parity for the block. -/
theorem dequant_loop_poll_setup {t : TState} {block : Nat}
    (hpre : Pre P L mem0) (hAt : AtVector t 2667 (dequantHeadFacts L g block) t.sub t.acc) :
    ∃ u, run kernel Assumptions.all L g 10 t = some u ∧
      AtVector u 2677 (dequantPollFacts L g block) t.sub t.acc := by
  have hShared := sharedBase_lt hpre
  have hParity : block / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hSlot : block % 2 < 2 := Nat.mod_lt _ (by decide)
  have hA : L.sharedBase + 8 * (block % 2) + 222808 < 2 ^ 32 := by omega
  unfold dequantHeadFacts dequantParityWord at hAt
  simp only [dequantPollFacts, dequantHeadFacts, dequantParityWord, List.cons_append,
    List.nil_append]
  seg_fp hAt using
    (try simp only [sb, Wg2.rawReadyOff, b32])
    norm_bits [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_comm,
      Wg2.land255, Wg2.nf_not]

/-- Just before updating the trip counter, the two-slot parity and slot have advanced. -/
theorem dequant_loop_advance {t : TState} {block : Nat}
    (hAt : AtVector t 3600
      ([(351, dequantParityWord block), (2789, b32 (4294967295 - block % 2))] ++
        dequantHeadFacts L g block) t.sub t.acc) :
    ∃ u, run kernel Assumptions.all L g 5 t = some u ∧
      AtVector u 3605 (dequantHeadFacts L g (block + 1)) t.sub t.acc := by
  have hParity : block / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hSlot : block % 2 < 2 := Nat.mod_lt _ (by decide)
  have hFlip := Wg2.par_flip block
  have hBufFlip := Wg2.buf_flip block
  simp only [dequantHeadFacts, dequantParityWord, List.cons_append, List.nil_append] at hAt
  unfold dequantHeadFacts dequantParityWord
  have hTest :
      ∃ v, run kernel Assumptions.all L g 3 t = some v ∧
        AtVector v 3603
          [(136, .pred (decide (block / 2 % 2 ≠ block % 2))),
            (2789, b32 (4294967295 - block % 2)), (513, b32 (Wg2.idxInGroup L g))]
          t.sub t.acc := by
    seg_fp hAt using
      exact Wg2.setp_ne_par hParity hSlot
  obtain ⟨v, hRun, hv⟩ := hTest
  by_cases hEq : block / 2 % 2 = block % 2
  · have hNext : (block + 1) / 2 % 2 = 0 := by simpa only [hEq, ↓reduceIte] using hFlip.symm
    simp only [hEq, ne_eq, not_true_eq_false, decide_false] at hv
    have hTail :
        ∃ u, run kernel Assumptions.all L g 2 v = some u ∧
          AtVector u 3605
            [(513, b32 (Wg2.idxInGroup L g)), (457, .bits 16 (BitVec.ofNat 64 0)),
              (2988, b32 ((block + 1) % 2))] t.sub t.acc := by
      seg_fp hv using
        (first | (rw [← hBufFlip]; exact Wg2.land1_of_lt hSlot) | rfl)
    obtain ⟨u, hu, hAt⟩ := hTail
    exact ⟨u, by simpa using run_comp hRun hu, by rwa [hNext]⟩
  · have hNext : (block + 1) / 2 % 2 = 1 := by simpa only [hEq, ↓reduceIte] using hFlip.symm
    simp only [ne_eq, hEq, not_false_eq_true, decide_true] at hv
    have hTail :
        ∃ u, run kernel Assumptions.all L g 2 v = some u ∧
          AtVector u 3605
            [(513, b32 (Wg2.idxInGroup L g)), (457, .bits 16 (BitVec.ofNat 64 1)),
              (2988, b32 ((block + 1) % 2))] t.sub t.acc := by
      seg_fp hv using
        (first | (rw [← hBufFlip]; exact Wg2.land1_of_lt hSlot) | rfl)
    obtain ⟨u, hu, hAt⟩ := hTail
    exact ⟨u, by simpa using run_comp hRun hu, by rwa [hNext]⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
