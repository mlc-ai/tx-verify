-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Flow.Code.Part035
public import Kernels.TmlFa4Fwd.Flow.Code.Part039
public import Lemmas.Flow.TauFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- The machine stores the negative of the number of remaining KV trips. -/
def counterWord (remaining : Nat) : Value := b32 (2 ^ 32 - remaining)

private theorem negativeBits {n : Nat} (hn : 0 < n) (hN : n < 2 ^ 32) :
    truncBits 32 (-BitVec.ofNat 64 n) = BitVec.ofNat 64 (2 ^ 32 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_neg]
  omega

private theorem incrementBits {n : Nat} (hn : 2 ≤ n) (hN : n < 2 ^ 32) :
    truncBits 32 (BitVec.ofNat 64 (2 ^ 32 - n) + 1) =
      BitVec.ofNat 64 (2 ^ 32 - (n - 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add]
  change (((2 ^ 32 - n) % 2 ^ 64 + 1) % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 = _
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - n < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - n + 1 < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - n + 1 < 2 ^ 32 by omega)]
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - n + 1 < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (show 2 ^ 32 - (n - 1) < 2 ^ 64 by omega)]
  omega

/-- Initialization at the first steady traversal. -/
theorem initializeCounter {l : Launch} {g n : Nat} (hn : 0 < n) (hN : n < 2 ^ 32) :
    Seg kernel [] l g 5 2286 [(1189, b32 n)] 2291 [(7204, counterWord n)] := by
  intro t ht
  simp only [counterWord]
  seg_fp ht using
    simp only [b32, truncBits_ofNat hN (by decide), negativeBits hn hN]

private theorem counterTail {l : Launch} {g n : Nat} (hn : 2 ≤ n) (hN : n < 2 ^ 32) :
    Seg kernel [] l g 3 2530 [(7204, counterWord n)] 2533
      [(399, .pred (decide (2 < n))), (7204, counterWord (n - 1))] := by
  have hb : 2 ^ 32 - n < 2 ^ 32 := by omega
  have hNext : 4294967296 - (n - 1) < 2 ^ 64 := by omega
  have hd : truncBits 32
      (truncBits 32 (BitVec.ofNat 64 (4294967296 - n)) + truncBits 32 1#64) =
      BitVec.ofNat 64 (4294967296 - (n - 1)) := by
    rw [show truncBits 32 (BitVec.ofNat 64 (4294967296 - n)) =
        BitVec.ofNat 64 (4294967296 - n) from truncBits_ofNat hb (by decide)]
    exact incrementBits hn hN
  have hc : decide (4294967296 - (n - 1) = 4294967295) = !decide (2 < n) := by
    by_cases h : 2 < n
    · have hne : 4294967296 - (n - 1) ≠ 4294967295 := by omega
      simp [h, hne]
    · have he : 4294967296 - (n - 1) = 4294967295 := by omega
      simp [h, he]
  have hTrunc : truncBits 32 (BitVec.ofNat 64 (4294967296 - (n - 1))) =
      BitVec.ofNat 64 (4294967296 - (n - 1)) :=
    truncBits_ofNat (by omega) (by decide)
  intro t ht
  simp only [counterWord] at ht ⊢
  seg_fp ht using
    first
    | exact congrArg (Value.bits 32) hd
    | simp only [Value.pred.injEq, compare, Option.getD_some, ne_eq, Int.natCast_inj,
        decide_not, Bool.not_eq_eq_eq_not]
      change decide ((truncBits 32 (truncBits 32
          (truncBits 32 (BitVec.ofNat 64 (4294967296 - n)) + truncBits 32 1#64))).toNat =
          4294967295) = !decide (2 < n)
      rw [hd, hTrunc, toNat_ofNat_lt hNext]
      exact hc

/-- The frozen backedge decrements the remaining trips and exits when one trip remains. -/
theorem stepCounter {l : Launch} {g n : Nat} (hn : 2 ≤ n) (hN : n < 2 ^ 32) {t : TState}
    (ht : At t 2530 [(7204, counterWord n)]) :
    ∃ u, run kernel Assumptions.all l g 4 t = some u ∧
      At u (if 2 < n then 2291 else 2534) [(7204, counterWord (n - 1))] := by
  obtain ⟨u, hu, hU⟩ := counterTail hn hN t ht
  have hCalc := localRun (by decide) (by decide) ht.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hu
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_2533 _ hU hU.2.2.2.2.1 (by simp)
  have hBr := localRun (by decide) (by decide) hU.1 rfl hv
  refine ⟨v, run_comp hCalc hBr, ?_, hV.2.1, hV.2.2.1, hV.2.2.2.1,
    hV.2.2.2.2.2.1, trivial⟩
  simpa only [decide_eq_true_eq] using hV.1

/-- The counter register is untouched by all local instructions in the steady traversal. -/
theorem counterFrame {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2530)
    (hc : kernel.code[pc]? = some ins) : 7204 ∉ writesRegs ins.op := by
  have hall : ((kernel.code.drop 2291).take 239).all
      (fun i => !(writesRegs i.op).contains 7204) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hi : ((kernel.code.drop 2291).take 239)[pc - 2291]? = some ins := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
    exact hc
  have := List.all_eq_true.mp hall ins (List.mem_of_getElem? hi)
  simpa using this

/-- The six canonical polling backedges in the steady traversal. -/
def steadyPollBackedges : List (Nat × Nat) :=
  [(2296, 2294), (2299, 2297), (2337, 2335), (2354, 2352), (2421, 2419), (2452, 2450)]

private theorem steadyCodeMember {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2534)
    (hc : kernel.code[pc]? = some ins) :
    (ins, pc) ∈ ((kernel.code.drop 2291).take 243).zipIdx 2291 := by
  apply List.mem_of_getElem? (i := pc - 2291)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hlo, hc]
  rfl

private def steadyControlOk (ins : Instr) (pc : Nat) : Bool :=
  match ins.op with
  | .bra dst _ =>
    (2291 ≤ dst && dst ≤ 2534) &&
      (pc < dst || steadyPollBackedges.contains (pc, dst) || (pc == 2533 && dst == 2291))
  | .brx .. => false
  | _ => true

/-- The decoded steady region has one counted-loop backedge, plus the six polling backedges. -/
theorem steadyControl {pc : Nat} {ins : Instr} (hlo : 2291 ≤ pc) (hhi : pc < 2534)
    (hc : kernel.code[pc]? = some ins) :
    match ins.op with
    | .bra dst _ => 2291 ≤ dst ∧ dst ≤ 2534 ∧
        (pc < dst ∨ (pc, dst) ∈ steadyPollBackedges ∨ (pc = 2533 ∧ dst = 2291))
    | .brx .. => False
    | _ => True := by
  have hall : (((kernel.code.drop 2291).take 243).zipIdx 2291).all
      (fun pair => steadyControlOk pair.1 pair.2) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hall (ins, pc) (steadyCodeMember hlo hhi hc)
  cases hi : ins.op <;> simp_all [steadyControlOk, and_assoc, or_assoc]

end
end PTX.Kernels.TmlFa4Fwd.Mma
