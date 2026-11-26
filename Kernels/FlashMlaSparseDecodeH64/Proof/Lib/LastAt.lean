-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue

@[expose] public section

/-! # A thread's last events at a pc, one event on

`lastAt_succ_eq`, `lastAt_succ_ne`: appending event `f` to the prefix adds it to the last events at
its own pc and leaves the others'. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {X : Execution} {g i p : Nat} {f : Event}

private theorem filter_succ (hg : (X.tr g)[i]? = some f) :
    ((X.tr g).take (i + 1)).filter (fun e => decide (e.pc = p)) =
      ((X.tr g).take i).filter (fun e => decide (e.pc = p)) ++
        (if f.pc = p then [f] else []) := by
  rw [List.take_add_one, hg, List.filter_append]
  simp only [Option.toList_some, List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

/-- **An event at `p` joins the last events at `p`.** -/
theorem lastAt_succ_eq (hg : (X.tr g)[i]? = some f) (h : f.pc = p) (n : Nat) :
    lastAt X g (i + 1) p (n + 1) = lastAt X g i p n ++ [f] := by
  unfold lastAt lastN
  rw [filter_succ hg]
  simp only [h, ↓reduceIte, List.length_append, List.length_singleton]
  rw [List.drop_append_of_le_length (by omega)]
  congr 2
  omega

/-- **An event at another pc leaves the last events at `p`.** -/
theorem lastAt_succ_ne (hg : (X.tr g)[i]? = some f) (h : f.pc ≠ p) (n : Nat) :
    lastAt X g (i + 1) p n = lastAt X g i p n := by
  unfold lastAt
  rw [filter_succ hg]
  simp [h]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
