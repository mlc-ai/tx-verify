-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Compare
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w
local notation "S" => SegU kernel Assumptions.all L g

private theorem guardAt {pc p : Nat} {val : Nat → Value} {t : TState} {b : Bool}
    (h : At t pc (factsFrom (Flow.live pc) val))
    (hm : p ∈ Flow.live pc) (hv : val p = .pred b) :
    At t pc ((p, .pred b) :: factsFrom (Flow.live pc) val) := by
  obtain ⟨hp,hsub,hacc,hf,hR⟩ := h
  exact ⟨hp,hsub,hacc,hf,hv ▸ holds_mem hR (mem_factsFrom hm),hR⟩

local syntax "branch_at " num ppSpace num ppSpace term : tactic
local macro_rules
  | `(tactic| branch_at $reg:num $pc:num $b) => `(tactic| (
    apply SegU.of_seg (n := 1)
    intro t ht
    have state := guardAt (p := $reg) (b := $b) ht (show $reg ∈ Flow.live $pc by decide)
      (by change Value.pred _ = _; congr 1; first | apply decide_eq_true | apply decide_eq_false
          all_goals (try dsimp only [D.limit] at *); omega)
    seg_fp state using rfl))

theorem qk_branch (h : d.i < d.limit) : S 2456 (F d 2456) 2457 (F d 2457) := by
  branch_at 7 2456 false

theorem pv_branch (h : d.limit ≤ d.i) : S 2456 (F d 2456) 2500 (F d 2500) := by
  branch_at 7 2456 true

theorem skip_pv (h : d.i = 0) : S 2501 (F d 2501) 2447 (F d 2447) := by
  branch_at 12 2501 true

theorem enter_pv (h : d.i ≠ 0) : S 2501 (F d 2501) 2502 (F d 2502) := by
  branch_at 12 2501 false

theorem next_iter (h : d.i ≠ d.limit) :
    S 2454 (F {d with i := d.i + 1} 2454) 2455 (F {d with i := d.i + 1} 2455) := by
  branch_at 17 2454 true

theorem end_iter (h : d.i = d.limit) :
    S 2454 (F {d with i := d.i + 1} 2454) 2550
      (F {d with i := d.i + 1, site := .finBar} 2550) := by
  branch_at 17 2454 false

theorem within_limit (h : d.limit ≤ 2147483646) :
    S 2426 (F d 2426) 2427 (F d 2427) := by branch_at 6 2426 false

theorem over_limit (h : 2147483646 < d.limit) :
    S 2426 (F d 2426) 2550 (F {d with site := .finBar} 2550) := by branch_at 6 2426 true

end PTX.Kernels.InklingRelDecode.Proof.Mma
