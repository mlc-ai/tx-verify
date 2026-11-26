-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg1.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # The idle code's length loads read the row's words

-- domain: consistent

The event the idle code fires at a length load whose pointer is set (`ldA`, pc 2596; `ldB`, pc
2601) is the `.nc` read of the four bytes of the row's word (`idle_topk_read`, `idle_extra_read`):
the address register holds the row's address in the array (`idleVal`, `Lib/Idle.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}
  {s : IdleSite} {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **The top-k length load reads the row's word.** -/
theorem idle_topk_read (hp : Pre P L m) {x : Nat} (hx : P.topkLenBase = some x)
    (hs : s = .ldA) (hat : (idle P L g).AtD s t)
    (hc : kernel.code[(idle P L g).pc s]? = some ins)
    (hf : Fires ((idle P L g).pc s) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.topkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  subst hs
  have hreg := regs_of_factsFrom hF (r := 3106) (by decide)
  simp only [idleVal, idleVals, hx, Option.getD_some, List.lookup] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2596)
  exact len_read hp hrange hal hpc hsub hreg
    (by show ncLoads.contains 2596 = true; decide) hf

/-- **The extra length load reads the row's word.** -/
theorem idle_extra_read (hp : Pre P L m) {x : Nat} (hx : P.extraTopkLenBase = some x)
    (hs : s = .ldB) (hat : (idle P L g).AtD s t)
    (hc : kernel.code[(idle P L g).pc s]? = some ins)
    (hf : Fires ((idle P L g).pc s) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.extraTopkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  subst hs
  have hreg := regs_of_factsFrom hF (r := 3108) (by decide)
  simp only [idleVal, idleVals, hx, Option.getD_some, List.lookup] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2601)
  exact len_read hp hrange hal hpc hsub hreg
    (by show ncLoads.contains 2601 = true; decide) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1
