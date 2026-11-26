-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The TMA warp's length loads read the row's words

-- domain: consistent

The event a TMA state at a length load fires (`Tma.Nc`'s `tma_topk`, `tma_extra`) is the `.nc` read
of the four bytes of the row's word (`topk_read`, `extra_read`): the address the machine's
continuation does not state. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}
  {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **The top-k length load reads the row's word.** -/
theorem topk_read (hp : Pre P L m) {x : Nat} (hx : P.topkLenBase = some x)
    (hs : d.site = .loadTopk) (hat : (code P L g).AtD d t)
    (hc : kernel.code[(code P L g).pc d]? = some ins)
    (hf : Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.topkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g).pc d = 2181 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3045) (by rw [hs]; decide)
  simp only [valueOf, values, hs, hx, Option.getD_some, dstVals,
    valuesLoop, valuesPre] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2181)
  have hs0 : t.sub = 0 := by rw [hsub]; simp [hs, Site.sub]
  exact len_read hp hrange hal hpc hs0 hreg (by decide) hf

/-- **The extra length load reads the row's word.** -/
theorem extra_read (hp : Pre P L m) {x : Nat} (hx : P.extraTopkLenBase = some x)
    (hs : d.site = .loadExtra) (hat : (code P L g).AtD d t)
    (hc : kernel.code[(code P L g).pc d]? = some ins)
    (hf : Fires ((code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.extraTopkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g).pc d = 2191 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3047) (by rw [hs]; decide)
  simp only [valueOf, values, hs, hx, Option.getD_some, dstVals,
    valuesLoop, valuesPre] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2191)
  have hs0 : t.sub = 0 := by rw [hsub]; simp [hs, Site.sub]
  exact len_read hp hrange hal hpc hs0 hreg (by decide) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
