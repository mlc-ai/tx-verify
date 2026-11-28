-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenRead
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # Warpgroup 2's length loads read the row's words

-- domain: consistent

The event a warpgroup-2 state at a length load fires (`Dequant.Nc`'s `deq_topk`, `deq_extra`) is
the `.nc` read of the four bytes of the row's word (`topk_read`, `extra_read`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat} {w : BitVec 64}
  {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- **The top-k length load reads the row's word.** -/
theorem topk_read (hp : Pre P L m) {x : Nat} (hx : P.topkLenBase = some x)
    (hs : d.site = .lenA) (hat : (code P L g w).AtD d t) (hi : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.topkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g w).pc d = 2620 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3833) (by rw [hs]; decide)
  simp only [valueOf, values, valuesSetup, valuesLoop, chunkOffs, List.map, List.lookup,
    List.cons_append, List.nil_append, hx, Option.getD_some] at hreg
  norm_num at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2620)
  have hs0 : t.sub = 0 := by
    have h1 : d.el < elems d.site := hi
    rw [hs] at h1
    simp only [elems] at h1
    rw [hsub]
    show d.el = 0
    omega
  exact len_read hp hrange hal hpc hs0 hreg (by decide) hf

/-- **The extra length load reads the row's word.** -/
theorem extra_read (hp : Pre P L m) {x : Nat} (hx : P.extraTopkLenBase = some x)
    (hs : d.site = .lenB) (hat : (code P L g w).AtD d t) (hi : (code P L g w).inv d)
    (hc : kernel.code[(code P L g w).pc d]? = some ins)
    (hf : Fires ((code P L g w).pc d) (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨-, hal, hrange⟩ := hp.extraTopkLenAddressable x hx
  obtain ⟨hpc, hsub, -, -, hF⟩ := hat
  have hpd : (code P L g w).pc d = 2630 := by simp [hs, Site.pc]
  rw [hpd] at hpc hc hf
  have hreg := regs_of_factsFrom hF (r := 3835) (by rw [hs]; decide)
  simp only [valueOf, values, valuesSetup, valuesLoop, chunkOffs, List.map, List.lookup,
    List.cons_append, List.nil_append, hx, Option.getD_some] at hreg
  norm_num at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2630)
  have hs0 : t.sub = 0 := by
    have h1 : d.el < elems d.site := hi
    rw [hs] at h1
    simp only [elems] at h1
    rw [hsub]
    show d.el = 0
    omega
  exact len_read hp hrange hal hpc hs0 hreg (by decide) hf

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control
