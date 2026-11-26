-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.StrictQt
public import Lemmas.Flow.ShflReg
public import Lemmas.Flow.ShflRegImm
public import Lemmas.Flow.Step.SiteShape
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The index warp's shuffles send the words their facts name

A good state at one of the index warp's four shuffle sites holds the word the shuffle sends in its
operand register as a fact (`ixVal`: `%r606`, `%r609`, `%r645`, `%r648`, the `cvt.s32.s8` of the
lane's validity bits and of the first received word's `or`), so the shuffle event it fires sends
that word (`fires_shfl_regv`), a 32-bit one (`ix_sendBits`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged

/-- The register a shuffle site sends. -/
def sendReg : IxSite → Nat
  | .sA1 => 606
  | .sA2 => 609
  | .sB1 => 645
  | _ => 648

/-- The butterfly distance of a shuffle site. -/
def sendDist : IxSite → Nat
  | .sA1 | .sB1 => 1
  | _ => 2

/-- **The event a shuffle site of the index warp fires sends the word of its operand's fact**,
a full-warp butterfly of the site's distance. -/
theorem ix_shflSends {P : Params} {L : Launch} {g : Nat} {c : IxCtl} {s : IxSite} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hF : Holds t.regs (ixFacts P L g c s))
    (hs : s = .sA1 ∨ s = .sA2 ∨ s = .sB1 ∨ s = .sB2) (hc : kernel.code[s.pc]? = some ins)
    (hf : Fires s.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (he : Execution.isShfl e = true) :
    ∃ recv ok,
      e = ⟨s.pc, .shfl .bfly (ixVal P L g c (sendReg s)) (sendDist s) 31 recv ok⟩ := by
  rcases hs with rfl | rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2464)
    exact fires_shfl_regimm (p := some 27) (d := 607)
      (regs_of_factsFrom hF (by decide +kernel)) hf he
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2467)
    exact fires_shfl_regimm (p := some 28) (d := 610)
      (regs_of_factsFrom hF (by decide +kernel)) hf he
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2553)
    exact fires_shfl_regimm (p := some 42) (d := 646)
      (regs_of_factsFrom hF (by decide +kernel)) hf he
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2556)
    exact fires_shfl_regimm (p := some 43) (d := 649)
      (regs_of_factsFrom hF (by decide +kernel)) hf he

/-- The word a shuffle site sends is a 32-bit one. -/
theorem ix_sendBits {P : Params} {L : Launch} {g : Nat} (c : IxCtl) {s : IxSite}
    (hs : s = .sA1 ∨ s = .sA2 ∨ s = .sB1 ∨ s = .sB2) :
    ∃ y, ixVal P L g c (sendReg s) = .bits 32 y := by
  rcases hs with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
