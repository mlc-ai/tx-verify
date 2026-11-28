-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Step.ShapeRegs

@[expose] public section

/-! # Small no-fault lemmas: polls, the CTA of a lane, cache policies

-- domain: consistent

A wait on an mbarrier word through two registers that read as 32-bit or wider words is undefined
behaviour only at a misaligned word (`fires_wait_reg_al`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A lane of the launch is in a CTA of the grid. -/
theorem cta_lt (hp : Pre P L m) (hg : g < L.threads) : g / L.block < L.grid := by
  have hb : 0 < L.block := by rw [hp.block]; decide
  exact (Nat.div_lt_iff_lt_mul hb).2 hg

/-- A 64-bit register read of a 64-bit word the facts give. -/
theorem readBits64_reg {t : TState} {r : Nat} {x : BitVec 64}
    (h : t.regs r = some (.bits 64 x)) : readBits L g t 64 (.reg r) = .ok x := by
  have hx : x.toNat % 18446744073709551616 = x.toNat := Nat.mod_eq_of_lt x.isLt
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure, truncBits, hx]

/-- A 32-bit register read of a word the facts give. -/
theorem readBits32_reg {t : TState} {r w : Nat} {x : BitVec 64}
    (h : t.regs r = some (.bits w x)) : readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

/-- A cache-policy register holding a 64-bit word is a defined policy. -/
theorem pol_ok {t : TState} {r : Nat} {x : BitVec 64} (h : t.regs r = some (.bits 64 x)) :
    cachePolicyRead L g t (some (.reg r)) = .ok () := by
  simp only [cachePolicyRead, readBits64_reg (L := L) (g := g) h, bind, Except.bind, pure,
    Except.pure]

/-- **A poll at an aligned word is no fault.** -/
theorem poll_nonub {A : List Assumption} {t : TState} {p base par : Nat} {off : Int} {acq : Bool}
    {sc : MbarScope} {pc : Nat} {e : Event} {o : Option TState} {x q : BitVec 64} {wx wq : Nat}
    (hA : A.any (·.clusterScopeMbar t.pc) = false)
    (hb : t.regs base = some (.bits wx x)) (hq : t.regs par = some (.bits wq q))
    (hal : (smLoc L g x off).addr % 8 = 0)
    (hf : Fires pc (eventTmpl A L g t (.mbarWait p base off (.reg par) acq sc)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  rcases fires_wait_reg_al hA hb hq hf with ⟨ok, hk⟩ | ⟨f, -, hn⟩
  · rw [hk]; intro f h; cases h
  · exact absurd hal hn

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
