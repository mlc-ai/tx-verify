-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # A length load reads its row's word

-- domain: consistent

A set length pointer is a parameter's address (`len_ptr`). A `.nc` load at one of the read-only
sites whose address register holds the row's address in the length array at `x`
(`x + 4 * ctaidY`, the code's `add64 (pw8 x) (mulWide .u (r2W L g) 4)`) fires the read of the row's
four bytes (`len_read`). With `rebuild_topk`/`rebuild_extra` (`Lib/LaunchReads.lean`), a role's
machine continues there with the launch's length word. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A length pointer whose word is not zero is set. -/
theorem len_ptr {b : Option Nat} (h : eqz64 (pw8 (b.getD 0)) = false) : ∃ x, b = some x := by
  rcases b with _ | x
  · exact absurd h (by decide)
  · exact ⟨x, rfl⟩

/-- **A length load reads its row's word.** -/
theorem len_read (hp : Pre P L m) {x : Nat} (hx : x + 4 * P.b ≤ 2 ^ 64) (hal : x % 4 = 0)
    {t : TState} {e : Event} {o : Option TState} {pc base dst : Nat} (hpc : t.pc = pc)
    (hs : t.sub = 0)
    (hreg : t.regs base = some (.bits 64 (add64 (pw8 x) (mulWide .u (r2W L g) 4))))
    (hnc : ncLoads.contains pc = true)
    (hf : Fires pc (loadTmpl Assumptions.all L g t .global true 32 [dst] base 0) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  have hrow := (ctaid_lt hp g).2
  have hb := hp.bLt
  have hw : add64 (pw8 x) (mulWide .u (r2W L g) 4) = W (x + 4 * ctaidY L g) := by
    rw [pw8_eq x (by omega)]
    exact lenAddr_eq (by omega) (by omega)
  rw [hw] at hreg
  have hA : Assumptions.all.any (·.ncLoads t.pc) = true := by
    have hm : pc ∈ ncLoads := by simpa using hnc
    rw [hpc]
    simp [Assumptions.all, Assumptions.ncReadOnly, Assumption.ncReadOnly, hm]
  rw [loadTmpl_global_nc hs hreg (by omega) (by decide) (by omega) hA] at hf
  obtain ⟨bs, -, rfl, -⟩ := hf
  exact ⟨bs, rfl, hnc⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
