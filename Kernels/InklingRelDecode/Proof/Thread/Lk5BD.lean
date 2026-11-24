-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5BPro

@[expose] public section

/-!
# The default partition's `bar.sync 0, 128` before a state, `bar24` apart

`p128 L g C Lc s` is the number of a default-partition thread's earlier `bar.sync 0, 128` events
other than `bar24`, at the state `s`: none in the common start, `proOff` in the prologue,
`C + phi` in the softmax region (`C` the prologue's count), `C + Lc` in the epilogue (`Lc` the
loop's count, `Lfun num_iters`). `p128_next`: a step adds its own instruction's
`bar.sync 0, 128` unless it is `bar24`, given the prologue's gate, the prologue's count at its last
site (`C`), and `Lc = Lfun num_iters` at the softmax states.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- The loop's `bar.sync 0, 128` other than `bar24` for `n` iterations. -/
def Lfun (n : Nat) : Int := if n = 0 then 0 else 4 * (n : Int) - 2

/-- The state is the softmax region's `bar24`. -/
def isB24 : DComp.St → Bool
  | .sm d => decide (d.site = .bar24)
  | _ => false

/-- The number of earlier `bar.sync 0, 128` other than `bar24`. -/
def p128 (L : Launch) (g : Nat) (C Lc : Int) : DComp.St → Int
  | .dstart _ => 0
  | .pro d => proOff L g d
  | .sm d => C + phi d.site d.i
  | .epi _ => C + Lc

/-- The increment of a state: its `bar.sync 0, 128`, unless it is `bar24`. -/
def inc128 (s : DComp.St) : Int :=
  if b0At (DComp.pc s) = 2 ∧ isB24 s = false then 1 else 0

theorem inc128_sm (d : Sm.D) : inc128 (.sm d) = phiInc d.site := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  simp only [inc128, DComp.pc, sm_b0At, isB24]
  cases s <;> simp [smB0, phiInc]

theorem inc128_pro (d : ProA.D) : inc128 (.pro d) = proInc d.site := by
  simp only [inc128, DComp.pc, pro_b0At, isB24, proInc]
  split_ifs <;> simp_all

theorem dstart_b0At_le (s : DStart.Site) : b0At s.pc ≠ 2 := by
  rw [dstart_b0 s]; cases s <;> simp

theorem epi_b0At_le (s : Epi.Site) : b0At s.pc ≠ 2 := by
  rw [epi_b0 s]; cases s <;> simp

/-- **A step adds its own instruction's `bar.sync 0, 128` unless it is `bar24`.** -/
theorem p128_next {L : Launch} {g : Nat} {Q : Params} {C Lc : Int} {s s' : DComp.St}
    {e : Event} (h : DComp.next L g Q s e = some (some s'))
    (hG : ∀ d, s = .pro d → ProA.Gate L g d.site d.dt)
    (hC : ∀ d, s = .pro d → d.site = .bar18 → (proOff L g d : Int) = C)
    (hL : ∀ d, s = .sm d → Lc = Lfun d.e.r26) :
    p128 L g C Lc s' = p128 L g C Lc s + inc128 s := by
  cases s with
  | dstart d =>
    have hi : inc128 (.dstart d) = 0 := by
      simp [inc128, DComp.pc, dstart_b0At_le]
    rw [hi]
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, -, hf⟩ := mapInv h
    split at hf
    · subst hf
      have hlt : ProA.Site.sMax.ctorIdx ≤ ProA.Site.bar2.ctorIdx := by decide
      simp [p128, proOff, blkOff, ProA.D.start, hlt]
    · subst hf
      simp [p128]
  | pro d =>
    obtain ⟨st, dt⟩ := d
    by_cases hb : st = ProA.Site.bar18
    · subst hb
      simp only [DComp.next, DComp.proNext, ite_true] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        have hc := hC _ rfl rfl
        have hi : inc128 (.pro ⟨.bar18, dt⟩) = 0 := by
          rw [inc128_pro]; simp [proInc, proB0]
        simp only [p128, SmEntry.d0, hi]
        rw [← hc]
        simp [phi]
      · simp at h
    · simp only [DComp.next, DComp.proNext, hb, ite_false] at h
      obtain ⟨a, ha, rfl⟩ := mapInv h
      have := proOff_next ha (hG _ rfl)
      simp only [p128, inc128_pro]
      rw [this]
      push_cast
      rfl
  | sm d =>
    have hl := hL d rfl
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · rename_i hlv
      simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [p128, inc128_sm, hl]
        obtain ⟨st, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
        cases st <;> simp only [DComp.leaves] at hlv <;>
          simp_all [Lfun, phi, phiInc] <;> (try split_ifs) <;> omega
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := mapInv h
      simp only [p128, inc128_sm, phi_next ha]
      ring
  | epi d =>
    have hi : inc128 (.epi d) = 0 := by
      simp [inc128, DComp.pc, epi_b0At_le]
    rw [hi]
    simp only [DComp.next] at h
    obtain ⟨a, -, rfl⟩ := mapInv h
    simp [p128]

end
end PTX.Kernels.InklingRelDecode.Proof.Lk5B
