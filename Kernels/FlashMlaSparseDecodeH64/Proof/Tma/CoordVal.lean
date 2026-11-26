-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Machine
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The coordinate words in the facts

The facts after the fourth element of quadruple `k` (`afterQuad`) are the facts before it on the
registers that are not the quadruple's (`value_old`: the quadruple before it is `cp` then), and the
loaded words on the quadruple's (`value_new`); the registers live after the load are the quadruple's
or live before (`live_regs`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- A register live after the load of quadruple `k` is the quadruple's or live before. -/
theorem live_regs (k : Fin 16) :
    ∀ r ∈ Flow.live (coordPc k + 1), r ∈ ldRegs k ∨ r ∈ tmaLive (coordPc k) := by
  fin_cases k <;> decide +kernel

/-- A coordinate register live after the load of quadruple `k`, not its own, is the one before's. -/
theorem old_regs (k : Fin 16) : ∀ r ∈ Flow.live (coordPc k + 1), (crdSlot r).isSome = true →
    r ∉ ldRegs k → r ∈ ldRegs (k.val - 1) := by
  fin_cases k <;> decide +kernel

/-- A register that is no coordinate word holds the default. -/
theorem crdWord_none (d : D) {r : Nat} (h : (crdSlot r).isSome = false) :
    crdWord d r = .pred false := by
  unfold crdWord
  cases hs : crdSlot r <;> simp_all

/-- **The registers that are not the quadruple's keep their values** at its fourth element. -/
theorem value_old (k : Fin 16) (d : D) (hs : d.site = .coord3 k) (v : Value) :
    ∀ r ∈ Flow.live (coordPc k + 1), r ∉ ldRegs k →
      valueOf P L g (afterQuad d k v) r = valueOf P L g d r := by
  intro r hr hn
  tma_state d
  dsimp only at hs
  subst hs
  by_cases hc : (crdSlot r).isSome = true
  · have h1 := old_regs k r hr hc hn
    fin_cases k <;> simp only [ldRegs, List.mem_cons, List.not_mem_nil, or_false,
      Nat.reduceSub] at h1 <;> rcases h1 with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd (by simp [ldRegs]) hn
  · have hc' : (crdSlot r).isSome = false := by simpa using hc
    have hv : ∀ j, values P L g (afterQuad ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac,
        cp, cq⟩ k j) = values P L g ⟨.coord3 k, l0, l1, neg, cnt, buf, slot, pf, pr, ac, cp, cq⟩ :=
      fun _ => by fin_cases k <;> rfl
    unfold valueOf
    rw [hv, crdWord_none _ hc', crdWord_none _ hc']

/-- **The quadruple's registers hold its words** at its fourth element. -/
theorem value_new (k : Fin 16) (d : D) (hs : d.site = .coord3 k) (v : Value) :
    ∀ r ∈ Flow.live (coordPc k + 1), r ∈ ldRegs k →
      (r, valueOf P L g (afterQuad d k v) r) ∈
        (ldRegs k).zip (accOf d ++ [v]) := by
  intro r _ hin
  tma_state d
  dsimp only at hs
  subst hs
  have hc : (crdSlot r).isSome = true := by
    fin_cases k <;> simp only [ldRegs, List.mem_cons, List.not_mem_nil, or_false] at hin <;>
      rcases hin with rfl | rfl | rfl | rfl <;> decide
  unfold valueOf
  fin_cases k <;> simp only [ldRegs, List.mem_cons, List.not_mem_nil, or_false] at hin <;>
    rcases hin with rfl | rfl | rfl | rfl <;>
    first
    | exact List.mem_cons_self
    | exact List.mem_cons_of_mem _ List.mem_cons_self
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
