-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Span
import Lemmas.Flow.Step.Combinators

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

theorem vector_store (st : Fin 2) (j : Fin 16) (h : Fin 2) :
    ∃ a, kernel.code[(Site.fst st j h).pc]? = some ⟨none, .mem a⟩ ∧ a.kind = .store ∧
      a.srcs.length = 4 ∧ (Op.mem a).isLocal = false := by
  have table : ∀ st j h, 8000 ≤ (Site.fst st j h).pc ∧
      (match tailCode[(Site.fst st j h).pc - 8000]? with
       | some ⟨none, .mem a⟩ => a.kind == .store && a.srcs.length == 4 && !(Op.mem a).isLocal
       | _ => false) = true := by decide +kernel
  obtain ⟨hb, hc⟩ := table st j h
  rw [← tailCode_eq, List.getElem?_drop, Nat.add_sub_of_le hb] at hc
  split at hc
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
    exact ⟨_, ‹_›, hc.1.1, hc.1.2, hc.2⟩
  · cases hc

/-- The first three vector elements each advance one substep regardless of the stored word. -/
theorem stepAt_fst_midU {p L g} (st : Fin 2) (j : Fin 16) (h : Fin 2) (k : Fin 4)
    (hk : k.val < 3) (v : V) : (code p L g).StepAtU ⟨.fst st j h, v, k⟩ := by
  obtain ⟨a, hc, hs, hn, hl⟩ := vector_store st j h
  apply Code.StepAt.toStepAtU
  refine ⟨fun _ => ⟨_, hc, hl, trivial⟩, ?_⟩
  intro t e u
  refine (Code.step_vec_mid (d := ⟨.fst st j h, v, k⟩) (C := code p L g)
    (dn := ⟨.fst st j h, v, k+1⟩) hc hs ?_ ?_ rfl ?_
    rfl rfl (fun _ => .inr trivial)).step
  · change k.val + 1 < _
    omega
  · intro e
    simp only [code, succ, Correction.succ, D.scheduler, hk, ↓reduceIte, Option.map_some,
      erase, V.scheduler]
  · change (k.val + 1) % 4 = k.val + 1
    exact Nat.mod_eq_of_lt (by omega)

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
