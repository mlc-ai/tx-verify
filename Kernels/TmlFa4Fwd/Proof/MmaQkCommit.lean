-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaQkIssue
public import Kernels.TmlFa4Fwd.Proof.MmaCommitGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

def qkCommitSite : Fin 4 → Fin 12
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 5

private theorem qkPcRange (block : Fin 4) : 1904 ≤ qkPc block ∧ qkPc block + 8 < 2768 := by
  fin_cases block <;> decide

private theorem skipQKSegment {l : Launch} {g : Nat} (block : Fin 4) {F : List (Nat × Value)}
    (n start : Nat) (hLen : start + n ≤ 8) {t : TState}
    (ht : At t (qkPc block + start) ((qkGuard block, .pred false) :: F)) :
    ∃ u, At u (qkPc block + (start + n)) ((qkGuard block, .pred false) :: F) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  induction n generalizing start t with
  | zero => exact ⟨t, ht, .refl⟩
  | succ n ih =>
    let step : Fin 8 := ⟨start, by omega⟩
    have hCode := qkCode block step
    have hPc : t.pc = qkPc block + step.val := ht.1
    rw [← hPc] at hCode
    have hRange := qkPcRange block
    have hGuard : guardHolds t (some (qkGuard block, false)) = .ok false := by
      simp [guardHolds, readReg, ht.2.2.2.2.1, bind, Except.bind, pure, Except.pure]
    have hStep : Tau kernel Assumptions.all l g t (next t) := by
      unfold Tau
      rw [out_eq_core (by omega) (by omega)]
      simp only [out, ht.2.2.2.1, hCode, hGuard]
      have hSub := ht.2.1
      have hAcc := ht.2.2.1
      simp [skip, next, hSub, hAcc]
    have hv : At (next t) (qkPc block + (start + 1)) ((qkGuard block, .pred false) :: F) := by
      simpa only [Nat.add_assoc] using ht.next
    obtain ⟨u, hu, hSteps⟩ := ih (start + 1) (by omega) hv
    exact ⟨u, by simpa only [Nat.add_assoc, Nat.add_comm 1] using hu, .head hStep hSteps⟩

/-- All eight guarded QK instructions skip without an event in the other MMA lanes. -/
theorem skipQK {l : Launch} {g : Nat} (block : Fin 4) {F : List (Nat × Value)} {t : TState}
    (ht : At t (qkPc block) ((qkGuard block, .pred false) :: F)) :
    ∃ u, At u (qkPc block + 8) F ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u, hu, hRest⟩ := skipQKSegment (l := l) (g := g) block 8 0 (by decide) ht
  exact ⟨u, hu.mono hu.2.2.2.2.2, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
