-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WarpUniform

@[expose] public section

/-! # The poll branches of a kernel, checked in one pass

`Kernel.pollGuardsOk` searches the whole code for a branch target at each lane-compared
instruction. `pollPass T` checks the same in one pass over the code, with `T` the list of the
lane-compared positions: a lane-compared instruction is at a position of `T` and is a guarded
`bra.uni` on the predicate of the unguarded `mbarrier.try_wait` just before it, and no branch
targets a position of `T`. A proof tool, generic over the kernel. -/

namespace PTX

/-- The instruction is a guarded `bra.uni` on the predicate of the unguarded wait before it. -/
def pollShape (prev : Option Instr) (ins : Instr) : Bool :=
  match ins, prev with
  | ⟨some (p, _), .bra _ true⟩, some ⟨none, .mbarWait dst ..⟩ => p == dst
  | _, _ => false

/-- No branch of the instruction targets a position of `T`. -/
def noTarget (T : List Nat) (ins : Instr) : Bool :=
  match ins.op with
  | .bra t _ => !T.contains t
  | .brx _ ts _ => ts.all fun t => !T.contains t
  | _ => true

/-- The pass over the code from position `pc` on, after instruction `prev`. -/
def pollPass (T : List Nat) : Nat → Option Instr → List Instr → Bool
  | _, _, [] => true
  | pc, prev, ins :: l =>
    (!ins.laneCompared || (T.contains pc && pollShape prev ins)) && noTarget T ins &&
      pollPass T (pc + 1) (some ins) l

theorem pollPass_spec {T : List Nat} : ∀ {l : List Instr} {pc : Nat} {prev : Option Instr},
    pollPass T pc prev l = true → ∀ {i : Nat} {ins : Instr}, l[i]? = some ins →
      noTarget T ins = true ∧ (ins.laneCompared = true → pc + i ∈ T ∧
        pollShape (if i = 0 then prev else l[i - 1]?) ins = true)
  | [], _, _, _, _, _, h => by simp at h
  | a :: l, pc, prev, hp, i, ins, h => by
    simp only [pollPass, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.contains_iff_mem] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      refine ⟨h2, fun hc => ?_⟩
      rcases h1 with h1 | h1
      · rw [h1] at hc; cases hc
      · exact ⟨by simpa using h1.1, by simpa using h1.2⟩
    | succ i =>
      rw [List.getElem?_cons_succ] at h
      obtain ⟨k1, k2⟩ := pollPass_spec h3 h
      refine ⟨k1, fun hc => ?_⟩
      obtain ⟨k3, k4⟩ := k2 hc
      refine ⟨by rw [← Nat.add_assoc, Nat.add_right_comm]; exact k3, ?_⟩
      simp only [Nat.add_eq_zero_iff, Nat.succ_ne_self, and_false, ↓reduceIte,
        Nat.add_sub_cancel]
      cases i with
      | zero => simpa using k4
      | succ i => simpa using k4

variable {K : Kernel} {T : List Nat}

/-- **The lane-compared positions are in `T`.** -/
theorem pollPass_mem (h : pollPass T 0 none K.code = true) {pc : Nat} {ins : Instr}
    (hc : K.code[pc]? = some ins) (hl : ins.laneCompared = true) : pc ∈ T := by
  simpa using ((pollPass_spec h hc).2 hl).1

/-- **A poll branch is a position of `T`.** -/
theorem pollPass_branch (h : pollPass T 0 none K.code = true) {pc : Nat}
    (hb : K.pollBranch pc = true) : pc ∈ T := by
  obtain ⟨-, -, dst, neg, tgt, _, _, _, _, _, hc, -⟩ := pollBranch_spec hb
  exact pollPass_mem h hc rfl

/-- **Every instruction that compares a guard or an index between lanes is a poll branch.** -/
theorem pollPass_ok (h : pollPass T 0 none K.code = true) : K.pollGuardsOk = true := by
  unfold Kernel.pollGuardsOk
  refine List.all_eq_true.mpr fun ⟨ins, pc⟩ hm => ?_
  have hc : K.code[pc]? = some ins := List.mem_zipIdx_iff_getElem?.mp hm
  cases hl : ins.laneCompared with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := (pollPass_spec h hc).2 hl
    have h1 : pc ∈ T := by simpa using h1
    have h0 : pc ≠ 0 := by
      rintro rfl
      simp only [↓reduceIte, pollShape] at h2
      cases h2
    rw [ite_eq_right h0] at h2
    have hnt : K.branchTarget pc = false := by
      unfold Kernel.branchTarget
      rw [List.any_eq_false]
      intro q hq
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
      have hq' := (pollPass_spec h hj).1
      unfold noTarget at hq'
      split at hq'
      · rename_i t u hop
        rw [hop]
        simp only [beq_iff_eq]
        rintro rfl
        simp [h1] at hq'
      · rename_i i ts u hop
        rw [hop]
        intro hmem
        have := List.all_eq_true.mp hq' pc (by simpa using hmem)
        simp [h1] at this
      · split <;> simp_all
    simp only [Bool.not_true, Bool.false_or, Kernel.pollBranch, hnt, Bool.not_false, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    rw [hc]
    revert h2
    generalize K.code[pc - 1]? = prev
    unfold pollShape
    intro h2
    split at h2
    · exact h2
    · cases h2

end PTX
