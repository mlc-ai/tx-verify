-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Mma.CoverHist
public import Kernels.InklingRelDecode.Proof.Common.MmaHistory

set_option linter.unusedSimpArgs false

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

/-- The QK steps the current round still owes: step `j` is pending at the sites between the
round's poll and its issue. -/
def qpend (d : D) (j : Fin 8) : Nat :=
  match d.site with
  | .qkShfl | .qkBar2 | .qkElect => 1
  | .qk j' => if j'.val ≤ j.val then 1 else 0
  | _ => 0

/-- **The count of QK issues by step**: the issues of step `j` before the state, plus the one the
round still owes, are the ready polls of the QK loop. -/
def QkCnt (d : D) (n : Cls → Nat) : Prop :=
  d.site ≠ .qkSkip ∧ ∀ j : Fin 8, n (.atPc (qkPc j)) + qpend d j = (polls d).1

theorem qkCnt_start {n : Cls → Nat} (h : QkZero n) : QkCnt {} n := by
  refine ⟨by decide, fun j => ?_⟩
  simp [qpend, polls, h j]

private theorem seven_low : low (b32 7) = 7 := by decide

private theorem shfl_seven {X : Execution} {g k : Nat} {e : Event} {md a b c recv ok}
    (seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7)
    (get : X.get (g,k) = some e) (heq : e.kind = .shfl md a b c recv ok)
    (site : e.pc = 2464 ∨ e.pc = 2512) : recv = b32 7 := by
  obtain ⟨pc, kd⟩ := e
  simp only at heq site
  subst heq
  exact seven k pc md a b c recv ok get site

private theorem pv_ne (a b : Fin 8) : pvPc a ≠ qkPc b := by revert a b; decide

private theorem bump_at (n : Cls → Nat) (e : Event) (p : Nat) :
    Code.bump cls n e (.atPc p) = n (.atPc p) + (if e.pc == p then 1 else 0) := by
  simp [Code.bump, cls]

set_option hygiene false in
local macro "quiet" : tactic => `(tactic| (
  have nq : ∀ j : Fin 8, (e.pc == qkPc j) = false := fun j => by
    rw [pc]; simp only [Site.pc]
    first | exact beq_false_of_ne (pv_ne _ j) | (fin_cases j <;> decide)
  refine ⟨by simp, fun j => ?_⟩
  have h1 := hc j
  simp only [bump_at, nq j, qpend, polls, D.limit] at h1 ⊢
  simpa using h1))

set_option hygiene false in
local macro "iterstep" : tactic => `(tactic| (
  have nq : ∀ j : Fin 8, (e.pc == qkPc j) = false := fun j => by
    rw [pc]; simp only [Site.pc]; fin_cases j <;> decide
  have inv' : 0 < i ∧ i ≤ low v ∧ low v ≤ 2147483646 := inv
  refine ⟨by simp [iterNext]; split_ifs <;> simp, fun j => ?_⟩
  have h1 := hc j
  simp only [bump_at, nq j, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 ⊢
  by_cases h2 : i = low v <;> by_cases h3 : i + 1 < low v <;>
    simp [iterNext, h2, h3, qpend, polls, D.limit, runCount, inv'.2.2] at h1 ⊢ <;> omega))

/-- **One step keeps the QK count**: the broadcast of the QK loop is a 7 and the elected lane is
the leader, so no round skips its issues. -/
theorem qkCnt_step {L : Launch} {g k : Nat} {X : Execution} {d d' : D} {e : Event} {n : Cls → Nat}
    (hlead : ElectLead L g (X.tr g))
    (seven : ∀ k pc md a b c recv ok, X.get (g,k) = some ⟨pc,.shfl md a b c recv ok⟩ →
      (pc = 2464 ∨ pc = 2512) → recv = b32 7)
    (get : X.get (g,k) = some e) (pc : e.pc = d.site.pc) (inv : Inv d) (h : QkCnt d n)
    (move : next L g d e = some (some d')) : QkCnt d' (Code.bump cls n e) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨s,i,v⟩ := d
  cases s with
  | qkSkip => exact absurd rfl hs
  | setMaxReg =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | ldNum =>
    simp only [next] at move
    split at move
    · rename_i bs _
      cases hw : Except.toOption (rebuild 3 bs) with
      | none => simp only [hw] at move; exact absurd move (by simp)
      | some v' =>
        simp only [hw] at move
        obtain rfl := Option.some.inj (Option.some.inj move)
        quiet
    · exact absurd move (by simp)
  | bar0 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    have nq : ∀ j : Fin 8, (e.pc == qkPc j) = false := fun j => by
      rw [pc]; simp only [Site.pc]; fin_cases j <;> decide
    have i0 : i = 0 := inv
    subst i0
    refine ⟨by simp [startSite]; split <;> simp, fun j => ?_⟩
    have h1 := hc j
    simp only [bump_at, nq j, qpend, polls, D.limit] at h1 ⊢
    by_cases hz : low v = 0 ∨ 2147483646 < low v
    · simp [startSite, hz, qpend, polls, D.limit, runCount] at h1 ⊢
      split_ifs <;> omega
    · simp [startSite, hz, qpend, polls, D.limit] at h1 ⊢
      omega
  | qkBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | kvWait =>
    simp only [next] at move
    split at move
    · split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        have nq : ∀ j : Fin 8, (e.pc == qkPc j) = false := fun j => by
          rw [pc]; simp only [Site.pc]; fin_cases j <;> decide
        refine ⟨by simp, fun j => ?_⟩
        have h1 := hc j
        simp only [bump_at, nq j, qpend, polls, D.limit, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero] at h1 ⊢
        omega
      · obtain rfl := Option.some.inj (Option.some.inj move)
        exact ⟨hs, fun j => by
          have h1 := hc j
          have nq : (e.pc == qkPc j) = false := by
            rw [pc]; simp only [Site.pc]; fin_cases j <;> decide
          simpa [bump_at, nq] using h1⟩
    · exact absurd move (by simp)
  | qkShfl =>
    simp only [next] at move
    split at move
    · rename_i md a b c recv ok heq
      obtain rfl := shfl_seven seven get heq (.inl (pc.trans rfl))
      obtain rfl := Option.some.inj (Option.some.inj move)
      simp only [seven_low, ↓reduceIte]
      quiet
    · exact absurd move (by simp)
  | qkBar2 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | qkElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      have win := hlead _ (List.mem_of_getElem? get) mask inst lead heq
      split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        quiet
      · rename_i no
        exact absurd win.symm no
    · exact absurd move (by simp)
  | qk j' =>
    simp only [next, issueNext] at move
    have same : ∀ a b : Fin 8, qkPc a = qkPc b → a = b := by decide
    have eq : ∀ j : Fin 8, (e.pc == qkPc j) = decide (j = j') := fun j => by
      rw [pc]; simp only [Site.pc]
      by_cases hj : j = j'
      · subst hj; simp
      · simp only [hj, decide_false, beq_eq_false_iff_ne]
        exact fun h => hj (same _ _ h.symm)
    split at move
    all_goals
      obtain rfl := Option.some.inj (Option.some.inj move)
      refine ⟨by simp, fun j => ?_⟩
      have h1 := hc j
      simp only [bump_at, eq j, qpend, polls, D.limit, Fin.val_mk] at h1 ⊢
      split_ifs at h1 ⊢ <;> simp_all <;> omega
  | qkCommit =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    have inv' : i < low v ∧ low v ≤ 2147483646 := inv
    have nq : ∀ j : Fin 8, (e.pc == qkPc j) = false := fun j => by
      rw [pc]; simp only [Site.pc]; fin_cases j <;> decide
    refine ⟨by simp [afterQk, iterNext]; split_ifs <;> simp, fun j => ?_⟩
    have h1 := hc j
    have hlt : i ≠ low v := by omega
    simp only [bump_at, nq j, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 ⊢
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      have hlt0 : 0 ≠ low v := hlt
      by_cases h3 : 1 < low v <;>
        simp [afterQk, iterNext, hlt0, h3, qpend, polls, D.limit] at h1 ⊢ <;> omega
    · have h0' : i ≠ 0 := by omega
      by_cases h3 : i + 1 < low v <;>
        simp [afterQk, iterNext, hlt, h0', h3, qpend, polls, D.limit] at h1 ⊢ <;> omega
  | pvBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | pWait =>
    simp only [next] at move
    split at move
    · split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        quiet
      · obtain rfl := Option.some.inj (Option.some.inj move)
        quiet
    · exact absurd move (by simp)
  | pvShfl =>
    simp only [next] at move
    split at move
    · rename_i md a b c recv ok heq
      obtain rfl := shfl_seven seven get heq (.inr (pc.trans rfl))
      obtain rfl := Option.some.inj (Option.some.inj move)
      simp only [seven_low, ↓reduceIte]
      quiet
    · exact absurd move (by simp)
  | pvBar2 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | pvSkip =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    iterstep
  | pvElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      split at move
      · obtain rfl := Option.some.inj (Option.some.inj move)
        quiet
      · obtain rfl := Option.some.inj (Option.some.inj move)
        iterstep
    · exact absurd move (by simp)
  | pv j' =>
    simp only [next, issueNext] at move
    split at move <;> (obtain rfl := Option.some.inj (Option.some.inj move); quiet)
  | pvCommit1 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | pvCommit2 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    iterstep
  | finBar =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | finElect =>
    simp only [next] at move
    split at move
    · rename_i mask inst lead heq
      split at move <;> (obtain rfl := Option.some.inj (Option.some.inj move); quiet)
    · exact absurd move (by simp)
  | finCommit =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | bar1 =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | setMaxRegInc =>
    simp only [next] at move
    obtain rfl := Option.some.inj (Option.some.inj move)
    quiet
  | dispatch => simp [next] at move

end PTX.Kernels.InklingRelDecode.Proof.Mma
