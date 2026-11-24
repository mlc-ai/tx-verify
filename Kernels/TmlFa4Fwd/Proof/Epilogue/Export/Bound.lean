-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's events are bounded (G1)

Every transition of the output warp's machine either moves to a site of larger rank (`rank`:
the sites in the order of the code's two passes, below 64), or fires a warp shuffle, or is a
failed poll that keeps the state and does not count toward the execution's size
(`succ_rank`). So the number of shuffles before a state, times 64, plus the rank of its site,
increases at every counted event and never decreases (`measure_step`).

The shuffles are bounded by the reference invariant: a state that holds the reference values
(`Fits`) is past at most `14 batch + 27` warp collectives (`fits_coll_le_all`), since a reached
scan round is at most the batch (`reached_le`) and each pass has at most `7 (batch + 1) + 2`
shuffles after its start. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The rank of a scan's first site. -/
def Scan.base : Scan → Nat
  | .first => 1 | .loop => 9 | .second => 39 | .loop2 => 47

/-- **The rank of a site**: the first scan, its loop, the choice, the writeback in code order,
then the second pass's scan, its loop and its choice. -/
def rank : Site → Nat
  | .start => 0
  | .word k => k.base
  | .down k => k.base + 1
  | .up k j => k.base + 2 + j.val
  | .total k => k.base + 7
  | .vote l => if l then 55 else 17
  | .pre l => if l then 56 else 18
  | .tiles l => if l then 57 else 19
  | .exit l => if l then 58 else 20
  | .q0 => 21
  | .q1 => 22
  | .ready st => 23 + 6 * st.val
  | .store st b => 24 + 6 * st.val + b.val
  | .commit st => 28 + 6 * st.val
  | .drain st => 35 + 2 * st.val
  | .free st => 36 + 2 * st.val

theorem rank_lt (s : Site) : rank s < 64 := by
  cases s with
  | word k | down k | total k => cases k <;> decide
  | up k j => cases k <;> revert j <;> decide
  | vote l | pre l | tiles l | exit l => cases l <;> decide
  | ready st | commit st | drain st | free st => revert st; decide
  | store st b => revert st b; decide
  | start | q0 | q1 => decide

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **Every transition of the output warp moves to a larger rank, fires a shuffle, or is a
failed poll** that keeps the state. -/
theorem succ_rank {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    rank d.site < rank d'.site ∨ Execution.isShfl e = true ∨ (d' = d ∧ e.counts = false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases s with
  | down k | up k j | total k | pre l | tiles l =>
    right; left
    cases kind <;> first | rfl | simp [succ] at h
  | start =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    split <;> simp [rank, Scan.base]
  | word k =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; simp [rank]
      · cases h
    · cases h
  | q0 | q1 =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; simp [rank]
      · cases h
    · cases h
  | vote l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    cases l <;> split <;> simp [rank]
  | ready st =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left; fin_cases st <;> simp [rank]
  | store st b =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    fin_cases st <;> fin_cases b <;> simp [rank, storeNext]
  | commit st | drain st | free st =>
    left
    fin_cases st <;> simp only [succ, Option.some.injEq, Fin.zero_eta, Fin.mk_one] at h <;>
      subst h <;> (try split) <;> simp [rank, Scan.base]
  | exit l => simp [succ] at h

/-- **The measure of a state** past `ns` shuffles. -/
def measure (d : D) (ns : Nat) : Nat := ns * 64 + rank d.site

/-- **The measure never decreases along a transition, and increases at every counted event**;
`ns'` is the count of shuffles after the event (the thread machine's ledger, `Code.bump`). -/
theorem measure_step {d d' : D} {e : Event} {ns ns' : Nat}
    (h : succ p L g d e = some (some d'))
    (hn : ns' = ns + if Execution.isShfl e then 1 else 0) :
    measure d ns ≤ measure d' ns' ∧ (e.counts = true → measure d ns < measure d' ns') := by
  have h1 := rank_lt d.site
  have h2 := rank_lt d'.site
  unfold measure
  rcases succ_rank h with hr | hs | ⟨rfl, hc⟩
  · have : ns ≤ ns' := by omega
    have : ns * 64 ≤ ns' * 64 := Nat.mul_le_mul_right 64 this
    omega
  · simp only [hs, ↓reduceIte] at hn
    subst hn
    omega
  · rw [hc]
    have : ns ≤ ns' := by omega
    have : ns * 64 ≤ ns' * 64 := Nat.mul_le_mul_right 64 this
    simp only [Bool.false_eq_true, false_implies, and_true]
    omega

/-- **A state that holds the reference values is past at most `14 batch + 27` warp
collectives**, in either pass. -/
theorem fits_coll_le_all (hp : Pre p L m) {d : D} {ns nv : Nat}
    (hF : Fits p L g d ns nv) : ns + nv ≤ 14 * p.batch + 27 := by
  cases hl : d.site.late
  · have := fits_coll_le hp hF hl
    omega
  have hsel : ∀ b : BitVec 64, selN b ≤ 2 := fun b => (selN_pos b).2
  have hP : ∀ {n0 v0 : Nat}, PassStart p L g true n0 v0 → n0 ≤ 7 * p.batch + 12 ∧ v0 = 1 := by
    intro n0 v0 h
    simp only [PassStart, ↓reduceIte] at h
    obtain ⟨R, b, hPk, rfl, rfl⟩ := h
    have := reached_le hp hPk.1.1
    have := hsel b
    omega
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases s <;> simp only [Site.late, reduceCtorEq] at hl <;> simp only [Fits] at hF
  case word k | down k | up k j | total k =>
    obtain ⟨r, n0, v0, hP0, hR, hns, hnv, -⟩ := hF
    rw [hl] at hP0
    have := hP hP0
    have := reached_le hp hR.1
    omega
  case vote l | pre l =>
    obtain ⟨R, n0, v0, hP0, hE, hns, hnv, -⟩ := hF
    subst hl
    have := hP hP0
    have := reached_le hp hE.1.1
    omega
  case tiles l =>
    obtain ⟨R, n0, v0, hP0, hE, hns, hnv, -⟩ := hF
    subst hl
    have := hP hP0
    have := reached_le hp hE.1.1
    have := hsel bal
    omega
  case exit l =>
    subst hl
    obtain ⟨n0, v0, hP0, R, hE, h⟩ := hF
    have := hP hP0
    have := reached_le hp hE.1
    rcases h with ⟨-, h1, h2⟩ | ⟨b, -, -, h1, h2, -⟩
    · omega
    · have := hsel b; omega

/-- **The measure of a state that holds the reference values is bounded.** -/
theorem measure_le (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : Fits p L g d ns nv) :
    measure d ns ≤ (14 * p.batch + 27) * 64 + 63 := by
  have h1 := fits_coll_le_all hp hF
  have h2 := rank_lt d.site
  have : ns * 64 ≤ (14 * p.batch + 27) * 64 := Nat.mul_le_mul_right 64 (by omega)
  unfold measure
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
