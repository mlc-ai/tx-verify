-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Correction.RefSucc
import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' events are bounded (G1)

The sites of a correction lane are ranked in the order of the code (`pos`): the start, the first
scheduler pass, the request's reads, the rescale rounds, the final stage, the second pass. A
rescale round's sites are ranked above the round counter `trip` (`%r6218`, the negated number of
rounds left), which the end of a round increments; the reference invariant says it is the
negated count of rounds left, so it does not wrap (`trip_room`). A state's rank is four times its
site's plus its sub-step (`rk`).

Every transition moves to a larger rank, fires a warp shuffle, or is a failed poll that keeps the
state (`succ_rank`). So the number of shuffles before a state, above the rank, is a measure
(`measure_step`), bounded under the reference invariant by the output warp's bound on the scan
(`measure_le`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

/-- The rank of the final stage's first site, and of the second pass's first site. -/
abbrev F : Nat := 2 ^ 40
abbrev P : Nat := 2 ^ 40 + 256

/-- The rank of a scan's first site. -/
def sbase : Epilogue.Scan → Nat
  | .first => 4 | .loop => 12 | .second => P | .loop2 => P + 8

/-- The rank of a rescale round's first site, above the round counter `t`. -/
abbrev rbase (t : BitVec 64) : Nat := 64 + (r32 t).toNat * 64

/-- **The rank of a site**, with round counter `t`. -/
def pos (s : Site) (t : BitVec 64) : Nat :=
  match s with
  | .setmax => 0
  | .bar1 => 1
  | .arr k => 2 + k.val
  | .word k => sbase k
  | .down k => sbase k + 1
  | .up k j => sbase k + 2 + j.val
  | .total k => sbase k + 7
  | .vote l => if l then P + 16 else 20
  | .pre l => if l then P + 17 else 21
  | .tiles l => if l then P + 18 else 22
  | .wend l => if l then P + 19 else 23
  | .barEnd l => if l then P + 20 else 24
  | .exit l => if l then P + 21 else 25
  | .q0 => 26
  | .q1 => 27
  | .uk => 28
  | .nb k => 29 + 2 * k.val
  | .free => 30
  | .rbar st => rbase t + 32 * st.val
  | .rscale st => rbase t + 1 + 32 * st.val
  | .rvote st => rbase t + 2 + 32 * st.val
  | .rld st c => rbase t + 3 + 3 * c.val + 32 * st.val
  | .rldw st c => rbase t + 4 + 3 * c.val + 32 * st.val
  | .rst st c => rbase t + 5 + 3 * c.val + 32 * st.val
  | .rwait st => rbase t + 27 + 32 * st.val
  | .rarr st k => rbase t + 28 + k.val + 32 * st.val
  | .farr0 => F
  | .fbar st => F + 1 + 80 * st.val
  | .fsum st => F + 2 + 80 * st.val
  | .fmax st => F + 3 + 80 * st.val
  | .farr st => F + 4 + 80 * st.val
  | .fw st k => F + 5 + k.val + 80 * st.val
  | .fld st j => F + 7 + 4 * j.val + 80 * st.val
  | .fwl st j => F + 8 + 4 * j.val + 80 * st.val
  | .fst st j h => F + 9 + h.val + 4 * j.val + 80 * st.val
  | .fence st => F + 71 + 80 * st.val
  | .fdone st k => F + 72 + k.val + 80 * st.val
  | .lse h => F + 160 + h.val

theorem pos_lt (s : Site) (t : BitVec 64) : pos s t < P + 22 := by
  have ht : (r32 t).toNat < 2 ^ 32 := by
    simp only [r32, truncBits, BitVec.toNat_ofNat]; omega
  cases s with
  | word k | down k | up k _ | total k => cases k <;> simp only [pos, sbase, P] <;> omega
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> simp [pos]
  | _ => simp only [pos, P, F, rbase]; omega

/-- **The rank of a state**: its site's, then its sub-step. -/
def rk (d : D) : Nat := 4 * pos d.site d.v.trip + d.k.val

theorem rk_lt (d : D) : rk d < 4 * (P + 22) := by
  have := pos_lt d.site d.v.trip
  have := d.k.isLt
  unfold rk
  omega

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem rk_passStart_false (d : D) : 16 ≤ rk (passStart p L g false d) := by
  simp only [passStart, D.ite, rk, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [pos, sbase]

theorem rk_passStart_true (d : D) : 4 * P ≤ rk (passStart p L g true d) := by
  simp only [passStart, D.ite, rk, ↓reduceIte]
  split <;> simp [pos, sbase]

theorem r32_lt (t : BitVec 64) : (r32 t).toNat < 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem rbase_lt (t : BitVec 64) : rbase t + 64 ≤ F := by
  have := r32_lt t
  unfold rbase F
  omega

/-- **Every transition of a correction lane moves to a larger rank, fires a shuffle, or is a
failed poll** that keeps the state, when the round counter has room at a round's end. -/
theorem succ_rank {d d' : D} {e : Event} (h : succ p L g d e = some (some d'))
    (ht : d.site = .rarr 1 1 → (r32 d.v.trip).toNat + 1 < 2 ^ 32) :
    rk d < rk d' ∨ Execution.isShfl e = true ∨ (d' = d ∧ e.counts = false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k⟩ := d
  have hk := k.isLt
  cases s with
  | down k | up k j | total k | pre l | tiles l =>
    right; left
    cases kind <;> first | rfl | simp [succ] at h
  | setmax | bar1 | free | farr0 | rbar | rwait | fbar | farr | fwl | fence =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    simp only [rk, pos, F]
    omega
  | barEnd l =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases l <;> simp [rk, pos] <;> omega
  | arr j =>
    left
    fin_cases j
    · simp only [succ, Option.some.injEq] at h
      subst h
      simp only [rk, pos]
      omega
    · simp only [succ, Option.some.injEq] at h
      subst h
      have := rk_passStart_false (p := p) (L := L) (g := g) ⟨.arr 1, v, k⟩
      simp only [rk, pos] at this ⊢
      simp only [Fin.isValue, Fin.mk_one]
      omega
  | nb j =>
    left
    fin_cases j
    · simp only [succ, Option.some.injEq] at h
      subst h
      simp only [rk, pos]
      omega
    · simp only [succ, Option.some.injEq] at h
      subst h
      simp only [enterRounds, D.ite, rk]
      split <;> simp only [pos, rbase, F] <;> simp <;> omega
  | rldw st c =>
    left
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp only [rk, pos]
      omega
    · cases h
  | rst st c =>
    left
    simp only [succ] at h
    split at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp only [rk, pos] <;>
      (try simp only [Fin.val_add]) <;> omega
  | rarr st j =>
    left
    fin_cases st <;> fin_cases j
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · have ht' : (r32 v.trip).toNat + 1 < 2 ^ 32 := ht rfl
      simp only [succ, Option.some.injEq] at h
      subst h
      simp only [roundEnd, D.ite, rk]
      split
      · have e1 : rbase (addi v.trip 1) = rbase v.trip + 64 := by
          unfold rbase; rw [r32_addi1 ht']; ring
        simp only [pos, e1, Fin.isValue, Fin.val_zero]
        omega
      · have := rbase_lt v.trip
        simp only [pos, Fin.isValue]
        omega
  | fdone st j =>
    left
    fin_cases st <;> fin_cases j
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · simp only [succ, Option.some.injEq] at h; subst h; simp [rk, pos]; omega
    · simp only [succ] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [afterFinal, D.ite]
        split
        · split
          · have : rk ⟨.fdone 1 1, v, k⟩ < 4 * P := by simp [rk, pos, F, P]; omega
            exact lt_of_lt_of_le this (rk_passStart_true _)
          · simp [rk, pos]; omega
        · simp [rk, pos]; omega
      · cases h
  | lse j =>
    left
    fin_cases j
    · simp only [succ] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [afterLse, D.ite]
        split
        · have : rk ⟨.lse 0, v, k⟩ < 4 * P := by simp [rk, pos, F, P]; omega
          exact lt_of_lt_of_le this (rk_passStart_true _)
        · simp [rk, pos]; omega
      · cases h
    · simp only [succ, Option.some.injEq] at h
      subst h
      have : rk ⟨.lse 1, v, k⟩ < 4 * P := by simp [rk, pos, F, P]; omega
      exact lt_of_lt_of_le this (rk_passStart_true _)
  | exit l => simp [succ] at h
  | word k =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        cases k <;> simp [rk, pos, sbase] <;> omega
      · cases h
    · cases h
  | q0 | q1 | uk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [rk, pos]
        omega
      · cases h
    · cases h
  | fsum st =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold real32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [rk, pos]
        omega
      · cases h
    · cases h
  | rscale st =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold scale32 at h
      repeat' split at h
      all_goals cases h
      all_goals simp [rk, pos]
      all_goals omega
    · cases h
  | fmax st =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold max32 at h
      repeat' split at h
      all_goals cases h
      all_goals simp [rk, pos]
      all_goals omega
    · cases h
  | vote l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [D.ite]
    cases l <;> split <;> simp [rk, pos] <;> omega
  | rvote st =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [afterVote, D.ite]
    split <;> simp [rk, pos, setB_trip] <;> omega
  | rld st c =>
    left
    simp only [succ] at h
    split at h
    · rename_i hk0
      cases kind <;> try simp only [reduceCtorEq] at h
      rename_i op
      cases op <;> try simp only [reduceCtorEq] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp [rk, pos, hk0]
      · cases h
    · cases h
  | fld st j =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i op
    cases op <;> simp only [reduceCtorEq] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp [rk, pos]
      omega
    · cases h
  | fst st j h' =>
    left
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rename_i hk3
      simp only [rk, Fin.val_add]
      omega
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        rename_i _ hh
        simp only [rk, pos, hh]
        simp
        omega
      · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;>
          simp only [rk, pos] <;> (try simp only [Fin.val_add]) <;> omega
  | fw st j =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      simp only [↓reduceIte]
      split <;> simp [rk, pos] <;> omega
  | wend l =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      cases l <;> simp [rk, pos] <;> omega

/-- The weight of a shuffle: above every rank. -/
abbrev W : Nat := 4 * (P + 22)

/-- **The measure of a state** past `ns` shuffles. -/
def measure (d : D) (ns : Nat) : Nat := ns * W + rk d

/-- **The measure never decreases along a transition, and increases at every counted event**;
`ns'` is the count of shuffles after the event (the thread machine's ledger, `Code.bump`). -/
theorem measure_step {d d' : D} {e : Event} {ns ns' : Nat}
    (h : succ p L g d e = some (some d'))
    (ht : d.site = .rarr 1 1 → (r32 d.v.trip).toNat + 1 < 2 ^ 32)
    (hn : ns' = ns + if Execution.isShfl e then 1 else 0) :
    measure d ns ≤ measure d' ns' ∧ (e.counts = true → measure d ns < measure d' ns') := by
  have h1 : rk d < W := rk_lt d
  have h2 : rk d' < W := rk_lt d'
  unfold measure
  generalize W = w at h1 h2 ⊢
  have hle : ns * w ≤ ns' * w := Nat.mul_le_mul_right w (by omega)
  rcases succ_rank h ht with hr | hs | ⟨rfl, hc⟩
  · omega
  · simp only [hs, ↓reduceIte] at hn
    subst hn
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · rw [hc]
    simp only [Bool.false_eq_true, false_implies, and_true]
    omega

/-- **The round counter has room at a round's end**: the reference invariant says it is the
negated number of rounds left, at least two. -/
theorem trip_room {d : D} {ns nv : Nat} (hF : CorrWarp.CFits p L g d ns nv)
    (hs : d.site = .rarr 1 1) : (r32 d.v.trip).toNat + 1 < 2 ^ 32 := by
  obtain ⟨rv, -, hR, -⟩ := hF
  have hin : inRound d.site.pc = true := by rw [hs]; decide
  simp only [CorrWarp.RvAt, hin, ↓reduceIte] at hR
  obtain ⟨r, hr, ht, -⟩ := hR
  have hB := toSigned32_lt (r32 (blocks p L g d.v))
  rw [ht]
  exact i32_room (by simp only [Bs] at hr ⊢; omega) (by simp only [Bs] at hr ⊢; omega)

/-- **The measure of a state that holds the reference values is bounded.** -/
theorem measure_le (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : CorrWarp.CFits p L g d ns nv) :
    measure d ns ≤ (14 * p.batch + 28) * W := by
  obtain ⟨rv, -, -, hE, -⟩ := hF
  have h1 := Epilogue.fits_coll_le_all hp hE
  have h2 : rk d < W := rk_lt d
  unfold measure
  generalize W = w at h2 ⊢
  have : ns * w ≤ (14 * p.batch + 27) * w := Nat.mul_le_mul_right w (by omega)
  rw [show 14 * p.batch + 28 = (14 * p.batch + 27) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
