-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' events are bounded (G1)

The sites of a softmax lane are ranked in the order of the code (`pos`): the start and the first
scheduler pass with the request's reads, the first round, the biased rounds, the plain rounds,
the final stores, the second pass. A biased round's sites are ranked above its counter `nb`
(`%r6188`) and a plain round's above `pl` (`%r6194`), which the end of a round increments. A
plain round continues only while the incremented counter is not zero, so it does not wrap; a
biased round continues while it is not `-1`, and the reference invariant says the counter is
`rb - nB - 1` with `rb < nB`, so it does not wrap either (`nb_room`). A state's rank is four
times its site's plus its sub-step (`rk`).

Every transition moves to a larger rank, fires a warp shuffle, or is a failed poll that keeps the
state (`succ_rank`). So the number of shuffles before a state, above the rank, is a measure
(`measure_step`), bounded under the reference invariant by the output warp's bound on the scan
(`measure_le`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

/-- The rank of the plain rounds' first site, the final stores' and the second pass's. -/
abbrev F : Nat := 2 ^ 40
abbrev G : Nat := 2 ^ 41
abbrev P : Nat := 2 ^ 41 + 64

/-- The rank of a scan's first site. -/
def sbase : Epilogue.Scan → Nat
  | .first => 2 | .loop => 10 | .second => P | .loop2 => P + 8

/-- The rank of a round's first site. -/
def rbase (r : Rd) (v : V) : Nat :=
  match r with
  | .first => 64
  | .bias => 128 + (r32 v.nb).toNat * 64
  | .plain => F + (r32 v.pl).toNat * 64

/-- **The rank of a site**, with the state's values `v`. -/
def pos (s : Site) (v : V) : Nat :=
  match s with
  | .setmax => 0
  | .bar1 => 1
  | .word k => sbase k
  | .down k => sbase k + 1
  | .up k j => sbase k + 2 + j.val
  | .total k => sbase k + 7
  | .vote l => if l then P + 16 else 18
  | .pre l => if l then P + 17 else 19
  | .tiles l => if l then P + 18 else 20
  | .wend l => if l then P + 19 else 21
  | .barEnd l => if l then P + 20 else 22
  | .exit l => if l then P + 21 else 23
  | .q0 => 24
  | .q1 => 25
  | .uk => 26
  | .wq => 27
  | .ws r => rbase r v
  | .sld r c => rbase r v + 1 + 2 * c.val
  | .sldw c => rbase .plain v + 2 + 2 * c.val
  | .wb b => rbase (rdOf b) v + 9
  | .bld b c => rbase (rdOf b) v + 10 + c.val
  | .fence b => rbase (rdOf b) v + 26
  | .bsync b => rbase (rdOf b) v + 27
  | .barr b => rbase (rdOf b) v + 28
  | .stat pl => rbase (if pl then .plain else .bias) v + 29
  | .narr r => rbase r v + 30
  | .pst r q => rbase r v + 31 + q.val + (if q.val = 3 then 2 else 0)
  | .pwst r k => rbase r v + 34 + 3 * k.val
  | .parr r => rbase r v + 35
  | .pws r => rbase r v + 38
  | .pel r => rbase r v + 39
  | .parr2 r => rbase r v + 40
  | .pwend r => rbase r v + 41
  | .fin k => G + k.val
  | .finarr => G + 2

theorem r32_lt (t : BitVec 64) : (r32 t).toNat < 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem rbase_lt (r : Rd) (v : V) : rbase r v + 64 ≤ G := by
  have := r32_lt v.nb
  have := r32_lt v.pl
  cases r <;> simp only [rbase, F, G] <;> omega

theorem pos_lt (s : Site) (v : V) : pos s v < P + 22 := by
  have hG : G + 64 = P := rfl
  cases s <;> simp only [pos]
  all_goals first
    | (have := rbase_lt ‹Rd› v; (try split_ifs) <;> omega)
    | (have := rbase_lt (rdOf ‹Bool›) v; omega)
    | (have := rbase_lt .plain v; omega)
    | (have := rbase_lt .bias v; have := rbase_lt .plain v; split_ifs <;> omega)
    | (cases ‹Epilogue.Scan› <;> simp only [sbase] <;> omega)
    | (cases ‹Bool› <;> simp <;> omega)
    | omega

/-- **The rank of a state**: its site's, then its sub-step. -/
def rk (d : D) : Nat := 4 * pos d.site d.v + d.k.val

theorem rk_lt (d : D) : rk d < 4 * (P + 22) := by
  have := pos_lt d.site d.v
  have := d.k.isLt
  unfold rk
  omega

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Compute and compare the ranks of concrete sites. -/
macro "rk_fin" : tactic => `(tactic|
  (simp [rk, pos, sbase, rbase, Epilogue.Scan.late, rdOf, pstNext, afterLoads, recordBias] <;>
    (try simp only [F, G, P]) <;> omega))

theorem rk_passStart_false (d : D) : 8 ≤ rk (passStart p L g false d) := by
  simp only [passStart, D.ite, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [rk, pos, sbase]

theorem rk_passStart_true (d : D) : 4 * P ≤ rk (passStart p L g true d) := by
  simp only [passStart, D.ite, ↓reduceIte]
  split <;> simp [rk, pos, sbase]

/-- The plain rounds' entry is above every biased round's site. -/
theorem rk_plainEntry (v : V) : 4 * F ≤ rk (plainEntry p L g v) := by
  simp only [plainEntry, D.ite]
  split <;> simp [rk, pos, rbase, F, G] <;> omega

theorem bias_lt (v : V) : rbase .bias v + 64 ≤ F := by
  have := r32_lt v.nb
  simp only [rbase, F]; omega

/-- **Every transition of a softmax lane moves to a larger rank, fires a shuffle, or is a failed
poll** that keeps the state, when the biased rounds' counter has room at a biased round's end. -/
theorem succ_rank {d d' : D} {e : Event} (h : succ p L g d e = some (some d'))
    (ht : d.site = .pwend .bias → (r32 d.v.nb).toNat + 1 < 2 ^ 32) :
    rk d < rk d' ∨ Execution.isShfl e = true ∨ (d' = d ∧ e.counts = false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k, acc⟩ := d
  have hk := k.isLt
  cases s with
  | down kk | up kk _ | total kk | pre l | tiles l =>
    right; left
    cases kind <;> first | rfl | simp [succ] at h
  | setmax =>
    left
    simp only [succ, Option.some.injEq] at h; subst h; rk_fin
  | bar1 =>
    left
    simp only [succ, Option.some.injEq] at h; subst h
    exact lt_of_lt_of_le (by rk_fin) (rk_passStart_false _)
  | word kk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; cases kk <;> rk_fin
      · cases h
    · cases h
  | q0 | q1 | uk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h; subst h; rk_fin
      · cases h
    · cases h
  | vote l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [D.ite]
    cases l <;> split <;> rk_fin
  | wq | ws _ | wb _ =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      simp only [↓reduceIte]
      first
        | (rk_fin; done)
        | (cases ‹Bool› <;> rk_fin)
        | (cases ‹Rd› <;> rk_fin)
  | wend l =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left; cases l <;> rk_fin
  | pwend r =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      simp only [↓reduceIte]
      have := bias_lt v
      cases r
      · -- the first round: the biased rounds or the plain entry
        simp only [afterRound, afterFirst, D.ite]
        split
        · exact lt_of_lt_of_le (by rk_fin) (rk_plainEntry _)
        · rk_fin
      · have ht' := ht rfl
        simp only [afterRound, afterBias, D.ite]
        split
        · simp only [rk, pos, rbase, r32_addi1 ht']; omega
        · refine lt_of_lt_of_le ?_ (rk_plainEntry _)
          simp only [rk, pos, rbase] at this ⊢; omega
      · simp only [afterRound, afterPlain, D.ite]
        split
        · rename_i hc
          have hroom : (r32 v.pl).toNat + 1 < 2 ^ 32 := by
            have := r32_lt v.pl
            by_contra hn
            have h0 : (r32 v.pl).toNat = 2 ^ 32 - 1 := by omega
            apply absurd hc
            simp only [scmpi, PTX.compare, r32, i32, addi, truncBits, BitVec.toNat_ofNat,
              BitVec.toNat_add, BitVec.toNat_ofInt] at h0 ⊢
            simp
            omega
          simp only [rk, pos, rbase, r32_addi1 hroom]; omega
        · have := r32_lt v.pl
          simp [rk, pos, rbase, F, G]; omega
  | sld r c =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i op
    cases op <;> simp only [reduceCtorEq] at h
    split at h
    · cases r <;> simp only [Option.some.injEq] at h <;> subst h <;>
        (try split) <;> (try simp only [Fin.val_add]) <;> rk_fin
    · cases h
  | sldw c =>
    left
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split <;> (try simp only [Fin.val_add]) <;> rk_fin
    · cases h
  | bld b c =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          simp only [rk, Fin.val_add]
          omega
        · simp only [Option.some.injEq] at h
          subst h
          split <;> (try simp only [Fin.val_add]) <;> cases b <;> rk_fin
      · cases h
    · cases h
  | fence b | barr b | stat b =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases b <;> rk_fin
  | bsync b =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    simp only [D.ite]
    cases b <;> split <;> rk_fin
  | narr r | pwst r _ | parr r | pws r | parr2 r =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases r <;> (try split) <;> rk_fin
  | pst r q =>
    left
    cases r <;> fin_cases q <;> simp only [succ, Fin.reduceFinMk, Fin.isValue] at h
    all_goals (try split at h)
    all_goals (simp only [Option.some.injEq] at h; subst h)
    all_goals first
      | (simp only [rk, Fin.val_add]; omega)
      | rk_fin
  | pel r =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    cases r <;> split <;> rk_fin
  | fin j =>
    left
    fin_cases j <;> simp only [succ, Option.some.injEq] at h <;> subst h <;> rk_fin
  | finarr =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    exact lt_of_lt_of_le (by rk_fin) (rk_passStart_true _)
  | barEnd l =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases l <;> rk_fin
  | exit l => simp [succ] at h


/-- The weight of a shuffle: above every rank. -/
abbrev W : Nat := 4 * (P + 22)

/-- **The measure of a state** past `ns` shuffles. -/
def measure (d : D) (ns : Nat) : Nat := ns * W + rk d

/-- **The measure never decreases along a transition, and increases at every counted event**;
`ns'` is the count of shuffles after the event (the thread machine's ledger, `Code.bump`). -/
theorem measure_step {d d' : D} {e : Event} {ns ns' : Nat}
    (h : succ p L g d e = some (some d'))
    (ht : d.site = .pwend .bias → (r32 d.v.nb).toNat + 1 < 2 ^ 32)
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

/-- **The biased rounds' counter has room at a biased round's end**: the reference invariant says
it is `rb - nB - 1` with `rb < nB`, at most `-2`. -/
theorem nb_room {dn : D × (Cnt → Nat)} (hR : RefCounts p L g dn) (hs : dn.1.site = .pwend .bias) :
    (r32 dn.1.v.nb).toNat + 1 < 2 ^ 32 := by
  obtain ⟨rb, rp, hQ⟩ := hR
  have hin : inBias dn.1.site.pos = true := by rw [hs]; decide
  obtain ⟨-, -, hlt, hnb⟩ := hQ.bias hin
  have hB : nB p L g dn.1.v < 2 ^ 31 := toSigned32_lt _
  rw [hnb]
  exact i32_room (by omega) (by omega)

/-- **The measure of a state that holds the reference values is bounded.** -/
theorem measure_le (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : SmWarp.SFits p L g d ns nv) :
    measure d ns ≤ (14 * p.batch + 28) * W := by
  have h1 := Epilogue.fits_coll_le_all hp hF.1
  have h2 : rk d < W := rk_lt d
  unfold measure
  generalize W = w at h2 ⊢
  have : ns * w ≤ (14 * p.batch + 27) * w := Nat.mul_le_mul_right w (by omega)
  rw [show 14 * p.batch + 28 = (14 * p.batch + 27) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
