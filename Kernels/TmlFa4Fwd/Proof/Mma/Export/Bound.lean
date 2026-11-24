-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Lemmas.Flow.Counter32
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's events are bounded (G1)

The sites of the MMA warp are ranked in the order of the code (`pos`): the start, the first
scheduler pass, the request's reads, the pipeline before its loop, the loop, the tail, the
second pass. A loop site is ranked above the loop counter `trip` (`%r6144`, the negated number
of rounds left), which the end of a round increments; the reference invariant says it is the
negated count of rounds left, so it does not wrap (`trip_room`).

Every transition moves to a larger rank, fires a scheduler shuffle, or is a failed poll that
keeps the state (`succ_rank`); a pipeline broadcast is a shuffle that also moves to a larger
rank, and the state counts it (`ps`, `succ_ps`). So the scheduler's shuffles before a state
(the thread's shuffles less the broadcasts), above the rank, are a measure (`measure_step`),
bounded under the reference invariant by the output warp's bound on the scan (`measure_le`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

/-- The rank of the tail's first site, and of the second pass's first site. -/
abbrev T : Nat := 2 ^ 40
abbrev P : Nat := 2 ^ 40 + 64

/-- The rank of a scan's first site. -/
def sbase : Epilogue.Scan → Nat
  | .first => 3 | .loop => 11 | .second => P | .loop2 => P + 8

/-- The rank of a loop round's first site, above the loop counter `t`. -/
abbrev lb (t : BitVec 64) : Nat := 64 + (r32 t).toNat * 128

/-- The ranks of the polls, the broadcasts, the elections and the blocks. -/
def wtR (k : Fin 10) (t : BitVec 64) : Nat :=
  [29, 30, 44, lb t, lb t + 1, lb t + 15, lb t + 28, T + 4, T + 5, T + 19].getD k.val 0
def shR (k : Fin 14) (t : BitVec 64) : Nat :=
  [31, 32, 45, lb t + 2, lb t + 3, lb t + 4, lb t + 16, lb t + 29, lb t + 30, T + 6, T + 7, T + 8,
    T + 20, T + 21].getD k.val 0
def eqR (b : Fin 4) (t : BitVec 64) : Nat := [33, 46, lb t + 17, lb t + 43].getD b.val 0
def qkR (b : Fin 4) (t : BitVec 64) : Nat := [34, 47, lb t + 18, lb t + 44].getD b.val 0
def epR (b : Fin 4) (t : BitVec 64) : Nat := [lb t + 5, lb t + 31, T + 9, T + 22].getD b.val 0
def ceR (c : Fin 12) (t : BitVec 64) : Nat :=
  [42, 55, 57, lb t + 26, lb t + 41, lb t + 52, lb t + 54, T, T + 2, T + 32, T + 34,
    T + 36].getD c.val 0

/-- **The rank of a site**, with loop counter `t`. -/
def pos (s : Site) (t : BitVec 64) : Nat :=
  match s with
  | .bar1 => 0
  | .ldAlloc => 1
  | .bcast => 2
  | .word k => sbase k
  | .down k => sbase k + 1
  | .up k j => sbase k + 2 + j.val
  | .total k => sbase k + 7
  | .vote l => if l then P + 16 else 19
  | .pre l => if l then P + 17 else 20
  | .tiles l => if l then P + 18 else 21
  | .relinq l => if l then P + 19 else 22
  | .bar2 l => if l then P + 20 else 23
  | .dealloc l => if l then P + 21 else 24
  | .exit l => if l then P + 22 else 25
  | .q0 => 26
  | .q1 => 27
  | .uk => 28
  | .wt k => wtR k t
  | .sh k => shR k t
  | .eq b => eqR b t
  | .qk b j => qkR b t + j.val
  | .ep b => epR b t
  | .pv b j => epR b t + 1 + (if j.val ≤ 5 then j.val else j.val + 1)
  | .mw b _ => epR b t + 7
  | .ce c => ceR c t
  | .cm c => ceR c t + 1

theorem r32_lt (t : BitVec 64) : (r32 t).toNat < 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem lb_lt (t : BitVec 64) : lb t + 128 ≤ T := by
  have := r32_lt t
  unfold lb T
  omega

theorem pos_lt (s : Site) (t : BitVec 64) : pos s t < P + 23 := by
  have : lb t + 128 ≤ 2 ^ 40 := lb_lt t
  cases s with
  | word k | down k | up k _ | total k => cases k <;> simp only [pos, sbase, P] <;> omega
  | vote l | pre l | tiles l | relinq l | bar2 l | dealloc l | exit l => cases l <;> simp [pos, P]
  | wt k => fin_cases k <;> simp [pos, wtR, T, P] <;> omega
  | sh k => fin_cases k <;> simp [pos, shR, T, P] <;> omega
  | eq b => fin_cases b <;> simp [pos, eqR, P] <;> omega
  | qk b j => fin_cases b <;> simp [pos, qkR, P] <;> omega
  | ep b => fin_cases b <;> simp [pos, epR, T, P] <;> omega
  | pv b j => fin_cases b <;> simp [pos, epR, T, P] <;> split <;> omega
  | mw b _ => fin_cases b <;> simp [pos, epR, T, P] <;> omega
  | ce c | cm c => fin_cases c <;> simp [pos, ceR, T, P] <;> omega
  | _ => simp only [pos, P]; omega

/-- **The rank of a state.** -/
def rk (d : D) : Nat := pos d.site d.v.trip

/-- The pipeline broadcasts. -/
def Site.isSh : Site → Bool
  | .sh _ => true
  | _ => false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-! ### The broadcasts a state counts -/

theorem scanExit_v (late : Bool) (d : D) (gx cur : BitVec 64) :
    (scanExit p late d gx cur).v.ps = d.v.ps ∧ (scanExit p late d gx cur).v.trip = d.v.trip := by
  unfold scanExit; split <;> exact ⟨rfl, rfl⟩

theorem loopHead_v (late : Bool) (d : D) (grp acc : BitVec 64) :
    (loopHead p L g late d grp acc).v.ps = d.v.ps ∧
      (loopHead p L g late d grp acc).v.trip = d.v.trip := by
  unfold loopHead
  split
  · exact scanExit_v ..
  · split <;> exact ⟨rfl, rfl⟩

theorem afterTotal_v (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    (afterTotal p L g k d x).v.ps = d.v.ps := by
  unfold afterTotal
  cases k <;> simp only <;> split
  all_goals first | exact (scanExit_v ..).1 | exact (loopHead_v ..).1

theorem passStart_v (late : Bool) (d : D) : (passStart p L g late d).v.ps = d.v.ps := by
  simp only [passStart]; split <;> split <;> rfl

theorem setS_ps (v : V) (x : BitVec 64) (k : Fin 14) : (setS v x k).ps = v.ps := by
  fin_cases k <;> rfl

theorem enterLoop_ps (d : D) : (enterLoop p L g d).v.ps = d.v.ps := by
  unfold enterLoop; split <;> rfl

theorem loopEnd_ps (d : D) : (loopEnd d).v.ps = d.v.ps := by
  unfold loopEnd; split <;> rfl

theorem ceNext_ps (d : D) (c : Fin 12) : (ceNext p L g d c).v.ps = d.v.ps := by
  fin_cases c <;> simp [ceNext, enterLoop_ps, loopEnd_ps, passStart_v]

theorem afterTiles_ps {d d' : D} {x : BitVec 64} (h : afterTiles p L g d x = some d') :
    d'.v.ps = d.v.ps := by
  simp only [afterTiles] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; subst h; split <;> rfl
    · cases h
  · cases h

/-- **A step counts the broadcast it fires.** -/
theorem succ_ps {d d' : D} {e : Event} (h : succ p L g d e = some (some d')) :
    d'.v.ps = d.v.ps + if d.site.isSh then 1 else 0 := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v⟩ := d
  cases s <;> simp only [succ] at h
  all_goals (repeat' (first | split at h | (simp only [word32] at h)))
  all_goals try (cases h; done)
  all_goals try (simp only [Option.some.injEq] at h; subst h)
  all_goals first
    | (simp [Site.isSh, afterTotal_v, passStart_v, ceNext_ps]; done)
    | (obtain ⟨_, h1, h2⟩ := Option.map_eq_some_iff.mp h
       cases h2
       exact afterTiles_ps h1)

/-! ### The ranks of the steps -/

theorem setS_trip (v : V) (x : BitVec 64) (k : Fin 14) : (setS v x k).trip = v.trip := by
  fin_cases k <;> rfl

theorem rk_passStart_true (d : D) : P ≤ rk (passStart p L g true d) := by
  simp only [passStart, rk, ↓reduceIte]
  split <;> simp [pos, sbase]

/-- The commits' successors move to a larger rank; the end of a round (`c = 6`) when the loop
counter has room. -/
theorem ceNext_rk (d : D) (c : Fin 12) (ht : c = 6 → (r32 d.v.trip).toNat + 1 < 2 ^ 32) :
    ceR c d.v.trip + 1 < rk (ceNext p L g d c) := by
  have := r32_lt d.v.trip
  fin_cases c
  all_goals simp only [ceNext, ceR, rk]
  case «2» =>
    unfold enterLoop
    split <;> simp [pos, wtR, ceR, T, lb]; omega
  case «6» =>
    have ht' := ht rfl
    unfold loopEnd
    split
    · simp [pos, wtR, lb, r32_addi1 ht']; omega
    · simp [pos, ceR, T, lb]; omega
  case «11» =>
    have := rk_passStart_true (p := p) (L := L) (g := g) d
    simp only [rk] at this
    simp [T, P, lb] at this ⊢
    omega
  all_goals simp [pos, wtR, ceR, eqR, T, lb]

/-- **Every transition of the MMA warp moves to a larger rank, fires a scheduler shuffle, or is a
failed poll** that keeps the state, when the loop counter has room at a round's end. -/
theorem succ_rank {d d' : D} {e : Event} (h : succ p L g d e = some (some d'))
    (ht : d.site = .ce 6 ∨ d.site = .cm 6 → (r32 d.v.trip).toNat + 1 < 2 ^ 32) :
    rk d < rk d' ∨ (d.site.isSh = false ∧ Execution.isShfl e = true) ∨
      (d' = d ∧ e.counts = false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v⟩ := d
  have := lb_lt v.trip
  cases s with
  | bcast | down k | up k j | total k | pre l | tiles l =>
    right; left
    cases kind <;> first | exact ⟨rfl, rfl⟩ | simp [succ] at h
  | bar1 =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    simp [rk, pos]
  | relinq l | bar2 l | dealloc l =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases l <;> simp [rk, pos]
  | exit l => simp [succ] at h
  | word k =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        cases k <;> simp [rk, pos, sbase]
      · cases h
    · cases h
  | ldAlloc | q0 | q1 | uk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    all_goals try (cases h; done)
    all_goals try (unfold word32 at h; split at h)
    all_goals try (cases h; done)
    all_goals simp only [Option.some.injEq] at h
    all_goals subst h
    all_goals simp [rk, pos, wtR]
  | vote l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    cases l <;> split <;> simp [rk, pos]
  | wt k =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      fin_cases k <;> simp [rk, pos, wtR, wtNext, shR, T, lb]
  | sh k =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      fin_cases k <;> simp [rk, pos, shR, shNext, eqR, epR, setS_trip, T, lb]
    · cases h
  | eq b =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    fin_cases b <;> split <;> simp [rk, pos, eqR, qkR, qkDone, ceR, T, lb]
  | qk b j =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    have := j.isLt
    fin_cases b <;> split <;> simp [rk, pos, qkR, qkDone, ceR, T, lb, Fin.val_add] <;> omega
  | ep b =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    split <;> simp [rk, pos]
  | pv b j =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    have := j.isLt
    fin_cases b <;> split <;> (try split) <;>
      simp_all [rk, pos, epR, pvDone, wtR, ceR, T, lb, Fin.val_add] <;> (try split_ifs) <;>
      omega
  | mw b ld =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      fin_cases b <;> cases ld <;> simp [rk, pos, epR, pvDone, wtR, ceR, T, lb]
  | ce c =>
    left
    have hc := ceNext_rk (p := p) (L := L) (g := g) ⟨.ce c, v⟩ c
      (fun h6 => ht (.inl (by rw [h6])))
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    split
    · simp [rk, pos]
    · simpa [rk, pos] using Nat.lt_of_succ_lt hc
  | cm c =>
    left
    have hc := ceNext_rk (p := p) (L := L) (g := g) ⟨.cm c, v⟩ c
      (fun h6 => ht (.inr (by rw [h6])))
    simp only [succ, Option.some.injEq] at h
    subst h
    simpa [rk, pos] using hc

/-! ### The measure -/

/-- The weight of a scheduler shuffle: above every rank. -/
abbrev W : Nat := P + 23

/-- **The measure of a state** past `ns` shuffles: the scheduler's shuffles (less the state's
broadcasts) above the rank. -/
def measure (d : D) (ns : Nat) : Nat := (ns - d.v.ps) * W + rk d

/-- A broadcast site fires a shuffle. -/
theorem sh_shfl {d d' : D} {e : Event} (h : succ p L g d e = some (some d'))
    (hs : d.site.isSh = true) : Execution.isShfl e = true := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v⟩ := d
  cases s <;> simp only [Site.isSh, Bool.false_eq_true] at hs
  cases kind <;> first | rfl | simp [succ] at h

/-- **The measure never decreases along a transition, and increases at every counted event**;
`ns'` is the count of shuffles after the event (the thread machine's ledger, `Code.bump`), and
the state's broadcasts are at most the thread's shuffles. -/
theorem measure_step {d d' : D} {e : Event} {ns ns' : Nat}
    (h : succ p L g d e = some (some d'))
    (ht : d.site = .ce 6 ∨ d.site = .cm 6 → (r32 d.v.trip).toNat + 1 < 2 ^ 32)
    (hps : d.v.ps ≤ ns) (hn : ns' = ns + if Execution.isShfl e then 1 else 0) :
    measure d ns ≤ measure d' ns' ∧ (e.counts = true → measure d ns < measure d' ns') := by
  have h1 : rk d < W := pos_lt _ _
  have h2 : rk d' < W := pos_lt _ _
  have hp' := succ_ps h
  have hw : ns - d.v.ps ≤ ns' - d'.v.ps := by
    by_cases hs : d.site.isSh = true
    · rw [sh_shfl h hs] at hn; simp only [hs, ↓reduceIte] at hp' hn; omega
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hp'
      split at hn <;> omega
  unfold measure
  generalize W = w at h1 h2 ⊢
  have hle : (ns - d.v.ps) * w ≤ (ns' - d'.v.ps) * w := Nat.mul_le_mul_right w hw
  rcases succ_rank h ht with hr | ⟨hs, hsh⟩ | ⟨rfl, hc⟩
  · omega
  · simp only [hs, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hp'
    simp only [hsh, ↓reduceIte] at hn
    have : ns' - d'.v.ps = (ns - d.v.ps) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega
  · rw [hc]
    simp only [Bool.false_eq_true, false_implies, and_true]
    omega

/-- **The loop counter has room at a round's end**: the reference invariant says it is the
negated number of rounds left, at least two. -/
theorem trip_room {d : D} {n : Cnt → Nat} (hJ : RefCounts p L g (d, n))
    (hs : d.site = .ce 6 ∨ d.site = .cm 6) : (r32 d.v.trip).toNat + 1 < 2 ^ 32 := by
  obtain ⟨r, w, hQ, -⟩ := hJ
  have hq : 20 ≤ d.site.ord ∧ d.site.ord < 60 := by
    rcases hs with hs | hs <;> rw [hs] <;> decide
  obtain ⟨hr, ht⟩ := hQ.loop hq
  have hB := toSigned32_lt (r32 (blocks p L g d.v))
  rw [ht]
  exact i32_room (by simp only [Bs] at hr ⊢; omega) (by simp only [Bs] at hr ⊢; omega)

/-- **The measure of a state that holds the reference values is bounded.** -/
theorem measure_le (hp : Pre p L m) {d : D} {ns nv : Nat} (hF : MFits p L g d ns nv) :
    measure d ns ≤ (14 * p.batch + 29) * W := by
  have hc : ns - d.v.ps ≤ 14 * p.batch + 28 := by
    unfold MFits at hF
    split at hF
    · omega
    · have := Epilogue.fits_coll_le_all hp hF.2.1
      omega
  have h2 : rk d < W := pos_lt _ _
  unfold measure
  generalize W = w at h2 ⊢
  have : (ns - d.v.ps) * w ≤ (14 * p.batch + 28) * w := Nat.mul_le_mul_right w hc
  rw [show 14 * p.batch + 29 = (14 * p.batch + 28) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
