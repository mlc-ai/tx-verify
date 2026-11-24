-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! `vote.sync` with a mode (§9.7.15.10): decoding, the rule, the template with its fault cases,
the reduction `voteResult` at its boundaries, and the instance constraint `VoteModeOk`
(DEP-WARP-VOTE, DEP-WARP-INSTANCE) with a complete instance, a wrong result and an exited lane, and
the waiting dependency (DEP-ORDER) with a qualifier disagreement with a ballot, a mode disagreement
and a mask disagreement. -/
namespace PTX.Tests.VoteModes
open PTX.Syntax
noncomputable section

/-! ## Decoding and rules -/

-- `%r0`, `%r1` are registers 0, 1 (32-bit); `%p0`, `%p1` are registers 2, 3 (predicates).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 2, 32⟩, ⟨"%p".toList, 2, 1⟩], labels := [], params := [] }

private def allPred : WarpInstr :=
  { kind := .vote .all false, ty := some .pred, dsts := [some 2], srcs := [.reg 3],
    mask := some (.imm 3) }

example : Decode.op env "vote.sync.all.pred" [.register "%p0", .register "%p1", .literal "3"] =
    .ok (.warp allPred) := rfl
example : allPred.rule = some .threadVote := rfl
-- A negated source `!a` and a register member mask.
example : Decode.op env "vote.sync.any.pred"
    [.register "%p0", .negate (.register "%p1"), .register "%r1"] =
    .ok (.warp { allPred with kind := .vote .any true, mask := some (.reg 1) }) := rfl
example : Decode.op env "vote.sync.uni.pred" [.register "%p0", .register "%p1", .literal "3"] =
    .ok (.warp { allPred with kind := .vote .uni false }) := rfl
example : WarpInstr.rule { allPred with kind := .vote .uni true } = some .threadVote := rfl
-- "The destination operand d is a predicate register"; "Operand a is a predicate register."
example : (Decode.op env "vote.sync.all.pred"
    [.register "%r0", .register "%p1", .literal "3"]).isOk = false := rfl
example : (Decode.op env "vote.sync.all.pred"
    [.register "%p0", .register "%r1", .literal "3"]).isOk = false := rfl
-- Guard divergence on a vote is unsafe.
example : Op.uniform (.warp allPred) = true := rfl
example : Op.uniform (.warp { allPred with kind := .vote .any true }) = true := rfl

/-! ## The event -/

-- One warp of two threads; lane 0 holds the predicate true in register 3 and the mask 3 in
-- register 1.
private def launch : Launch := { grid := 1, block := 2, params := fun _ => none }
private def t : TState :=
  { regs := fun r => if r = 3 then some (.pred true) else if r = 1 then some (.bits 32 3#64)
    else none }

example : voteModeTmpl launch 0 t .all 2 3 false (.imm 3) =
    .voteMode .all 3 true (fun r => next (setReg t 2 (.pred r))) := rfl
-- The negation complements the predicate.
example : voteModeTmpl launch 0 t .any 2 3 true (.imm 3) =
    .voteMode .any 3 false (fun r => next (setReg t 2 (.pred r))) := rfl
-- A register member mask is read.
example : voteModeTmpl launch 0 t .uni 2 3 false (.reg 1) =
    .voteMode .uni 3 true (fun r => next (setReg t 2 (.pred r))) := rfl
example : eventTmpl [] launch 0 t (.warp allPred) =
    .voteMode .all 3 true (fun r => next (setReg t 2 (.pred r))) := rfl
example : eventTmpl [] launch 0 t (.warp { allPred with kind := .vote .any true }) =
    .voteMode .any 3 false (fun r => next (setReg t 2 (.pred r))) := rfl
-- "The behavior of vote.sync is undefined if the executing thread is not in the membermask ."
example : voteModeTmpl launch 0 t .all 2 3 false (.imm 2) = .ub .badValue := rfl
example : voteModeTmpl launch 1 t .all 2 3 false (.imm 1) = .ub .badValue := rfl
-- A member mask that names a lane with no thread has no rule.
example : voteModeTmpl launch 0 t .all 2 3 false (.imm 7) = .ub .noRule := rfl
-- An unset predicate register is a fault; a non-predicate source is a type error.
example : voteModeTmpl launch 0 {} .all 2 3 false (.imm 3) = .ub .uninitialized := rfl
example : voteModeTmpl launch 0 t .all 2 1 false (.imm 3) = .ub .typeMismatch := rfl
-- The predicate received is written to the destination.
example : Fires 4 (voteModeTmpl launch 0 t .all 2 3 false (.imm 3))
    ⟨4, .voteMode .all 3 true false⟩ (some (next (setReg t 2 (.pred false)))) :=
  ⟨_, rfl, rfl⟩

/-! ## The reduction at its boundaries -/

private def two (a b : Option Bool) : Nat → Option Bool := fun lane =>
  if lane = 0 then a else if lane = 1 then b else none

example : voteResult .all (two (some true) (some true)) = true := by decide
example : voteResult .all (two (some true) (some false)) = false := by decide
example : voteResult .any (two (some false) (some false)) = false := by decide
example : voteResult .any (two (some false) (some true)) = true := by decide
example : voteResult .uni (two (some true) (some true)) = true := by decide
example : voteResult .uni (two (some false) (some false)) = true := by decide
example : voteResult .uni (two (some true) (some false)) = false := by decide
-- One participant.
example : voteResult .all (two (some false) none) = false := by decide
example : voteResult .any (two (some true) none) = true := by decide
example : voteResult .uni (two (some true) none) = true := by decide
-- An exited lane (`none`) takes no part: the other lane alone decides.
example : voteResult .all (two none (some true)) = true := by decide
example : voteResult .any (two (some false) none) = false := by decide
example : voteResult .uni (two none (some false)) = true := by decide

/-! ## Instances

Thread `h` of the warp performs the events `tr h`; the threads 0 and 1 are lanes 0 and 1. -/

private def exec (tr : Nat → List Event) : Execution := { tr := tr, rf := fun _ _ => none }

/-- Lane 0 performs `k0` and lane 1 performs `k1`. -/
private def both (k0 k1 : Kind) : Execution :=
  exec fun g => if g = 0 then [⟨0, k0⟩] else if g = 1 then [⟨0, k1⟩] else []

private theorem lane_eq (g : Nat) (hg : g < 2) : g - laneOf launch g = 0 := by
  simp [laneOf, launch, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt (by omega : g < 32)]

private theorem bit3 (lane : Nat) (hl : lane < 32) (hb : (3 : Nat).testBit lane = true) :
    lane < 2 := by
  by_contra hn
  have : (3 : Nat) < 2 ^ lane :=
    lt_of_lt_of_le (by decide : (3 : Nat) < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow this] at hb
  cases hb

private theorem get_both {k0 k1 : Kind} {h j pc : Nat} {k : Kind}
    (hj : (both k0 k1).get (h, j) = some ⟨pc, k⟩) :
    (h = 0 ∧ j = 0 ∧ k = k0) ∨ (h = 1 ∧ j = 0 ∧ k = k1) := by
  unfold both exec Execution.get at hj
  by_cases h0 : h = 0
  · subst h0; obtain _ | j := j <;> simp_all
  · by_cases h1 : h = 1
    · subst h1; obtain _ | j := j <;> simp_all
    · simp [h0, h1] at hj

/-- Lane 0 contributes `a0` and lane 1 contributes `a1`. -/
private def partOf (a0 a1 : Bool) : Nat → Option Bool := two (some a0) (some a1)

private theorem both_instance (m : VoteMode) (a0 a1 r0 r1 : Bool) (g : Nat) (hg : g < 2) :
    MaskInstance launch voteClass (both (.voteMode m 3 a0 r0) (.voteMode m 3 a1 r1)) g 3 0 m
      (partOf a0 a1) := by
  intro lane hl
  rw [lane_eq g hg, Nat.zero_add]
  refine ⟨fun hb => .inl ?_, fun hb => ?_⟩
  · have := bit3 lane hl hb
    obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
    · exact ⟨0, 0, _, a0, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨0, 0, _, a1, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
  · have : lane ≠ 0 ∧ lane ≠ 1 := by
      constructor <;> rintro rfl <;> exact absurd hb (by decide)
    simp [partOf, two, this.1, this.2]

/-- The reduction depends only on the lanes below 32. -/
private theorem result_congr (m : VoteMode) (p q : Nat → Option Bool)
    (h : ∀ lane ∈ List.range 32, p lane = q lane) : voteResult m p = voteResult m q := by
  unfold voteResult
  rw [List.filterMap_congr h]

/-- The reduction of the instance of a complete pair of votes is that of the predicates of the two
lanes. -/
private theorem part_eq (m : VoteMode) (a0 a1 r0 r1 : Bool) (g : Nat) (hg : g < 2)
    (part : Nat → Option Bool)
    (hi : MaskInstance launch voteClass (both (.voteMode m 3 a0 r0) (.voteMode m 3 a1 r1)) g 3 0
      m part) :
    voteResult m part = voteResult m (partOf a0 a1) := by
  apply result_congr
  intro lane hl
  have hl := List.mem_range.mp hl
  by_cases h2 : lane < 2
  · have hb : (3 : Nat).testBit lane = true := by
      obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
      all_goals decide
    rcases (hi lane hl).1 hb with ⟨j, pc, k, v, hj, hc, -, hpv⟩ | ⟨⟨k, pc, hk, -⟩, -⟩
    · rw [lane_eq g hg, Nat.zero_add] at hj
      obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
      · rcases get_both hj with ⟨-, -, rfl⟩ | ⟨h, -⟩
        · simp [voteClass] at hc
          rw [hpv, ← hc]; rfl
        · cases h
      · rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
        · cases h
        · simp [voteClass] at hc
          rw [hpv, ← hc]; rfl
    · rw [lane_eq g hg, Nat.zero_add] at hk
      rcases get_both hk with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> cases h
  · have hb : (3 : Nat).testBit lane = false := by
      rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
      · exact absurd (bit3 lane hl h) h2
      · exact h
    rw [(hi lane hl).2 hb]
    simp [partOf, two, show lane ≠ 0 by omega, show lane ≠ 1 by omega]

/-- Both lanes of a pair of votes with one mode and member mask hold exactly when both received
the reduction of the two predicates. -/
private theorem both_ok_iff (m : VoteMode) (a0 a1 r0 r1 : Bool) :
    VoteModeOk launch (both (.voteMode m 3 a0 r0) (.voteMode m 3 a1 r1)) ↔
      r0 = voteResult m (partOf a0 a1) ∧ r1 = voteResult m (partOf a0 a1) := by
  constructor
  · intro h
    exact ⟨h 0 0 0 m 3 a0 r0 0 rfl ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩ _
        (both_instance m a0 a1 r0 r1 0 (by omega)),
      h 1 0 0 m 3 a1 r1 0 rfl ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩ _
        (both_instance m a0 a1 r0 r1 1 (by omega))⟩
  · rintro ⟨h0, h1⟩ g i pc mode mask a r n hget hk
    have hn : n = 0 := by
      rcases get_both hget with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simpa using hk.2.symm
    subst hn
    rcases get_both hget with ⟨rfl, -, h⟩ | ⟨rfl, -, h⟩ <;>
      simp only [Kind.voteMode.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    · intro part hi
      exact h0.trans (part_eq _ a a1 r r1 0 (by omega) part hi).symm
    · intro part hi
      exact h1.trans (part_eq _ a0 a r0 r 1 (by omega) part hi).symm

-- Both lanes vote true and receive true.
theorem all_ok :
    VoteModeOk launch (both (.voteMode .all 3 true true) (.voteMode .all 3 true true)) :=
  (both_ok_iff .all true true true true).2 ⟨by decide, by decide⟩
-- One lane votes false, so `.all` is false and a lane that received true is rejected.
theorem all_wrong :
    ¬ VoteModeOk launch (both (.voteMode .all 3 true true) (.voteMode .all 3 false false)) :=
  fun h => absurd ((both_ok_iff .all true false true false).1 h).1 (by decide)
-- The same votes under `.any` give true to both lanes.
theorem any_ok :
    VoteModeOk launch (both (.voteMode .any 3 true true) (.voteMode .any 3 false true)) :=
  (both_ok_iff .any true false true true).2 ⟨by decide, by decide⟩
theorem uni_wrong :
    ¬ VoteModeOk launch (both (.voteMode .uni 3 true true) (.voteMode .uni 3 false true)) :=
  fun h => absurd ((both_ok_iff .uni true false true true).1 h).1 (by decide)

/-- The instance of lane 0 exists: lane 0 takes part with its predicate and lane 1 is an exited
lane of the mask, which takes no part. -/
theorem exited_instance : MaskInstance launch voteClass (both (.voteMode .all 3 true true) .exit)
    0 3 0 .all (two (some true) none) := by
  intro lane hl
  rw [lane_eq 0 (by omega), Nat.zero_add]
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have := bit3 lane hl hb
    obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
    · exact .inl ⟨0, 0, _, true, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · exact .inr ⟨⟨0, 0, rfl, by simp⟩, rfl⟩
  · have : lane ≠ 0 ∧ lane ≠ 1 := by
      constructor <;> rintro rfl <;> exact absurd hb (by decide)
    simp [two, this.1, this.2]

/-- The vote of lane 0 is ready: lane 0's own event and the exit of lane 1 fill its needs
(DEP-ORDER). -/
theorem exited_ready : Ready launch (both (.voteMode .all 3 true true) .exit) (0, 0) := by
  have hat : (both (.voteMode .all 3 true true) .exit).MaskAt voteClass (0, 0) 3 0 .all :=
    ⟨⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, _, _, rfl, rfl, rfl⟩
  intro n hn
  simp only [Needs, KindNeeds, maskNeeds, both, exec, Execution.get] at hn
  simp only [ite_true, List.getElem?_cons_zero, Option.bind_some, voteClass] at hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  have hl : l < 2 := by
    obtain ⟨hl, hb⟩ := List.mem_filter.mp hl
    exact bit3 l (List.mem_range.mp hl) hb
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨.thread (0, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inl hat⟩
  · exact ⟨.thread (1, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inr ⟨rfl, ⟨0, rfl⟩, by simp⟩⟩

/-- Lane 1 exited before the vote: lane 0 receives the reduction of its own predicate. -/
theorem exited_ok : VoteModeOk launch (both (.voteMode .all 3 true true) .exit) := by
  intro g i pc mode mask a r n hget hk
  have hn : n = 0 := by
    rcases get_both hget with ⟨-, rfl, -⟩ | ⟨-, rfl, h⟩ <;> simpa using hk.2.symm
  subst hn
  rcases get_both hget with ⟨rfl, -, h⟩ | ⟨-, -, h⟩
  · simp only [Kind.voteMode.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    intro part hi
    rw [result_congr _ part (two (some true) none) ?_]
    · decide
    intro lane hl
    have hl := List.mem_range.mp hl
    have hi' := hi lane hl
    rw [lane_eq 0 (by omega), Nat.zero_add] at hi'
    by_cases h2 : lane < 2
    · obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
      · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, hpv⟩ | ⟨⟨k, pc, hk, -⟩, -⟩
        · rcases get_both hj with ⟨-, -, rfl⟩ | ⟨h, -⟩
          · simp [voteClass] at hc
            rw [hpv, ← hc]; rfl
          · cases h
        · rcases get_both hk with ⟨-, -, h⟩ | ⟨h, -⟩
          · cases h
          · cases h
      · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, -⟩ | ⟨-, hpn⟩
        · rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
          · cases h
          · simp [voteClass] at hc
        · rw [hpn]; rfl
    · have hb : (3 : Nat).testBit lane = false := by
        rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
        · exact absurd (bit3 lane hl h) h2
        · exact h
      rw [hi'.2 hb]
      simp [two, show lane ≠ 0 by omega, show lane ≠ 1 by omega]
  · cases h

/-- Lane 1 performs `k1`, which is not a vote of mode `m` with member mask 3 and not an exit,
while lane 0 votes with mode `m`: the vote of lane 0 is not ready, so no consistent execution
contains it (`DependencyOk.ready`). -/
private theorem mismatch (m : VoteMode) (a0 r0 : Bool) (k1 : Kind)
    (hc : ∀ v, voteClass k1 ≠ some ⟨3, m, v⟩) (he : k1 ≠ .exit) :
    ¬ Ready launch (both (.voteMode m 3 a0 r0) k1) (0, 0) := by
  intro hr
  have hg0 : (both (.voteMode m 3 a0 r0) k1).get (0, 0) = some ⟨0, .voteMode m 3 a0 r0⟩ := rfl
  have hn := maskNeeds_mem launch voteClass _ (0, 0) hg0 (p := ⟨3, m, a0⟩) rfl
    (l := 1) (by decide) (show (3 : Nat).testBit 1 = true by decide)
  have hN : Needs launch (both (.voteMode m 3 a0 r0) k1) (0, 0) =
      maskNeeds launch voteClass (both (.voteMode m 3 a0 r0) k1) (0, 0) := by
    simp [Needs, hg0, KindNeeds]
  obtain ⟨x, -, j, rfl, hw⟩ := hr _ (hN ▸ hn)
  obtain ⟨-, m', n, q, ⟨⟨⟨ev, p, hg, hp, hm⟩, -⟩, ev', p', hg', hp', hq⟩, hw⟩ := hw
  rw [hg0] at hg hg'
  cases hg
  cases hg'
  simp only [voteClass, Option.some.injEq] at hp hp'
  subst hp hp'
  subst hm hq
  have hl : warpLane launch 0 1 = 1 := rfl
  rw [hl] at hw
  rcases hw with ⟨⟨⟨⟨pc, k⟩, p, hj, hk, hm⟩, -⟩, ev2, p2, hj2, hk2, hq2⟩ | ⟨-, ⟨pc, hk⟩, -⟩
  · rw [hj] at hj2
    cases hj2
    rw [hk] at hk2
    cases hk2
    rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
    · cases h
    · obtain ⟨mask, qual, v⟩ := p
      simp only at hm hq2
      subst hm hq2
      exact hc v hk
  · rcases get_both hk with ⟨h, -⟩ | ⟨-, -, h⟩
    · cases h
    · exact he h.symm

-- Lane 1 votes with the same member mask as a ballot, which the text does not pair with a mode
-- vote ("the same qualifiers").
theorem ballot_rejected :
    ¬ Ready launch (both (.voteMode .all 3 true true) (.vote 3 true 3#32)) (0, 0) :=
  mismatch .all true true _ (by simp [voteClass]) (by simp)

-- Lane 1 votes with `.any` while lane 0 votes with `.all`.
theorem mode_rejected :
    ¬ Ready launch (both (.voteMode .all 3 true true) (.voteMode .any 3 true true)) (0, 0) :=
  mismatch .all true true _ (by simp [voteClass]) (by simp)

-- Lane 1 votes with member mask 2 while lane 0 waits for it with member mask 3.
theorem mask_rejected :
    ¬ Ready launch (both (.voteMode .all 3 true true) (.voteMode .all 2 true true)) (0, 0) :=
  mismatch .all true true _ (by simp [voteClass]) (by simp)

end
end PTX.Tests.VoteModes
