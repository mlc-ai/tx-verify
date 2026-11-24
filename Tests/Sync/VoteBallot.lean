-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode

/-! `vote.sync.ballot.b32` (§9.7.15.10): decoding, the ballot event, the value written to the
destination, and the instance constraint `VoteOk` (DEP-WARP-VOTE) on the ballot value. -/
namespace PTX.Tests.VoteBallot
open PTX.Syntax
noncomputable section

/-! ## Decoding -/

-- `%r0`, `%r1` are registers 0, 1 (32-bit); `%p0`, `%p1` are registers 2, 3 (predicates).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 2, 32⟩, ⟨"%p".toList, 2, 1⟩], labels := [], params := [] }

example : Decode.op env "vote.sync.ballot.b32" [.register "%r0", .register "%p0", .literal "-1"] =
    .ok (.warp {
      kind := .vote .ballot false, ty := some (.int .b 32), dsts := [some 0], srcs := [.reg 2],
      mask := some (.imm (-1)) }) := rfl
example : Decode.op env "vote.sync.ballot.b32"
    [.register "%r0", .negate (.register "%p0"), .literal "-1"] =
    .ok (.warp {
      kind := .vote .ballot true, ty := some (.int .b 32), dsts := [some 0], srcs := [.reg 2],
      mask := some (.imm (-1)) }) := rfl
-- "Operand a is a predicate register."; "the destination operand d is a .b32 register."
example : (Decode.op env "vote.sync.ballot.b32"
    [.register "%r0", .register "%r1", .literal "-1"]).isOk = false := rfl
example : (Decode.op env "vote.sync.ballot.b32"
    [.register "%p1", .register "%p0", .literal "-1"]).isOk = false := rfl
-- The `.all`, `.any`, `.uni` modes are THREAD-VOTE's mode forms (Tests/Sync/VoteModes.lean).
example : WarpInstr.rule {
    kind := .vote .any false, ty := some .pred, dsts := [some 3], srcs := [.reg 2],
    mask := some (.imm (-1)) } = some .threadVote := rfl

/-! ## The event and the value it writes -/

private def launch : Launch := { grid := 1, block := 32, params := fun _ => none }
private def t (b : Bool) : TState := { regs := fun r => if r = 2 then some (.pred b) else none }

-- With the full member mask the event carries the lane's predicate, complemented by `!`.
example : voteTmpl launch 0 (t true) 0 2 false (.imm (-1)) =
    .vote (2 ^ 32 - 1) true (fun ballot =>
      next (setReg (t true) 0 (.bits 32 (BitVec.ofNat 64 ballot.toNat)))) := rfl
example : voteTmpl launch 0 (t true) 0 2 true (.imm (-1)) =
    .vote (2 ^ 32 - 1) false (fun ballot =>
      next (setReg (t true) 0 (.bits 32 (BitVec.ofNat 64 ballot.toNat)))) := rfl
-- Another member mask has no rule; a non-predicate source is a type error.
example : voteTmpl launch 0 (t true) 0 2 false (.imm 3) = .ub .noRule := rfl
example : voteTmpl launch 0 {} 0 2 false (.imm (-1)) = .ub .uninitialized := rfl
-- The ballot received is written to the destination as a 32-bit integer.
example : Fires 7 (voteTmpl launch 0 (t true) 0 2 false (.imm (-1)))
    ⟨7, .vote (2 ^ 32 - 1) true 0x55555555#32⟩
    (some (next (setReg (t true) 0 (.bits 32 0x55555555#64)))) := ⟨_, rfl, rfl⟩

/-! ## The ballot of one instance

Each lane of one warp executes one `vote.sync.ballot.b32` with predicate "lane is even". -/

private def full : Nat := 2 ^ 32 - 1

private def execution (ballot : BitVec 32) : Execution := {
  tr := fun g => if g < 32 then [⟨0, .vote full (decide (g % 2 = 0)) ballot⟩] else []
  rf := fun _ _ => none
}

private theorem even_bits : ∀ h < 32, (0x55555555#32).getLsbD h = decide (h % 2 = 0) := by
  decide

private theorem full_bits : ∀ h < 32, full.testBit h = true := by decide

/-- The instance of the ballots: every lane takes part with predicate "lane is even". -/
private def evenPart (lane : Nat) : Option Bool :=
  if lane < 32 then some (decide (lane % 2 = 0)) else none

private theorem get_execution {ballot : BitVec 32} {g i pc : Nat} {k : Kind}
    (h : (execution ballot).get (g, i) = some ⟨pc, k⟩) :
    g < 32 ∧ i = 0 ∧ k = .vote full (decide (g % 2 = 0)) ballot := by
  by_cases hg : g < 32
  · obtain _ | i := i
    · simp only [Execution.get, execution, hg, ite_true, List.getElem?_cons_zero,
        Option.some.injEq, Event.mk.injEq] at h
      exact ⟨hg, rfl, h.2.symm⟩
    · simp [Execution.get, execution, hg] at h
  · simp [Execution.get, execution, hg] at h

/-- Every instance of the ballots of the execution is `evenPart` on the lanes of the warp. -/
private theorem part_eq {ballot : BitVec 32} {g n : Nat} {part : Nat → Option Bool} (hg : g < 32)
    (hi : MaskInstance launch voteClass (execution ballot) g full n .ballot part) :
    ∀ lane < 32, part lane = some (decide (lane % 2 = 0)) := by
  intro lane hl
  have hb : g - laneOf launch g + lane = lane := by
    simp [laneOf, launch, Nat.mod_eq_of_lt hg]
  rcases (hi lane hl).1 (full_bits lane hl) with ⟨j, pc, k, v, hj, hc, -, hp⟩ |
      ⟨⟨k, pc, hk, -⟩, -⟩
  · rw [hb] at hj
    obtain ⟨-, -, rfl⟩ := get_execution hj
    simp only [voteClass, Option.some.injEq, WarpPart.mk.injEq] at hc
    rw [hp, ← hc.2.2]
  · rw [hb] at hk
    obtain ⟨-, -, h⟩ := get_execution hk
    cases h

-- The ballot holds every lane's predicate in its lane's bit.
theorem ballot_ok : VoteOk launch (execution 0x55555555#32) := by
  intro g i n pc mask a ballot hget hk part hpart lane hl
  obtain ⟨hg, rfl, h⟩ := get_execution hget
  simp only [Kind.vote.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨fun b hb => ?_, fun hm => ?_⟩
  · rw [part_eq hg hpart lane hl] at hb
    cases hb
    exact even_bits lane hl
  · rw [full_bits lane hl] at hm; cases hm

-- A ballot that does not hold the predicates is not a possible value.
theorem wrong_ballot : ¬ VoteOk launch (execution 0#32) := by
  intro hv
  have hinst : MaskInstance launch voteClass (execution 0#32) 0 full 0 .ballot evenPart := by
    intro lane hl
    refine ⟨fun _ => .inl ⟨0, 0, .vote full (decide (lane % 2 = 0)) 0#32,
      decide (lane % 2 = 0), ?_, rfl, ⟨⟨⟨0, .vote full (decide (lane % 2 = 0)) 0#32⟩,
        ⟨full, .ballot, decide (lane % 2 = 0)⟩, ?_, rfl, rfl⟩, rfl⟩, by simp [evenPart, hl]⟩,
      fun hm => by rw [full_bits lane hl] at hm; cases hm⟩ <;>
      simp [Execution.get, execution, hl]
  have h := (hv 0 0 0 0 full true 0#32 (by simp [Execution.get, execution])
    ⟨⟨⟨0, .vote full true 0#32⟩, ⟨full, .ballot, true⟩, by simp [Execution.get, execution],
      rfl, rfl⟩, rfl⟩ evenPart hinst 0
    (by decide)).1 true (by simp [evenPart])
  simp at h

end
end PTX.Tests.VoteBallot
