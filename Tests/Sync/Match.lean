-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! `match.sync` (§9.7.15.11): decoding, the rule of each form, the mask and predicate that an
instance delivers at their boundaries, the event, and the instance constraint `MatchOk`
(DEP-WARP-MATCH, DEP-WARP-INSTANCE) with a complete instance, a wrong mask and an exited lane, and
the waiting dependency (DEP-ORDER) with a mode, a type and a mask disagreement. -/
namespace PTX.Tests.Match
open PTX.Syntax
noncomputable section

/-! ## Decoding and rules -/

-- `%r0`, `%r1` are registers 0, 1 (32-bit); `%rd0`, `%rd1` are registers 2, 3 (64-bit);
-- `%p0`, `%p1` are registers 4, 5 (predicates).
private def env : Decode.Env :=
  { classes := [⟨"%r".toList, 2, 32⟩, ⟨"%rd".toList, 2, 64⟩, ⟨"%p".toList, 2, 1⟩], labels := [],
      params := [] }

private def any32 : WarpInstr :=
  { kind := .match_ false, ty := some (.int .b 32), dsts := [some 0], srcs := [.reg 1],
    mask := some (.imm 3) }

example : Decode.op env "match.any.sync.b32" [.register "%r0", .register "%r1", .literal "3"] =
    .ok (.warp any32) := rfl
example : any32.rule = some .threadMatch := rfl
-- `.b64`: the operand is a 64-bit register and the destination stays 32-bit.
private def any64 : WarpInstr := { any32 with ty := some (.int .b 64), srcs := [.reg 3] }
example : Decode.op env "match.any.sync.b64" [.register "%r0", .register "%rd1", .literal "3"] =
    .ok (.warp any64) := rfl
example : any64.rule = some .threadMatch := rfl
example : (Decode.op env "match.any.sync.b64"
    [.register "%r0", .register "%r1", .literal "3"]).isOk = false := rfl
-- `.all` with only `d`, and with `d|p`.
private def all32 : WarpInstr := { any32 with kind := .match_ true }
example : Decode.op env "match.all.sync.b32" [.register "%r0", .register "%r1", .literal "3"] =
    .ok (.warp all32) := rfl
example : all32.rule = some .threadMatch := rfl
private def all64p : WarpInstr :=
  { any64 with kind := .match_ true, dsts := [some 0, some 5] }
example : Decode.op env "match.all.sync.b64"
    [.pair [.register "%r0", .register "%p1"], .register "%rd1", .register "%r1"] =
    .ok (.warp { all64p with mask := some (.reg 1) }) := rfl
example : all64p.rule = some .threadMatch := rfl
-- The `d|p` form belongs to `.all`: `.any` takes no predicate destination.
example : (Decode.op env "match.any.sync.b32"
    [.pair [.register "%r0", .register "%p1"], .register "%r1", .literal "3"]).isOk = false :=
  rfl
-- "The sink symbol ‘_’ may be used in place of any one of the destination operands."
example : Decode.op env "match.all.sync.b32"
    [.pair [.sink, .register "%p1"], .register "%r1", .literal "3"] =
    .ok (.warp {
      kind := .match_ true, ty := some (.int .b 32), dsts := [none, some 5], srcs := [.reg 1],
      mask := some (.imm 3) }) := rfl
example : Decode.op env "match.all.sync.b32"
    [.pair [.register "%r0", .sink], .register "%r1", .literal "3"] =
    .ok (.warp {
      kind := .match_ true, ty := some (.int .b 32), dsts := [some 0, none], srcs := [.reg 1],
      mask := some (.imm 3) }) := rfl
example : WarpInstr.rule {
    kind := .match_ true, ty := some (.int .b 32), dsts := [none, some 5], srcs := [.reg 1],
    mask := some (.imm 3) } = some .threadMatch := rfl
example : WarpInstr.rule {
    kind := .match_ true, ty := some (.int .b 32), dsts := [some 0, none], srcs := [.reg 1],
    mask := some (.imm 3) } = some .threadMatch := rfl
-- Both destinations a sink: no rule.
example : WarpInstr.rule {
    kind := .match_ true, ty := some (.int .b 32), dsts := [none, none], srcs := [.reg 1],
    mask := some (.imm 3) } = none := rfl
-- A match requires a warp-uniform guard.
example : Op.uniform (.warp any32) = true := rfl
example : Op.uniform (.warp all64p) = true := rfl

/-! ## The mask and the predicate at their boundaries -/

private def two (a b : Option (BitVec 64)) : Nat → Option (BitVec 64) := fun lane =>
  if lane = 0 then a else if lane = 1 then b else none

-- `.any`: the lanes that have the same value of the operand.
example : matchMask false 5#64 (two (some 5#64) (some 5#64)) = 3#32 := by decide
example : matchMask false 5#64 (two (some 5#64) (some 6#64)) = 1#32 := by decide
example : matchMask false 6#64 (two (some 5#64) (some 6#64)) = 2#32 := by decide
-- `.all`: the mask of the participating lanes when all operands are equal, and 0 otherwise.
example : matchMask true 5#64 (two (some 5#64) (some 5#64)) = 3#32 := by decide
example : matchMask true 5#64 (two (some 5#64) (some 6#64)) = 0#32 := by decide
example : matchEqual 5#64 (two (some 5#64) (some 5#64)) = true := by decide
example : matchEqual 5#64 (two (some 5#64) (some 6#64)) = false := by decide
-- A lane that exited (`none`) is not in the mask and its operand is not compared.
example : matchMask true 5#64 (two (some 5#64) none) = 1#32 := by decide
example : matchMask true 5#64 (two none (some 5#64)) = 2#32 := by decide
example : matchMask false 5#64 (two (some 5#64) none) = 1#32 := by decide
example : matchEqual 5#64 (two (some 5#64) none) = true := by decide
-- The 64-bit operands are compared in full.
example : matchEqual 5#64 (two (some 5#64) (some 0x100000005#64)) = false := by decide

/-! ## The event -/

-- One warp of two threads; register 1 holds a 32-bit operand and register 3 a 64-bit operand.
private def launch : Launch := { grid := 1, block := 2, params := fun _ => none }
private def t : TState :=
  { regs := fun r => if r = 1 then some (.bits 32 5#64) else if r = 3 then some (.bits 64 (7#64))
    else none }

example : matchTmpl launch 0 t false 32 (some 0) none (.reg 1) (.imm 3) =
    .match_ false false 3 5#64 (fun r _ => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
example : eventTmpl [] launch 0 t (.warp any32) =
    .match_ false false 3 5#64 (fun r _ => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
-- `.b64` reads a 64-bit operand and records the width.
example : eventTmpl [] launch 0 t (.warp any64) =
    .match_ false true 3 7#64 (fun r _ => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
-- `.all` writes the mask to `d` and the predicate to `p`; a sink writes nothing.
example : eventTmpl [] launch 0 t (.warp all64p) =
    .match_ true true 3 7#64 (fun r ok =>
      next (setReg (setReg t 0 (.bits 32 (r.setWidth 64))) 5 (.pred ok))) := rfl
example : matchTmpl launch 0 t true 32 none (some 5) (.reg 1) (.imm 3) =
    .match_ true false 3 5#64 (fun _ ok => next (setReg t 5 (.pred ok))) := rfl
example : matchTmpl launch 0 t true 32 (some 0) none (.reg 1) (.imm 3) =
    .match_ true false 3 5#64 (fun r _ => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
-- "The behavior of match.sync is undefined if the executing thread is not in the membermask ."
example : matchTmpl launch 0 t false 32 (some 0) none (.reg 1) (.imm 2) = .ub .badValue := rfl
-- A member mask that names a lane with no thread has no rule.
example : matchTmpl launch 0 t false 32 (some 0) none (.reg 1) (.imm 7) = .ub .noRule := rfl
-- An unset operand is a fault.
example : matchTmpl launch 0 {} false 32 (some 0) none (.reg 1) (.imm 3) = .ub .uninitialized :=
  rfl
-- The mask and the predicate received are written to the destinations.
example : Fires 4 (matchTmpl launch 0 t true 32 (some 0) (some 5) (.reg 1) (.imm 3))
    ⟨4, .match_ true false 3 5#64 3#32 true⟩
    (some (next (setReg (setReg t 0 (.bits 32 3#64)) 5 (.pred true)))) := ⟨_, _, rfl, rfl⟩

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
private def partOf (a0 a1 : BitVec 64) : Nat → Option (BitVec 64) := two (some a0) (some a1)

private theorem both_instance (q : Bool × Bool) (a0 a1 : BitVec 64) (r0 r1 : BitVec 32)
    (p0 p1 : Bool) (g : Nat) (hg : g < 2) :
    MaskInstance launch matchClass
      (both (.match_ q.1 q.2 3 a0 r0 p0) (.match_ q.1 q.2 3 a1 r1 p1)) g 3 0 q
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

/-- The mask and the predicate depend only on the lanes below 32. -/
private theorem result_congr (all : Bool) (a : BitVec 64) (p q : Nat → Option (BitVec 64))
    (h : ∀ lane ∈ List.range 32, p lane = q lane) :
    matchMask all a p = matchMask all a q ∧ matchEqual a p = matchEqual a q := by
  have he : matchEqual a p = matchEqual a q := by
    unfold matchEqual
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true]
    exact forall_congr' fun lane => forall_congr' fun hl => by rw [h lane hl]
  refine ⟨?_, he⟩
  unfold matchMask
  rw [he]
  unfold laneBits
  cases all
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hf : (List.range 32).filter (fun lane => p lane == some a) =
        (List.range 32).filter (fun lane => q lane == some a) :=
      List.filter_congr fun lane hl => by rw [h lane hl]
    rw [hf]
  · simp only [↓reduceIte]
    have hf : (List.range 32).filter (fun lane => (p lane).isSome) =
        (List.range 32).filter (fun lane => (q lane).isSome) :=
      List.filter_congr fun lane hl => by rw [h lane hl]
    rw [hf]

/-- The instance of a complete pair of matches holds the operands of the two lanes. -/
private theorem part_eq (q : Bool × Bool) (a0 a1 : BitVec 64) (r0 r1 : BitVec 32) (p0 p1 : Bool)
    (g : Nat) (hg : g < 2) (part : Nat → Option (BitVec 64))
    (hi : MaskInstance launch matchClass
      (both (.match_ q.1 q.2 3 a0 r0 p0) (.match_ q.1 q.2 3 a1 r1 p1)) g 3 0 q part) :
    ∀ all a, matchMask all a part = matchMask all a (partOf a0 a1) ∧
      matchEqual a part = matchEqual a (partOf a0 a1) := by
  intro all a
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
        · simp [matchClass] at hc
          rw [hpv, ← hc]; rfl
        · cases h
      · rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
        · cases h
        · simp [matchClass] at hc
          rw [hpv, ← hc]; rfl
    · rw [lane_eq g hg, Nat.zero_add] at hk
      rcases get_both hk with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> cases h
  · have hb : (3 : Nat).testBit lane = false := by
      rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
      · exact absurd (bit3 lane hl h) h2
      · exact h
    rw [(hi lane hl).2 hb]
    simp [partOf, two, show lane ≠ 0 by omega, show lane ≠ 1 by omega]

/-- A pair of matches with one mode, type and member mask holds exactly when each lane received
the mask and the predicate of the two operands. -/
private theorem both_ok_iff (all wide : Bool) (a0 a1 : BitVec 64) (r0 r1 : BitVec 32)
    (p0 p1 : Bool) :
    MatchOk launch (both (.match_ all wide 3 a0 r0 p0) (.match_ all wide 3 a1 r1 p1)) ↔
      (r0 = matchMask all a0 (partOf a0 a1) ∧ p0 = matchEqual a0 (partOf a0 a1)) ∧
      (r1 = matchMask all a1 (partOf a0 a1) ∧ p1 = matchEqual a1 (partOf a0 a1)) := by
  constructor
  · intro h
    exact ⟨h 0 0 0 all wide 3 a0 r0 p0 0 rfl ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩ _
        (both_instance (all, wide) a0 a1 r0 r1 p0 p1 0 (by omega)),
      h 1 0 0 all wide 3 a1 r1 p1 0 rfl ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩ _
        (both_instance (all, wide) a0 a1 r0 r1 p0 p1 1 (by omega))⟩
  · rintro ⟨h0, h1⟩ g i pc all' wide' mask a r p n hget hk
    have hn : n = 0 := by
      rcases get_both hget with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simpa using hk.2.symm
    subst hn
    rcases get_both hget with ⟨rfl, -, h⟩ | ⟨rfl, -, h⟩ <;>
      simp only [Kind.match_.injEq] at h <;> obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    · intro part hi
      have e := part_eq (all', wide') a a1 r r1 p p1 0 (by omega) part hi all' a
      exact ⟨h0.1.trans e.1.symm, h0.2.trans e.2.symm⟩
    · intro part hi
      have e := part_eq (all', wide') a0 a r0 r p0 p 1 (by omega) part hi all' a
      exact ⟨h1.1.trans e.1.symm, h1.2.trans e.2.symm⟩

-- Both operands are 5: both lanes receive the mask 3 and the predicate true.
theorem all_ok : MatchOk launch
    (both (.match_ true false 3 5#64 3#32 true) (.match_ true false 3 5#64 3#32 true)) :=
  (both_ok_iff true false 5#64 5#64 3#32 3#32 true true).2
    ⟨⟨by decide, by decide⟩, by decide, by decide⟩
-- Any other mask is not a possible value.
theorem all_wrong_mask : ¬ MatchOk launch
    (both (.match_ true false 3 5#64 1#32 true) (.match_ true false 3 5#64 3#32 true)) :=
  fun h => absurd ((both_ok_iff true false 5#64 5#64 1#32 3#32 true true).1 h).1.1 (by decide)
-- With different operands `.all` gives mask 0 and predicate false.
theorem all_differ_ok : MatchOk launch
    (both (.match_ true false 3 5#64 0#32 false) (.match_ true false 3 6#64 0#32 false)) :=
  (both_ok_iff true false 5#64 6#64 0#32 0#32 false false).2
    ⟨⟨by decide, by decide⟩, by decide, by decide⟩
-- `.any` with different operands gives each lane its own class.
theorem any_ok : MatchOk launch
    (both (.match_ false false 3 5#64 1#32 false) (.match_ false false 3 6#64 2#32 false)) :=
  (both_ok_iff false false 5#64 6#64 1#32 2#32 false false).2
    ⟨⟨by decide, by decide⟩, by decide, by decide⟩

/-- The instance of lane 0 exists: lane 0 takes part with its operand and lane 1 is an exited
lane of the mask, which takes no part. -/
theorem exited_instance : MaskInstance launch matchClass
    (both (.match_ true false 3 5#64 1#32 true) .exit) 0 3 0 (true, false)
    (two (some 5#64) none) := by
  intro lane hl
  rw [lane_eq 0 (by omega), Nat.zero_add]
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have := bit3 lane hl hb
    obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
    · exact .inl ⟨0, 0, _, 5#64, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · exact .inr ⟨⟨0, 0, rfl, by simp⟩, rfl⟩
  · have : lane ≠ 0 ∧ lane ≠ 1 := by
      constructor <;> rintro rfl <;> exact absurd hb (by decide)
    simp [two, this.1, this.2]

/-- The match of lane 0 is ready: lane 0's own event and the exit of lane 1 fill its needs
(DEP-ORDER). -/
theorem exited_ready : Ready launch (both (.match_ true false 3 5#64 1#32 true) .exit) (0, 0) := by
  have hat : (both (.match_ true false 3 5#64 1#32 true) .exit).MaskAt matchClass (0, 0) 3 0
      (true, false) :=
    ⟨⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, _, _, rfl, rfl, rfl⟩
  intro n hn
  simp only [Needs, KindNeeds, maskNeeds, both, exec, Execution.get] at hn
  simp only [ite_true, List.getElem?_cons_zero, Option.bind_some, matchClass] at hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  have hl : l < 2 := by
    obtain ⟨hl, hb⟩ := List.mem_filter.mp hl
    exact bit3 l (List.mem_range.mp hl) hb
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨.thread (0, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inl hat⟩
  · exact ⟨.thread (1, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inr ⟨rfl, ⟨0, rfl⟩, by simp⟩⟩

/-- Lane 1 exited before the match: lane 0 matches alone. -/
theorem exited_ok : MatchOk launch
    (both (.match_ true false 3 5#64 1#32 true) .exit) := by
  intro g i pc all wide mask a r p n hget hk
  have hn : n = 0 := by
    rcases get_both hget with ⟨-, rfl, -⟩ | ⟨-, rfl, h⟩ <;> simpa using hk.2.symm
  subst hn
  rcases get_both hget with ⟨rfl, -, h⟩ | ⟨-, -, h⟩
  · simp only [Kind.match_.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    intro part hi
    have e := result_congr true 5#64 part (two (some 5#64) none) ?_
    · rw [e.1, e.2]
      exact ⟨by decide, by decide⟩
    intro lane hl
    have hl := List.mem_range.mp hl
    have hi' := hi lane hl
    rw [lane_eq 0 (by omega), Nat.zero_add] at hi'
    by_cases h2 : lane < 2
    · obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
      · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, hpv⟩ | ⟨⟨k, pc, hk, -⟩, -⟩
        · rcases get_both hj with ⟨-, -, rfl⟩ | ⟨h, -⟩
          · simp [matchClass] at hc
            rw [hpv, ← hc]; rfl
          · cases h
        · rcases get_both hk with ⟨-, -, h⟩ | ⟨h, -⟩
          · cases h
          · cases h
      · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, -⟩ | ⟨-, hpn⟩
        · rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
          · cases h
          · simp [matchClass] at hc
        · rw [hpn]; rfl
    · have hb : (3 : Nat).testBit lane = false := by
        rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
        · exact absurd (bit3 lane hl h) h2
        · exact h
      rw [hi'.2 hb]
      simp [two, show lane ≠ 0 by omega, show lane ≠ 1 by omega]
  · cases h

/-- Lane 1 performs `k1`, which is not a match with the qualifiers `q` and member mask 3 and not
an exit, while lane 0 matches with the qualifiers `q`: the match of lane 0 is not ready, so no
consistent execution contains it (`DependencyOk.ready`). -/
private theorem mismatch (q : Bool × Bool) (a0 : BitVec 64) (r0 : BitVec 32) (p0 : Bool)
    (k1 : Kind) (hc : ∀ v, matchClass k1 ≠ some ⟨3, q, v⟩) (he : k1 ≠ .exit) :
    ¬ Ready launch (both (.match_ q.1 q.2 3 a0 r0 p0) k1) (0, 0) := by
  intro hr
  have hg0 : (both (.match_ q.1 q.2 3 a0 r0 p0) k1).get (0, 0) =
      some ⟨0, .match_ q.1 q.2 3 a0 r0 p0⟩ := rfl
  have hn := maskNeeds_mem launch matchClass _ (0, 0) hg0 (p := ⟨3, q, a0⟩) rfl
    (l := 1) (by decide) (show (3 : Nat).testBit 1 = true by decide)
  have hN : Needs launch (both (.match_ q.1 q.2 3 a0 r0 p0) k1) (0, 0) =
      maskNeeds launch matchClass (both (.match_ q.1 q.2 3 a0 r0 p0) k1) (0, 0) := by
    simp [Needs, hg0, KindNeeds]
  obtain ⟨x, -, j, rfl, hw⟩ := hr _ (hN ▸ hn)
  obtain ⟨-, m', n, q', ⟨⟨⟨ev, p, hg, hp, hm⟩, -⟩, ev', p', hg', hp', hq⟩, hw⟩ := hw
  rw [hg0] at hg hg'
  cases hg
  cases hg'
  simp only [matchClass, Option.some.injEq] at hp hp'
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

-- Lane 1 matches in `.all` mode while lane 0 matches in `.any` mode.
theorem mode_rejected : ¬ Ready launch
    (both (.match_ false false 3 5#64 3#32 false) (.match_ true false 3 5#64 3#32 true)) (0, 0) :=
  mismatch (false, false) 5#64 3#32 false _ (by simp [matchClass]) (by simp)

-- Lane 1 matches 64-bit operands while lane 0 matches 32-bit operands.
theorem type_rejected : ¬ Ready launch
    (both (.match_ true false 3 5#64 3#32 true) (.match_ true true 3 5#64 3#32 true)) (0, 0) :=
  mismatch (true, false) 5#64 3#32 true _ (by simp [matchClass]) (by simp)

-- Lane 1 matches with member mask 2 while lane 0 waits for it with member mask 3.
theorem mask_rejected : ¬ Ready launch
    (both (.match_ true false 3 5#64 3#32 true) (.match_ true false 2 5#64 2#32 true)) (0, 0) :=
  mismatch (true, false) 5#64 3#32 true _ (by simp [matchClass]) (by simp)

end
end PTX.Tests.Match
