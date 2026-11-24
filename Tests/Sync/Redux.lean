-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Sync.WarpUniform

/-! `redux.sync` (§9.7.15.13): decoding, the rule of each form, the values of the operations at
their boundaries, the reduction event, and the instance constraint `ReduxOk` (DEP-WARP-REDUX,
DEP-WARP-INSTANCE) with an exited lane and a wrong result, and the waiting dependency
(DEP-ORDER) with a mask disagreement and an operation disagreement. -/
namespace PTX.Tests.Redux
open PTX.Syntax
noncomputable section

/-! ## Decoding and rules -/

-- `%r0`, `%r1` are registers 0, 1 (32-bit).
private def env : Decode.Env := { classes := [⟨"%r".toList, 2, 32⟩], labels := [], params := [] }

private def addS32 : WarpInstr :=
  { kind := .redux .add false false, ty := some (.int .s 32), dsts := [some 0], srcs := [.reg 1],
    mask := some (.imm 3) }

example : Decode.op env "redux.sync.add.s32" [.register "%r0", .register "%r1", .literal "3"] =
    .ok (.warp addS32) := rfl
example : addS32.rule = some .threadRedux := rfl
example : WarpInstr.rule { addS32 with kind := .redux .min false false, ty := some (.int .u 32) } =
    some .threadRedux := rfl
example : WarpInstr.rule { addS32 with kind := .redux .xor false false, ty := some (.int .b 32) } =
    some .threadRedux := rfl
-- The grammar pairs `.and`, `.or`, `.xor` with `.b32`, and `.add`, `.min`, `.max` with `.u32` and
-- `.s32`.
example : (Decode.op env "redux.sync.add.b32"
    [.register "%r0", .register "%r1", .literal "3"]).isOk = false := rfl
example : (Decode.op env "redux.sync.and.u32"
    [.register "%r0", .register "%r1", .literal "3"]).isOk = false := rfl
-- The `.f32` forms decode and have no rule; their execution is undefined behaviour with no rule.
private def minF32 : WarpInstr :=
  { kind := .redux .min false false, ty := some (.float .f32), dsts := [some 0], srcs := [.reg 1],
    mask := some (.imm 3) }
example : Decode.op env "redux.sync.min.f32" [.register "%r0", .register "%r1", .literal "3"] =
    .ok (.warp minF32) := rfl
example : minF32.rule = none := rfl
example (L : Launch) (g : Nat) (t : TState) : eventTmpl [] L g t (.warp minF32) = .ub .noRule :=
  rfl

-- Guard divergence on a reduction is unsafe.
example : Op.uniform (.warp addS32) = true := rfl

/-! ## The operations at their boundaries -/

-- "For the .add operation result is truncated to 32 bits."
example : reduxResult .add true [0xFFFFFFFF#32, 1#32] = 0#32 := by decide
-- `.min`/`.max` compare signed values for `.s32` and unsigned values for `.u32`.
example : reduxResult .min true [0x7FFFFFFF#32, 0x80000000#32] = 0x80000000#32 := by decide
example : reduxResult .min false [0x7FFFFFFF#32, 0x80000000#32] = 0x7FFFFFFF#32 := by decide
example : reduxResult .max true [0x7FFFFFFF#32, 0x80000000#32] = 0x7FFFFFFF#32 := by decide
example : reduxResult .max false [0x7FFFFFFF#32, 0x80000000#32] = 0x80000000#32 := by decide
example : reduxResult .and false [0xF0F0F0F0#32, 0xFF00FF00#32] = 0xF000F000#32 := by decide
example : reduxResult .or false [0xF0F0F0F0#32, 0x0F000000#32] = 0xFFF0F0F0#32 := by decide
example : reduxResult .xor false [0xFFFF0000#32, 0xFF00FF00#32, 1#32] = 0x00FFFF01#32 := by decide
-- A single participant receives its own source.
example : reduxResult .min true [0x80000000#32] = 0x80000000#32 := by decide

/-! ## The event -/

-- One warp of two threads.
private def launch : Launch := { grid := 1, block := 2, params := fun _ => none }
private def t : TState := { regs := fun r => if r = 1 then some (.bits 32 5#64) else none }

example : reduxTmpl launch 0 t .add true 0 (.reg 1) (.imm 3) =
    .redux .add true 3 5#32 (fun r => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
example : eventTmpl [] launch 0 t (.warp addS32) =
    .redux .add true 3 5#32 (fun r => next (setReg t 0 (.bits 32 (r.setWidth 64)))) := rfl
-- "The behavior of redux.sync is undefined if the executing thread is not in the membermask ."
example : reduxTmpl launch 0 t .add true 0 (.reg 1) (.imm 2) = .ub .badValue := rfl
-- A member mask that names a lane with no thread has no rule.
example : reduxTmpl launch 0 t .add true 0 (.reg 1) (.imm 7) = .ub .noRule := rfl
-- An unset source register is a fault.
example : reduxTmpl launch 0 {} .add true 0 (.reg 1) (.imm 3) = .ub .uninitialized := rfl
-- The result received is written to the destination as a 32-bit integer.
example : Fires 4 (reduxTmpl launch 0 t .add true 0 (.reg 1) (.imm 3))
    ⟨4, .redux .add true 3 5#32 12#32⟩ (some (next (setReg t 0 (.bits 32 12#64)))) :=
  ⟨_, rfl, rfl⟩

/-! ## Instances

Thread `h` of the warp performs the events `tr h`; the threads 0 and 1 are lanes 0 and 1. -/

private def exec (tr : Nat → List Event) : Execution := { tr := tr, rf := fun _ _ => none }

private theorem lane_eq (g : Nat) (hg : g < 2) : g - laneOf launch g = 0 := by
  simp [laneOf, launch, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt (by omega : g < 32)]

private theorem bit3 (lane : Nat) (hl : lane < 32) (hb : (3 : Nat).testBit lane = true) :
    lane < 2 := by
  by_contra hn
  have : (3 : Nat) < 2 ^ lane :=
    lt_of_lt_of_le (by decide : (3 : Nat) < 2 ^ 2) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow this] at hb
  cases hb

/-- Both lanes reduce 5 and 7 with `.add.u32` and the full member mask of the warp. -/
private def both (r : BitVec 32) : Execution :=
  exec fun g => if g = 0 then [⟨0, .redux .add false 3 5#32 r⟩]
    else if g = 1 then [⟨0, .redux .add false 3 7#32 r⟩] else []

private def bothPart : Nat → Option (BitVec 32) := fun lane =>
  if lane = 0 then some 5#32 else if lane = 1 then some 7#32 else none

private theorem both_instance (r : BitVec 32) (g : Nat) (hg : g < 2) :
    MaskInstance launch reduxClass (both r) g 3 0 (.add, false) bothPart := by
  intro lane hl
  rw [lane_eq g hg, Nat.zero_add]
  refine ⟨fun hb => .inl ?_, fun hb => ?_⟩
  · have := bit3 lane hl hb
    obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
    · exact ⟨0, 0, _, 5#32, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨0, 0, _, 7#32, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
  · have : lane ≠ 0 ∧ lane ≠ 1 := by
      constructor <;> rintro rfl <;> exact absurd hb (by decide)
    simp [bothPart, this.1, this.2]

private theorem get_both {r : BitVec 32} {h j pc : Nat} {k : Kind}
    (hj : (both r).get (h, j) = some ⟨pc, k⟩) :
    (h = 0 ∧ j = 0 ∧ k = .redux .add false 3 5#32 r) ∨
      (h = 1 ∧ j = 0 ∧ k = .redux .add false 3 7#32 r) := by
  unfold both exec Execution.get at hj
  by_cases h0 : h = 0
  · subst h0; obtain _ | j := j <;> simp_all
  · by_cases h1 : h = 1
    · subst h1; obtain _ | j := j <;> simp_all
    · simp [h0, h1] at hj

/-- The inputs of an instance in which lane 0 reduces 5 and lane 1 reduces 7 are those of
`bothPart`. -/
private theorem part_eq (X : Execution) (part : Nat → Option (BitVec 32)) (q : ReduxOp × Bool)
    (g : Nat) (hg : g < 2)
    (h0 : ∀ j pc k v, X.get (0, j) = some ⟨pc, k⟩ → reduxClass k = some ⟨3, q, v⟩ → v = 5#32)
    (h1 : ∀ j pc k v, X.get (1, j) = some ⟨pc, k⟩ → reduxClass k = some ⟨3, q, v⟩ → v = 7#32)
    (hx : ∀ h, h < 2 → ¬ MaskExited reduxClass X h 3 0)
    (hi : MaskInstance launch reduxClass X g 3 0 q part) :
    (List.range 32).filterMap part = [5#32, 7#32] := by
  have hp : ∀ lane ∈ List.range 32, part lane = bothPart lane := by
    intro lane hl
    have hl := List.mem_range.mp hl
    by_cases h2 : lane < 2
    · have hb : (3 : Nat).testBit lane = true := by
        obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
        all_goals decide
      rcases (hi lane hl).1 hb with ⟨j, pc, k, v, hj, hc, -, hpv⟩ | ⟨hex, -⟩
      · rw [lane_eq g hg, Nat.zero_add] at hj
        obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
        · rw [hpv, h0 j pc k v hj hc]; rfl
        · rw [hpv, h1 j pc k v hj hc]; rfl
      · rw [lane_eq g hg, Nat.zero_add] at hex
        exact (hx lane h2 hex).elim
    · have hb : (3 : Nat).testBit lane = false := by
        rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
        · exact absurd (bit3 lane hl h) h2
        · exact h
      rw [(hi lane hl).2 hb]
      simp [bothPart, show lane ≠ 0 by omega, show lane ≠ 1 by omega]
  rw [List.filterMap_congr hp]
  decide

/-- Lane 0 of `both r` reduces 5 with `.add.u32` and member mask 3. -/
private theorem src0 (r : BitVec 32) : ∀ j pc k v, (both r).get (0, j) = some ⟨pc, k⟩ →
    reduxClass k = some ⟨3, (.add, false), v⟩ → v = 5#32 := by
  intro j pc k v hj hc
  rcases get_both hj with ⟨-, -, rfl⟩ | ⟨h, -⟩
  · simp [reduxClass] at hc; exact hc.symm
  · cases h

/-- Lane 1 of `both r` reduces 7. -/
private theorem src1 (r : BitVec 32) : ∀ j pc k v, (both r).get (1, j) = some ⟨pc, k⟩ →
    reduxClass k = some ⟨3, (.add, false), v⟩ → v = 7#32 := by
  intro j pc k v hj hc
  rcases get_both hj with ⟨h, -⟩ | ⟨-, -, rfl⟩
  · cases h
  · simp [reduxClass] at hc; exact hc.symm

/-- No lane of `both r` exits. -/
private theorem noExit (r : BitVec 32) : ∀ h, h < 2 → ¬ MaskExited reduxClass (both r) h 3 0 := by
  rintro h - ⟨k, pc, hk, -⟩
  rcases get_both hk with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> cases h

-- Both lanes receive 12.
theorem both_ok : ReduxOk launch (both 12#32) := by
  intro g i pc op signed mask a r n hget hk
  have hg : g < 2 := by
    by_contra hn
    simp [both, exec, Execution.get, show g ≠ 0 by omega, show g ≠ 1 by omega] at hget
  have hn : n = 0 := by
    obtain _ | i := i
    · simpa using hk.2.symm
    · obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
      all_goals simp [both, exec, Execution.get] at hget
  subst hn
  have hev : op = .add ∧ signed = false ∧ mask = 3 ∧ r = 12#32 := by
    obtain _ | i := i
    · obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
      all_goals
        simp only [both, exec, Execution.get, ite_true, List.getElem?_cons_zero,
          Option.some.injEq, Event.mk.injEq, Kind.redux.injEq, one_ne_zero, ite_false] at hget
        obtain ⟨-, rfl, rfl, rfl, -, rfl⟩ := hget
        exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain rfl | rfl : g = 0 ∨ g = 1 := by omega
      all_goals simp [both, exec, Execution.get] at hget
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hev
  intro part hi
  rw [part_eq _ part _ g hg (src0 12#32) (src1 12#32) (noExit 12#32) hi]
  decide

-- Any other result is not a possible value.
theorem both_wrong : ¬ ReduxOk launch (both 5#32) := by
  intro h
  have hr := h 0 0 0 .add false 3 5#32 5#32 0 rfl ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩ bothPart
    (both_instance _ 0 (by omega))
  exact absurd hr (by decide)

/-- Lane 1 exited before reaching the reduction: lane 0 reduces its own source. -/
private def exited : Execution :=
  exec fun g => if g = 0 then [⟨0, .redux .max true 3 0xFFFFFFF0#32 0xFFFFFFF0#32⟩]
    else if g = 1 then [⟨0, .exit⟩] else []

/-- The instance of lane 0 exists: lane 0 takes part with its source and lane 1 is an exited lane
of the mask, which takes no part. -/
theorem exited_instance : MaskInstance launch reduxClass exited 0 3 0 (.max, true)
    (fun lane => if lane = 0 then some 0xFFFFFFF0#32 else none) := by
  intro lane hl
  simp only [laneOf, launch, Nat.zero_mod, Nat.sub_zero, Nat.zero_add]
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · have := bit3 lane hl hb
    obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
    · exact .inl ⟨0, 0, _, _, rfl, rfl, ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩
    · exact .inr ⟨⟨0, 0, rfl, by simp⟩, rfl⟩
  · have : lane ≠ 0 := by rintro rfl; simp at hb
    simp [this]

/-- The reduction of lane 0 is ready: lane 0's own event and the exit of lane 1 fill its needs
(DEP-ORDER). -/
theorem exited_ready : Ready launch exited (0, 0) := by
  have hat : exited.MaskAt reduxClass (0, 0) 3 0 (.max, true) :=
    ⟨⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩, _, _, rfl, rfl, rfl⟩
  intro n hn
  simp only [Needs, KindNeeds, maskNeeds, exited, exec, Execution.get] at hn
  simp only [ite_true, List.getElem?_cons_zero, Option.bind_some, reduxClass] at hn
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hn
  have hl : l < 2 := by
    obtain ⟨hl, hb⟩ := List.mem_filter.mp hl
    exact bit3 l (List.mem_range.mp hl) hb
  obtain rfl | rfl : l = 0 ∨ l = 1 := by omega
  · exact ⟨.thread (0, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inl hat⟩
  · exact ⟨.thread (1, 0), ⟨_, rfl⟩, 0, rfl, ⟨⟨by decide, by decide, rfl⟩, rfl⟩, 3, 0, _, hat,
      .inr ⟨rfl, ⟨0, rfl⟩, by simp⟩⟩

theorem exited_ok : ReduxOk launch exited := by
  intro g i pc op signed mask a r n hget hk
  unfold exited exec Execution.get at hget
  by_cases h0 : g = 0
  · subst h0
    obtain _ | i := i
    · simp only [ite_true, List.getElem?_cons_zero, Option.some.injEq, Event.mk.injEq,
        Kind.redux.injEq] at hget
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hget
      have hn : n = 0 := by simpa using hk.2.symm
      subst hn
      intro part hi
      have hp : ∀ lane ∈ List.range 32,
          part lane = if lane = 0 then some 0xFFFFFFF0#32 else none := by
        intro lane hl
        have hl := List.mem_range.mp hl
        have hi' := hi lane hl
        simp only [laneOf, launch, Nat.zero_mod, Nat.sub_zero, Nat.zero_add] at hi'
        by_cases h2 : lane < 2
        · obtain rfl | rfl : lane = 0 ∨ lane = 1 := by omega
          · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, hpv⟩ | ⟨⟨k, pc, hk, -⟩, -⟩
            · obtain _ | j := j
              · simp [exited, exec, Execution.get] at hj
                obtain ⟨-, rfl⟩ := hj
                simp only [reduxClass, Option.some.injEq, WarpPart.mk.injEq] at hc
                simp [hpv, hc.2.2]
              · simp [exited, exec, Execution.get] at hj
            · obtain _ | k := k <;> simp [exited, exec, Execution.get] at hk
          · rcases hi'.1 (by decide) with ⟨j, pc, k, v, hj, hc, -, -⟩ | ⟨-, hpn⟩
            · obtain _ | j := j
              · simp [exited, exec, Execution.get] at hj
                obtain ⟨-, rfl⟩ := hj
                simp [reduxClass] at hc
              · simp [exited, exec, Execution.get] at hj
            · simp [hpn]
        · have hb : (3 : Nat).testBit lane = false := by
            rcases Bool.eq_false_or_eq_true ((3 : Nat).testBit lane) with h | h
            · exact absurd (bit3 lane hl h) h2
            · exact h
          rw [hi'.2 hb]
          simp [show lane ≠ 0 by omega]
      rw [List.filterMap_congr hp]
      decide
    · simp at hget
  · by_cases h1 : g = 1
    · subst h1; obtain _ | i := i <;> simp at hget
    · simp [h0, h1] at hget

/-- The event `(0, 0)`, a reduction with member mask 3, is not ready when lane 1 has no event of
the class with member mask 3 and the same operation and type, and does not exit. -/
private theorem not_ready (X : Execution) (op : ReduxOp) (signed : Bool) (a r : BitVec 32)
    (he : X.get (0, 0) = some ⟨0, .redux op signed 3 a r⟩)
    (h1 : ∀ j pc k p, X.get (1, j) = some ⟨pc, k⟩ → reduxClass k = some p → p.mask = 3 →
      p.qual ≠ (op, signed))
    (hx : ∀ j pc, X.get (1, j) ≠ some ⟨pc, .exit⟩) : ¬ Ready launch X (0, 0) := by
  intro hr
  have hn := maskNeeds_mem launch reduxClass X (0, 0) he (p := ⟨3, (op, signed), a⟩) rfl
    (l := 1) (by decide) (show (3 : Nat).testBit 1 = true by decide)
  have hN : Needs launch X (0, 0) = maskNeeds launch reduxClass X (0, 0) := by
    simp [Needs, he, KindNeeds]
  obtain ⟨x, -, j, rfl, hw⟩ := hr _ (hN ▸ hn)
  obtain ⟨-, m, n, q, ⟨⟨⟨ev, p, hg, hc, hm⟩, -⟩, ev', p', hg', hc', hq⟩, hw⟩ := hw
  rw [he] at hg hg'
  cases hg
  cases hg'
  simp only [reduxClass, Option.some.injEq] at hc hc'
  subst hc hc'
  subst hm hq
  have hl : warpLane launch 0 1 = 1 := rfl
  rw [hl] at hw
  rcases hw with ⟨⟨⟨⟨pc, k⟩, p, hg, hc, hm⟩, -⟩, ev2, p2, hg2, hc2, hq2⟩ | ⟨-, ⟨pc, hk⟩, -⟩
  · rw [hg] at hg2
    cases hg2
    rw [hc] at hc2
    cases hc2
    exact h1 j pc k p hg hc hm hq2
  · exact hx j pc hk

/-- Lane 1 reduces alone (member mask 2) while lane 0 waits for it with member mask 3. -/
private def maskMismatch : Execution :=
  exec fun g => if g = 0 then [⟨0, .redux .add false 3 5#32 12#32⟩]
    else if g = 1 then [⟨0, .redux .add false 2 7#32 7#32⟩] else []

-- The instance of lane 0 never completes: its reduction is not ready, so no consistent execution
-- contains it (`DependencyOk.ready`).
theorem maskMismatch_rejected : ¬ Ready launch maskMismatch (0, 0) := by
  refine not_ready _ .add false 5#32 12#32 rfl ?_ ?_
  · intro j pc k p hj hc hm
    obtain _ | j := j
    · simp [maskMismatch, exec, Execution.get] at hj
      obtain ⟨-, rfl⟩ := hj
      simp only [reduxClass, Option.some.injEq] at hc
      subst hc
      simp at hm
    · simp [maskMismatch, exec, Execution.get] at hj
  · intro j pc h
    obtain _ | j := j <;> simp [maskMismatch, exec, Execution.get] at h

/-- Lane 1 executes `.min` while lane 0 executes `.add` with the same member mask. -/
private def opMismatch : Execution :=
  exec fun g => if g = 0 then [⟨0, .redux .add false 3 5#32 12#32⟩]
    else if g = 1 then [⟨0, .redux .min false 3 7#32 5#32⟩] else []

-- The text requires the same qualifiers, so the lanes form no instance and the reduction of lane
-- 0 is not ready.
theorem opMismatch_rejected : ¬ Ready launch opMismatch (0, 0) := by
  refine not_ready _ .add false 5#32 12#32 rfl ?_ ?_
  · intro j pc k p hj hc _
    obtain _ | j := j
    · simp [opMismatch, exec, Execution.get] at hj
      obtain ⟨-, rfl⟩ := hj
      simp only [reduxClass, Option.some.injEq] at hc
      subst hc
      simp
    · simp [opMismatch, exec, Execution.get] at hj
  · intro j pc h
    obtain _ | j := j <;> simp [opMismatch, exec, Execution.get] at h

end
end PTX.Tests.Redux
