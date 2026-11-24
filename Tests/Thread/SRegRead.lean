-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

/-!
# Reads of special registers that change while the thread runs (THREAD-SREG, THREAD-RUN)

A `mov` or an integer instruction that reads `%clock`, `%smid` or another changing register
performs one event with an open value below the register's bound; the instruction then runs with
the value read.
-/

namespace PTX.Tests.SRegRead
noncomputable section

private def launch : Launch := {
  grid := 2, block := 32, params := fun _ => none, sregInit := fun _ _ => 4 }

private def clockMov : Op := .move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.clock, none⟩]⟩
private def smidAdd : Op :=
  .int ⟨.add, .int .u 32, false, [some 0], [.sreg ⟨.smid, none⟩, .imm 1]⟩
private def laneMov : Op := .move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.laneid, none⟩]⟩

-- A read of a changing register is an event; a read of a fixed register is local.
example : clockMov.isLocal = false := rfl
example : smidAdd.isLocal = false := rfl
example : laneMov.isLocal = true := rfl
example : clockMov.varyingSregs = [⟨.clock, none⟩] := rfl

private def clockKernel : Kernel := { name := "clock", params := [], code := [⟨none, clockMov⟩] }
private def smidKernel : Kernel := { name := "smid", params := [], code := [⟨none, smidAdd⟩] }

example : out clockKernel [] launch 0 {} = .ev (sregTmpl [] launch 0 {} clockMov) := rfl

-- Any 32-bit value may be read from `%clock`, and the move writes it.
example : Fires 0 (sregTmpl [] launch 0 {} clockMov) ⟨0, .sreg [⟨.clock, none⟩] [123456]⟩
    (some (next (setReg {} 0 (.bits 32 123456)))) :=
  ⟨[123456], .cons (by decide) .nil, rfl, rfl⟩
example : Fires 0 (sregTmpl [] launch 0 {} clockMov) ⟨0, .sreg [⟨.clock, none⟩] [0]⟩
    (some (next (setReg {} 0 (.bits 32 0)))) :=
  ⟨[0], .cons (by decide) .nil, rfl, rfl⟩
-- A value outside the register's width is not a possible read.
example (o : Option TState) :
    ¬ Fires 0 (sregTmpl [] launch 0 {} clockMov) ⟨0, .sreg [⟨.clock, none⟩] [2 ^ 32]⟩ o := by
  rintro ⟨vals, hb, he, -⟩
  simp only [Event.mk.injEq, Kind.sreg.injEq, true_and] at he
  obtain ⟨-, rfl⟩ := he
  cases hb with
  | cons h _ => exact absurd h (by decide)

-- `%smid` is below the thread's `%nsmid` (4 here), and the instruction adds 1 to the value read.
example : Fires 0 (sregTmpl [] launch 0 {} smidAdd) ⟨0, .sreg [⟨.smid, none⟩] [3]⟩
    (some (next (setReg {} 0 (.bits 32 4)))) :=
  ⟨[3], .cons (by decide) .nil, rfl, rfl⟩
example (o : Option TState) :
    ¬ Fires 0 (sregTmpl [] launch 0 {} smidAdd) ⟨0, .sreg [⟨.smid, none⟩] [4]⟩ o := by
  rintro ⟨vals, hb, he, -⟩
  simp only [Event.mk.injEq, Kind.sreg.injEq, true_and] at he
  obtain ⟨-, rfl⟩ := he
  cases hb with
  | cons h _ => exact absurd h (by decide)

-- Two reads of `%clock` by one thread may return any two values, in either order.
private def twoClocks : Kernel :=
  { name := "twoClocks", params := [], code := [⟨none, clockMov⟩, ⟨none, clockMov⟩, ⟨none, .exit⟩] }
example : Produces twoClocks [] launch 0
    [⟨0, .sreg [⟨.clock, none⟩] [9]⟩, ⟨1, .sreg [⟨.clock, none⟩] [5]⟩, ⟨2, .exit⟩] :=
  ⟨none, .step (.refl) ⟨_, rfl, [9], .cons (by decide) .nil, rfl, rfl⟩
    (.step (.refl) ⟨_, rfl, [5], .cons (by decide) .nil, rfl, rfl⟩
      (.last (.refl) ⟨.exit, rfl, rfl, rfl⟩))⟩

-- `%pm0` has no rule: the instruction stays local and its rule fails with `noRule`.
private def pmMov : Op := .move ⟨.scalar, .int .u 32, [some 0], [.sreg ⟨.pm 0, none⟩]⟩
example : pmMov.isLocal = true := rfl
example : execLocal launch 0 {} pmMov = .error .noRule := rfl

end
end PTX.Tests.SRegRead
