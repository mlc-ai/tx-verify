-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Source.Decode
public import Core.Tc.TcGroup
public import Core.Tc.TcMmaRead

/-! `tcgen05.cp.cta_group::1.128x256b` (THREAD-TC-CP-CELLS, DEP-TMEM-COPY-VALUE): decoding, the
issue rule, source locations, destination cells and copied words. -/
namespace PTX.Tests.TcCopy
open PTX.TcCopy
noncomputable section

private def env : Decode.Env :=
  { classes := [⟨"r".toList, 2, 32⟩, ⟨"rd".toList, 1, 64⟩], labels := [], params := [] }

example : Decode.op env "tcgen05.cp.cta_group::1.128x256b"
    [.address [.register "r0"], .register "rd0"] = .ok (.tcCp .one .s128x256b 0 (.reg 2)) := rfl
-- The other shapes with their multicast and cta_group::2 decode to `Op.tcCp`.
example : Decode.op env "tcgen05.cp.cta_group::1.128x128b"
    [.address [.register "r0"], .register "rd0"] = .ok (.tcCp .one .s128x128b 0 (.reg 2)) := rfl
example : Decode.op env "tcgen05.cp.cta_group::2.128x256b"
    [.address [.register "r0"], .register "rd0"] = .ok (.tcCp .two .s128x256b 0 (.reg 2)) := rfl
example : Decode.op env "tcgen05.cp.cta_group::1.64x128b.warpx2::02_13"
    [.address [.register "r0"], .register "rd0"] =
    .ok (.tcCp .one (.s64x128b true) 0 (.reg 2)) := rfl
-- `.4x256b` and decompression decode to `Op.tcCp` (PROG-ISA-TC-CP).
example : Decode.op env "tcgen05.cp.cta_group::1.4x256b"
    [.address [.register "r0"], .register "rd0"] = .ok (.tcCp .one .s4x256b 0 (.reg 2)) := rfl
example : Decode.op env "tcgen05.cp.cta_group::1.128x256b.b8x16.b6x16_p32"
    [.address [.register "r0"], .register "rd0"] =
    .ok (.tcCp .one .s128x256b 0 (.reg 2) (some .b6x16p32)) := rfl
-- An instruction without a representation is undefined behaviour with no rule.
example (L : Launch) (g : Nat) (t : TState) (r : Isa.Raw) :
    eventTmpl [] L g t (.unmodeled r) = .ub .noRule := rfl
example : (Op.tcCp .one .s128x256b 0 (.reg 2)).tcGroup = some 1 := rfl
example : (Op.tcCp .one .s128x256b 0 (.reg 2)).isLocal = false := rfl

/-! ## Issue -/

private def launch : Launch := { grid := 2, block := 64, params := fun _ => none, clusterSize := 1 }
-- A no-swizzle K-major descriptor: start 1024, leading 128, stride 256, version 1.
private def sdesc : Nat := 64 + 8 * 2 ^ 16 + 16 * 2 ^ 32 + 2 ^ 46
private def src : TcShared.Descriptor := ⟨1024, 128, 256, 0, false, false, .none⟩
private def t (address : Nat) : TState := { regs := fun
  | 0 => some (.bits 32 (BitVec.ofNat 64 address))
  | 2 => some (.bits 64 (BitVec.ofNat 64 sdesc))
  | _ => none }
private def cp : Op := .tcCp .one .s128x256b 0 (.reg 2)

example : TcShared.decode sdesc = some src := by decide
-- Any thread may issue; the copy lands in its own CTA.
example : tcTmpl launch 70 (t 16) cp = .tc (.cp ⟨16, src, .s128x256b, [1], none⟩) (next (t 16)) :=
  rfl
example : eventTmpl [] launch 3 (t 504) cp =
    .tc (.cp ⟨504, src, .s128x256b, [0], none⟩) (next (t 504)) := rfl
-- The 128-lane copy must start at lane 0 and fit eight columns.
example : tcTmpl launch 3 (t (32 * 2 ^ 16)) cp = .ub .badValue := rfl
example : tcTmpl launch 3 (t 505) cp = .ub .badValue := rfl
example : tcTmpl launch 128 (t 0) cp = .ub .badValue := rfl

/-! ## Geometry -/

-- Source byte q is row q/32, byte q%32 of the canonical K-major layout (8-row core matrices
-- of 16 bytes, leading offset between the two 16-byte halves, stride between 8-row groups).
example : byteLoc .s128x256b src 1 0 = some ⟨.shared, 1, 1024⟩ := by decide
example : byteLoc .s128x256b src 1 (32 + 5) = some ⟨.shared, 1, 1024 + 16 + 5⟩ := by decide
example : byteLoc .s128x256b src 1 (32 * 9 + 20) =
    some ⟨.shared, 1, 1024 + 256 + 16 + 128 + 4⟩ := by decide
example : byteLoc .s128x256b src 1 4096 = none := by decide
-- Destination: lane = row, column = address column + byte / 4.
example : cell .s128x256b 16 1 9 (32 * 9 + 20) = ⟨1, 9, 21⟩ := rfl
example : cell .s128x256b 16 1 127 (32 * 127 + 31) = ⟨1, 127, 23⟩ := rfl

/-! ## Words -/

private def b (k : Nat) : Option Byte := some (.bits 8 (BitVec.ofNat 64 k), 0)
private def row0 : List (Option Byte) := (List.range 32).map b

example : word .s128x256b row0 0 1 =
    some (.pair (.pair (byteValue (.bits 8 (BitVec.ofNat 64 4), 0))
    (byteValue (.bits 8 (BitVec.ofNat 64 5), 0))) (.pair (byteValue (.bits 8 (BitVec.ofNat 64 6),
      0))
    (byteValue (.bits 8 (BitVec.ofNat 64 7), 0)))) := rfl
-- The word holds its four source bytes, in order.
example : ((word .s128x256b row0 0 1).map fun v => (List.range 4).map v.byteAt) =
    some [(.bits 8 (BitVec.ofNat 64 4), 0), (.bits 8 (BitVec.ofNat 64 5), 0),
      (.bits 8 (BitVec.ofNat 64 6), 0), (.bits 8 (BitVec.ofNat 64 7), 0)] := by
  simp [word, TcCpShape.rowBytes, row0, b, TcCopy.byteValue, Value.byteAt, Value.bytes,
    List.range_succ]
example : ((word .s128x256b row0 0 1).map Value.bytes) = some 4 := rfl
-- One unknown byte leaves its word unknown, but not its neighbours.
example : word .s128x256b (row0.set 6 none) 0 1 = none := rfl
example : (word .s128x256b (row0.set 6 none) 0 0).isSome = true := rfl

/-! ## In an execution -/

-- Thread 0 copies (pc 0), commits (pc 1), and a thread of the same warp loads (pc 2).
private def X : Execution where
  tr := fun g => if g = 0 then
    [⟨0, .tc (.cp ⟨16, src, .s128x256b, [0], none⟩)⟩,
      ⟨1, .tc (.commit ⟨.one, ⟨.shared, 0, 8⟩, 1, 0, 1⟩)⟩,
      ⟨2, .tc (.ld 16 [] .s32x32b)⟩] else []
  rf := fun _ _ => none
  async := { mmaOperands := fun i => if i = (0, 0) then some ⟨row0, []⟩ else none }

-- The copy is a commit-tracked asynchronous operation, like an MMA.
example : X.TcAsync (0, 0) := .inr (.inl ⟨⟨16, src, .s128x256b, [0], none⟩, ⟨0, rfl⟩⟩)
example : AsyncCopy.TracksMma X (0, 0) (0, 1) :=
  ⟨rfl, by decide, .inr (.inl ⟨⟨16, src, .s128x256b, [0], none⟩, ⟨0, rfl⟩⟩), _, ⟨1, rfl⟩⟩
-- Its source bytes are asynchronous operand reads at the descriptor's locations.
example : X.MmaFootprint (0, 0) false (32 * 9 + 20) ⟨.shared, 0, 1024 + 256 + 16 + 128 + 4⟩ :=
  .inr ⟨⟨16, src, .s128x256b, [0], none⟩, 0, 0, ⟨0, rfl⟩, rfl, rfl, by decide, by decide⟩
example (l : Loc) : ¬ X.MmaFootprint (0, 0) true 0 l := by
  rintro (⟨_, _, _, _, ⟨pc, h⟩, -⟩ | ⟨_, _, _, -, h, -⟩)
  · simp [Execution.get, X] at h
  · cases h
-- It writes 128 lanes x 8 columns of Tensor Memory, and the word of lane 0, column 17 holds
-- source bytes 4..7.
example : TcMma.CpCell X (0, 0) ⟨0, 127, 23⟩ :=
  ⟨⟨16, src, .s128x256b, [0], none⟩, 0, 32 * 127 + 28, 127, ⟨0, rfl⟩, by decide, by decide,
    by decide,
    rfl⟩
example : TcMma.TmemWrite launch X (0, 0) ⟨0, 0, 17⟩ :=
  .inr (.inr (.inl ⟨⟨16, src, .s128x256b, [0], none⟩, 0, 4, 0, ⟨0, rfl⟩, by decide, by decide,
    by decide, rfl⟩))
example : TcMma.CpValue X (0, 0) ⟨0, 0, 17⟩ ((word .s128x256b row0 0 1).get rfl) :=
  ⟨⟨16, src, .s128x256b, [0], none⟩, 0, 0, _, 0, 1, 0, ⟨0, rfl⟩, rfl, rfl, by decide, by decide,
    by decide, rfl, (Option.some_get _).symm⟩
-- The copy cannot be ordered before the load without an observed commit: there is no wait.
example : ¬ TcMma.WriteBefore launch X (0, 0) (0, 2) := by
  rintro (((⟨w, ws, ⟨n, m, -, ⟨pc, p, hw⟩, -⟩, -, -⟩ |
      ⟨w, ⟨acq, sc, ⟨n, m, -, ⟨pc, p, hw⟩, -⟩, -⟩, -⟩) |
      ⟨-, -, d, sp, a, mk, -, -, -, -, ⟨pc, hx⟩, -⟩) | ⟨⟨a, vs, sh, pc, ht⟩, -⟩ | _)
  · obtain ⟨g, i⟩ := w
    by_cases hg : g = 0
    · subst g; match i with
      | 0 | 1 | 2 | _ + 3 => simp [Execution.get, X] at hw
    · simp [Execution.get, X, hg] at hw
  · obtain ⟨g, i⟩ := w
    by_cases hg : g = 0
    · subst g; match i with
      | 0 | 1 | 2 | _ + 3 => simp [Execution.get, X] at hw
    · simp [Execution.get, X, hg] at hw
  · simp [Execution.get, X] at hx
  · simp [Execution.get, X] at ht
  · obtain ⟨-, -, _, _, _, _, _, -, -, ⟨pc, hm⟩, -⟩ := ‹TcMma.Pipelined launch X .cpWrite (0,
      0) .aRead (0, 2)›
    simp [Execution.get, X] at hm

/-! ## cp → MMA A-read pipeline -/

private def aSpec (address : Nat) : TcMma.OperandSpec :=
  ⟨⟨.one, .i8 true true false, 128, 8, false, false, false, false, false⟩, src, src, 0, 0,
    some address, {}⟩

-- Thread 0 copies to column 16 and then issues an MMA reading A from column 16 or 24.
private def P (address : Nat) : Execution where
  tr := fun g => if g = 0 then
      [⟨0, .tc (.cp ⟨16, src, .s128x256b, [0], none⟩)⟩,
        ⟨1, .tc (.mma 64 (aSpec address) false [0, 0, 0, 0])⟩] else []
  rf := fun _ _ => none

-- Same warp, same address: pipelined, no commit or wait needed.
example : TcMma.WriteBefore launch (P 16) (0, 0) (0, 1) :=
  .inr (.inr ⟨by simp [SameWarp, SameCta, launch, Launch.threads],
    .inl (.single (.inl ⟨rfl, by decide, by decide⟩)),
    ⟨16, src, .s128x256b, [0], none⟩, 64, aSpec 16, false, [0, 0, 0, 0], ⟨0, rfl⟩, by decide,
    ⟨1, rfl⟩,
    rfl⟩)
-- A different A address is not the pipelined pair.
example : ¬ TcMma.Pipelined launch (P 24) .cpWrite (0, 0) .aRead (0, 1) := by
  rintro ⟨-, -, c, d, sp, acc, mask, ⟨pc, hc⟩, -, ⟨pc', hm⟩, ha⟩
  simp [Execution.get, P] at hc hm
  obtain ⟨-, rfl⟩ := hc
  obtain ⟨-, -, rfl, -, -⟩ := hm
  simp [aSpec] at ha

end
end PTX.Tests.TcCopy
