-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SegSym
public import Kernels.TmlFa4Fwd.Audit.SoftwareExponent
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Flow.Sites

/-! # A kernel-assumption segment as one step of `seg_sym`

The software `exp2` of tml-fa4's softmax low block starts at pc 7090: 31 instructions that clamp,
pack, round down, evaluate a degree-3 polynomial, unpack and build each lane's exponent
(`cuteExp2Define`). The kernel's assumption `Assumptions.swExp2` reads that stretch as one local
step that gives each lane the exact `2 ^ x` (`Assumptions.swExp2Lane`, `execSwExp2`), at the stop
pc 7121. Its values are the lanes' numbers, which the instruction stream does not determine as
exact reals, so the kernel states the step once (`Seg.segRunStep`) with the old `SoftmaxExponent`
lemmas (`softwareExponentValues`), and `seg_sym` takes that statement as one step of its walk: the
hypothesis `seg7090` below is the segment's piece from the two lane inputs to their exponents.

Checked here: `seg_sym` walks the goal `∃ n, Seg kernel Assumptions.all l g n 7090 inF 7121 outG`
by taking the assumption's segment step (one step, not 31 instructions), which it finds by the
hypothesis whose type is that segment from 7090. -/

namespace PTX.Tests.SegStep
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section

set_option maxRecDepth 200000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 8000000

/-- The lane inputs the software `exp2` of pc 7090 reads: slots `x0`, `x1` hold the numbers 0
and 1 (`max.f32` of each lane, at %r5564 and %r5565). -/
def inF : List (Nat × Value) := [(5564, .float .f32 0), (5565, .float .f32 1)]

/-- The lane outputs of the segment: slots `y0`, `y1` (`2 ^ 0` and `2 ^ 1`, at %r5128 and
%r5131). -/
def outG : List (Nat × Value) := [(5128, .float .f32 1), (5131, .float .f32 2)]

/-- The matched shape of the software `exp2` instance at pc 7090: the defining 31-instruction
shape, its slots assigned the registers of this instance (in the order the template's matcher
builds, the code's instructions reversed), stopping after them at pc 7121. -/
def matched7090 : SegMatch CuteSlot where
  shape := cuteExp2Define
  reg := [(CuteSlot.y1, 5131), (CuteSlot.o1, 9829), (CuteSlot.xe1, 9828), (CuteSlot.fe1, 9827),
    (CuteSlot.xr1, 9826), (CuteSlot.y0, 5128), (CuteSlot.o0, 9825), (CuteSlot.xe0, 9824),
    (CuteSlot.fe0, 9823), (CuteSlot.xr0, 9822), (CuteSlot.q1, 5133), (CuteSlot.q0, 5130),
    (CuteSlot.p3, 8776), (CuteSlot.c0, 8775), (CuteSlot.k0, 5670), (CuteSlot.p2, 8774),
    (CuteSlot.c1, 8773), (CuteSlot.k1, 5669), (CuteSlot.p1, 8772), (CuteSlot.c3, 8771),
    (CuteSlot.k3, 5668), (CuteSlot.c2, 8770), (CuteSlot.k2, 5667), (CuteSlot.f, 8769),
    (CuteSlot.s, 8768), (CuteSlot.ri1, 5132), (CuteSlot.ri0, 5129), (CuteSlot.r, 8767),
    (CuteSlot.cM, 8766), (CuteSlot.kM, 5666), (CuteSlot.a, 8765), (CuteSlot.m1, 5665),
    (CuteSlot.x1, 5565), (CuteSlot.m0, 5664), (CuteSlot.x0, 5564)]
  stop := 7121

/-- The instance at pc 7090 is the template's first shape, matched at these registers. -/
theorem matchAt7090 : cuteExp2.matchAt kernel 7090 = some matched7090 := rfl

/-- The lanes' numbers as the segment reads them, and the exponents it gives them. -/
def raw7090 : CuteSlot → Value
  | .x0 => .float .f32 0
  | .x1 => .float .f32 1
  | _ => .bits 32 0

/-- The exact `2 ^ x` of the two lanes. -/
def exp7090 : CuteSlot → ℝ
  | .x0 => 1
  | .x1 => 2
  | _ => 0

/-- The segment's result state holds the two lanes' exponents in the output registers. -/
theorem result_holds (R : Nat → Option Value) (cf : Option Bool) :
    Holds (Softmax.softwareExponentResult matched7090 ⟨7090, R, cf, 0, [], none⟩ exp7090).regs
      outG := by
  refine ⟨?_, ?_, trivial⟩
  · show (Softmax.softwareExponentResult matched7090 ⟨7090, R, cf, 0, [], none⟩ exp7090).regs
      5128 = some (.float .f32 1)
    rfl
  · show (Softmax.softwareExponentResult matched7090 ⟨7090, R, cf, 0, [], none⟩ exp7090).regs
      5131 = some (.float .f32 2)
    rfl

/-- **The segment at pc 7090 is one step**: from the two lane inputs to the exact exponents of
both lanes at pc 7121. -/
theorem seg7090 (L : Launch) (g : Nat) :
    ∃ n, Seg kernel Assumptions.all L g n 7090 inF 7121 outG := by
  apply Seg.segRunStep
  intro R cf hR
  have hsite : 7090 ∈ Assumptions.swExp2Sites := by
    simp [Assumptions.swExp2Sites]
  have hcode : kernel.code[7090]? = some
      { guard := none,
        op := PTX.Op.float
          { op := PTX.FOp.max, ty := { fmt := PTX.FloatFmt.f32, lanes := 1 }, srcTys := [],
            cmpTy := none, rnd := none, mode := PTX.FMode.ieee, ftz := false, sat := false,
            relu := false, oob := false, nanMod := false, xorsign := false, absMod := false,
            dsts := [some 5664], srcs := [PTX.Opnd.reg 5564, PTX.Opnd.f32imm 3271426048] } } := by
    code_lookup
  have hmatch := matchAt7090
  have hio : matched7090.shape.io = [(CuteSlot.x0, CuteSlot.y0), (CuteSlot.x1, CuteSlot.y1)] :=
    rfl
  have hinput : ∀ p ∈ matched7090.shape.io,
      (⟨7090, R, cf, 0, [], none⟩ : TState).regs ((matched7090.reg.lookup p.1).getD 0)
        = some (raw7090 p.1) := by
    intro p hp
    rw [hio] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show (⟨7090, R, cf, 0, [], none⟩ : TState).regs 5564 = some (.float .f32 0)
      exact holds_mem hR (r := 5564) (v := .float .f32 0) (by simp [inF])
    · rcases List.mem_cons.mp hp with rfl | hp
      · show (⟨7090, R, cf, 0, [], none⟩ : TState).regs 5565 = some (.float .f32 1)
        exact holds_mem hR (r := 5565) (v := .float .f32 1) (by simp [inF])
      · simp at hp
  have heval : ∀ p ∈ matched7090.shape.io,
      Assumptions.swExp2Lane (raw7090 p.1) = .ok (exp7090 p.1) := by
    intro p hp
    rw [hio] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show Assumptions.swExp2Lane (raw7090 CuteSlot.x0) = .ok (exp7090 CuteSlot.x0)
      simp [Assumptions.swExp2Lane, raw7090, exp7090, cuteExp2]
      rfl
    · rcases List.mem_cons.mp hp with rfl | hp
      · show Assumptions.swExp2Lane (raw7090 CuteSlot.x1) = .ok (exp7090 CuteSlot.x1)
        simp [Assumptions.swExp2Lane, raw7090, exp7090, cuteExp2]
        rfl
      · simp at hp
  refine ⟨Softmax.softwareExponentResult matched7090 ⟨7090, R, cf, 0, [], none⟩ exp7090,
    Softmax.softwareExponentValues raw7090 exp7090 ⟨rfl, rfl, rfl, rfl, hR⟩ hsite hcode rfl
      hmatch (Or.inl rfl) hinput heval, rfl, rfl, rfl, rfl, result_holds R cf⟩

/-- **`seg_sym` takes the assumption's segment as one step**: the goal is the very segment the
hypothesis states, and the walk at pc 7090 finds it (it cannot reduce the 31 instructions to the
lanes' exponents itself) and glues it. -/
example (l : Launch) (g : Nat) :
    ∃ n, Seg kernel Assumptions.all l g n 7090 inF 7121 outG := by
  have hseg := seg7090 l g
  seg_sym using (intro t h; seg_fp h using first | rfl | sym_close)

end

end PTX.Tests.SegStep
