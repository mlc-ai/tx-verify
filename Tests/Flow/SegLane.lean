-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegLane
public import Kernels.TmlFa4Fwd.Proof.SoftmaxExponent
public import Kernels.TmlFa4Fwd.Flow.Code
public import Kernels.TmlFa4Fwd.Flow.Sites

/-! # A template segment with `-∞` lanes (`Seg.segLaneTwo`)

tml-fa4's `swExp2` reads the lanes of its software `exp2` template by `swExp2Lane`, which gives
`0` for the `-∞` encoding (a masked bias half). Its rule is `execSegmentLane swExp2Lane` by
definition, and at the instance of pc 7090 (`matched7090`) a state whose two lane inputs hold
`-∞` steps to the outputs `0`, `0` in one piece. -/

namespace PTX.Tests.SegLane
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

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

/-- The kernel's rule is the library's lane-read segment effect. -/
theorem swExp2_lane (m : SegMatch CuteSlot) (t : TState) :
    Assumptions.execSwExp2 m t = execSegmentLane Assumptions.swExp2Lane m t := rfl

/-- The `-∞` encoding. -/
abbrev negInf : Value := .bits 32 (BitVec.ofNat 64 0xFF800000)

/-- Both lane inputs `-∞`, every other register a word. -/
def base : Nat → Value := fun r => if r = 5564 ∨ r = 5565 then negInf else .bits 32 0

theorem keys_nodup : (segKeys matched7090 CuteSlot.y0 CuteSlot.y1).Nodup := by decide

theorem keys_cover : ∀ r ∈ [5128, 5131], r ∈ segKeys matched7090 CuteSlot.y0 CuteSlot.y1 ∨
    (r ∉ segKeys matched7090 CuteSlot.y0 CuteSlot.y1 ++
      matched7090.shape.writes.map matched7090.regOf ∧ r ∈ [5564, 5565]) := by decide

theorem lane0 : Assumptions.swExp2Lane (valueEx base [] (matched7090.regOf CuteSlot.x0)) =
    .ok 0 := Assumptions.swExp2Lane_negInf

theorem lane1 : Assumptions.swExp2Lane (valueEx base [] (matched7090.regOf CuteSlot.x1)) =
    .ok 0 := Assumptions.swExp2Lane_negInf

example (l : Launch) (g : Nat) :
    Seg kernel Assumptions.all l g 1 7090 (factsFrom [5564, 5565] (valueEx base [])) 7121
      (factsFrom [5128, 5131]
        (valueEx base (segValsY matched7090 CuteSlot.y0 CuteSlot.y1 0 0 ++ []))) := by
  have hA : Assumptions.all = [Assumptions.idealArith, Assumptions.approx, Assumptions.lg2,
      Assumptions.bf16Convert] ++ Assumptions.swExp2 ::
      (Assumptions.synchronization ++ [Assumptions.inputReadOnly]) := rfl
  rw [hA]
  refine Seg.segLaneTwo Flow.code_7090 rfl (fun t h1 h2 h3 => ?_) rfl (.inl rfl) (by decide)
    lane0 (by decide) lane1 keys_nodup keys_cover (by seg_free_pc)
  simp only [Assumptions.swExp2, h1, h2, h3, List.isEmpty_nil, and_self, matchAt7090]
  rfl

end
end PTX.Tests.SegLane
