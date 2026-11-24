-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.UbStop

@[expose] public section

/-! # More instructions whose event is not undefined behaviour

A proof tool, beside `UbStop`: an election with the immediate full mask (`elect_imm_ok`), an
index shuffle of a 4-byte register with immediate lane, clamp and full mask (`shfl_imm_ok`), and a
group-2 tile load through a cluster address with an immediate offset and a cache policy
(`cpTensor_off_ok`), when its map, destination, barrier and coordinates evaluate, its
destination is 128-aligned, its box is aligned and the pair routes it. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- A full-mask election with an immediate mask is not undefined behaviour. -/
theorem elect_imm_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst : Option Nat} {p : Nat} {ty : Option DType} (f : Fault) :
    eventTmpl A L g t (.warp ⟨.elect, ty, [dst, some p], [], some (.imm (-1))⟩) ≠ .ub f := by
  have hm := electMember_full (Nat.mod_lt (g % L.block) (show 0 < 32 by decide))
  simp only [eventTmpl, warpTmpl_elect, electTmpl, readBits, pure, Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 4294967295 by decide]
  simp [laneOf, hm]

/-- A full-mask shuffle of a 32-bit register with immediate lane and clamp is not undefined
behaviour, in a launch of whole warps. -/
theorem shfl_imm_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {mode : ShflMode} {d : Nat} {p : Option Nat} {r : Nat} {b c : Int} {x : BitVec 64}
    (hm : mode = .bfly ∨ mode = .idx) (hb : L.block % 32 = 0)
    (hr : t.regs r = some (.bits 32 x)) (f : Fault) :
    eventTmpl A L g t (.warp { kind := .shfl mode, ty := some (.int .b 32),
                               dsts := some d :: (p.map some).toList,
                               srcs := [.reg r, .imm b, .imm c], mask := some (.imm (-1)) }) ≠
      .ub f := by
  have hrule : WarpInstr.rule { kind := .shfl mode, ty := some (.int .b 32),
                                dsts := some d :: (p.map some).toList,
                                srcs := [.reg r, .imm b, .imm c], mask := some (.imm (-1)) } =
      some .threadShfl := by
    rcases hm with rfl | rfl <;> cases p <;> rfl
  simp only [eventTmpl, warpTmpl, hrule, shflTmpl, readValue, readReg, hr, readBits, pure,
    Except.pure]
  rw [show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 by decide]
  simp [hb, Value.bytes]

/-- A group-2 tile load through a cluster address, with an immediate destination offset and a
cache policy, whose map, destination, barrier and coordinates evaluate, with a 128-aligned
destination, an aligned box and the pair's route, is not undefined behaviour. -/
theorem cpTensor_off_ok {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {dst mb : Nat} {off : Int} {map : Opnd} {cs : List Opnd} {pol : Option Opnd} {a outer : Nat}
    {desc : TensorDescriptor.Descriptor outer} {dl ml : Loc} {vs : List (BitVec 64)}
    (hp : cachePolicyRead L g t pol = .ok ())
    (hm : tensorMap L g t map cs .tile = .ok (a, ⟨outer, desc⟩))
    (hd : sharedEffAddr L g t true dst off = .ok dl) (h128 : dl.addr % 128 = 0)
    (hmb : mbarClusterLoc L g t mb 0 = .ok ml) (hvs : cs.mapM (readBits L g t 32) = .ok vs)
    (hbox : TensorDescriptor.BoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt))
    (hr : TensorRoute L (g / L.block) true .two dl ml) (f : Fault) :
    eventTmpl A L g t (.cpTensor true true dst off map cs mb 0 none .tile pol) ≠ .ub f := by
  have hbox' : requireBoxAligned desc
      (fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt) = .ok () :=
    (requireBoxAligned_eq_ok desc _).2 hbox
  have hcopy : tensorLoadCopy L g t true true dst off map cs mb 0 .tile =
      .ok (a, ⟨⟨outer, desc, fun axis => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt,
        dl, none⟩, ml, true, .two⟩) := by
    simp only [tensorLoadCopy, bind, Except.bind, pure, Except.pure, hm, hd, hmb, hvs, hbox',
      h128, TensorMode.transfer, TensorMode.rowCoordinates, ↓reduceIte]
  simp only [eventTmpl, tensorTmpl, hp, hcopy, hr, ofExec, bind, Except.bind, pure, Except.pure,
    ↓reduceIte]
  simp

end
end PTX.Flow
