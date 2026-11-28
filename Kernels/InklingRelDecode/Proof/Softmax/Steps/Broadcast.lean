-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Proof.Lib.LaneField
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code.Part019

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g i : Nat} {v : Carry}
private theorem lane_bits (d : D) :
    SegU kernel Assumptions.all L g 1262 (facts e L g d 1262) 1265 (facts e L g d 1265) := by
  let val := valueOf e L g d
  have sh : SegU kernel Assumptions.all L g 1262 (facts e L g d 1262) 1263 (facts e L g d 1263) :=
    Lib.shiftLive val Flow.code_1262 (by decide) (by decide : 944 ∈ ctlLive 1262)
      (Lib.shift_lane_word d.held.base).symm (by decide +kernel)
  have mask := Lib.lane_mask_step (L := L) (g := g) val (Lib.word d.held.base).toNat
    Flow.code_1263 (by decide) (by decide : 945 ∈ ctlLive 1263) rfl rfl
    (by decide +kernel : ∀ r ∈ ctlLive 1264, r = 506 ∨ r ∈ ctlLive 1263)
  apply sh.comp (mask.comp _)
  exact Lib.sum_span false (δ := (Lib.word d.held.base).toNat%4*2^21) (by omega)
    Flow.code_1264 (by decide) (by decide : 943 ∈ ctlLive 1264) rfl
    (fun _ h => Lib.delta_reg h (show 506 ∈ ctlLive 1264 by decide) rfl (by omega))
    (by decide +kernel)

private theorem other_word (w : Value) (r : Nat)
    (hr : r ∈ ctlLive 1261) :
    valueOf e L g ⟨.ldS,i,{v with base := w}⟩ r = valueOf e L g ⟨.shfl4,i,v⟩ r := by
  have free : ∀ r ∈ ctlLive 1261, r ∉ [506,944,945,1542,1543,1544,1611,1676] := by
    decide +kernel
  have off := free r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off
  obtain ⟨h1,h2,h3,h6,h7,h8,h4,h5⟩ := off
  simp only [valueOf,h1,h2,h3,h6,h7,h8,h4,h5,↓reduceIte]

theorem step_shfl4 : (code e L g).StepAtU ⟨.shfl4,i,v⟩ where
  site := fun _ => ⟨_,Flow.code_1261,rfl,trivial⟩
  step := by
    intro t ev u ins hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1261)
    obtain ⟨a,b,c,w,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
    have free : 944 ∉ ctlLive 1261 := by decide +kernel
    have absent : 944 ∉ ((code e L g).facts ⟨.shfl4,i,v⟩).map Prod.fst := by
      change 944 ∉ (factsFrom (ctlLive 1261) _).map Prod.fst
      rwa [factsFrom_keys]
    have hs := At.set (r := 944) (v := w) (Code.at_of_atD hat rfl rfl)
      (fun p h he => absent (he ▸ List.mem_map_of_mem h))
    obtain ⟨pc,sub0,acc,fault,regs⟩ := hs
    have coverage : ∀ r ∈ ctlLive 1262,
        r = 944 ∨ r ∈ ctlLive 1261 := by decide +kernel
    have keep : Holds (setReg t 944 w).regs (facts e L g ⟨.ldS,i,{v with base := w}⟩ 1262) := by
      apply holds_of_pointwise
      intro r hr
      rcases coverage r hr with rfl | hm
      · exact regs.1
      · rw [other_word (v := v) w r hm]
        exact holds_mem regs.2 (mem_factsFrom hm)
    obtain ⟨s,steps,good⟩ := Code.landsU (C := code e L g) (d := ⟨.ldS,i,{v with base := w}⟩)
      (u := PTX.next (setReg t 944 w)) ⟨pc,sub0,acc,fault,keep⟩
      (lane_bits _) (body_inv hi rfl rfl) rfl rfl
    exact .inl (.inr ⟨_,s,rfl,steps,good⟩)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
