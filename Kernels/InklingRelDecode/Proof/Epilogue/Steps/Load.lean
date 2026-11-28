-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Steps.Base
import Kernels.InklingRelDecode.Proof.Lib.LaneField
import Kernels.InklingRelDecode.Proof.Lib.AddBase
import Kernels.InklingRelDecode.Flow.Code.Part040

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
variable {e : Entry} {L : Launch} {g : Nat} {v : Value}
private theorem lane_bits (w : Value) :
    SegU kernel Assumptions.all L g 2604 (facts e L g w 2604) 2607 (facts e L g w 2607) := by
  let val := valueOf e L g w
  have sh : SegU kernel Assumptions.all L g 2604 (facts e L g w 2604) 2605 (facts e L g w 2605) :=
    Lib.shiftLive val Flow.code_2604 (by decide) (by decide : 1828 ∈ ctlLive 2604)
      (Lib.shift_lane_word w).symm (by decide +kernel)
  have mask := Lib.lane_mask_step (L := L) (g := g) val (Lib.word w).toNat
    Flow.code_2605 (by decide) (by decide : 1829 ∈ ctlLive 2605) rfl rfl
    (by decide +kernel : ∀ r ∈ ctlLive 2606, r = 1830 ∨ r ∈ ctlLive 2605)
  apply sh.comp (mask.comp _)
  exact Lib.sum_span true (δ := (Lib.word w).toNat%4*2^21) (by omega)
    Flow.code_2606 (by decide) (by decide : 491 ∈ ctlLive 2606) rfl
    (fun _ h => Lib.delta_reg h (show 1830 ∈ ctlLive 2606 by decide) rfl (by omega))
    (by decide +kernel)

private theorem other_word (w : Value) (r : Nat)
    (hr : r ∈ ctlLive 2603) :
    valueOf e L g w r = valueOf e L g v r := by
  have ks : ∀ x ∈ ctlLive 2603, x≠1827 ∧ x≠1828 ∧ x≠1829 ∧ x≠1830 := by decide +kernel
  obtain ⟨a,b,c,d⟩ := ks r hr
  simp only [valueOf,a,b,c,d,↓reduceIte]

theorem step_shfl : (code e L g).StepAtU ⟨.shfl,v⟩ where
  site := fun _ => ⟨_,Flow.code_2603,rfl,trivial⟩
  step := by
    intro t ev u ins hat _ hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2603)
    obtain ⟨a,b,c,w,ok,rfl,rfl⟩ := fires_shfl (p := none) hf
    have free : 1828 ∉ ctlLive 2603 := by decide +kernel
    have absent : 1828 ∉ ((code e L g).facts ⟨.shfl,v⟩).map Prod.fst := by
      change 1828 ∉ (factsFrom (ctlLive 2603) _).map Prod.fst
      rwa [factsFrom_keys]
    have hs := At.set (r := 1828) (v := w) (Code.at_of_atD hat rfl rfl)
      (fun p h he => absent (he ▸ List.mem_map_of_mem h))
    obtain ⟨pc,sub0,acc,fault,regs⟩ := hs
    have coverage : ∀ r ∈ ctlLive 2604,
        r = 1828 ∨ r ∈ ctlLive 2603 := by decide +kernel
    have keep : Holds (setReg t 1828 w).regs (facts e L g w 2604) := by
      apply holds_of_pointwise
      intro r hr
      rcases coverage r hr with rfl | hm
      · exact regs.1
      · rw [other_word (v := v) w r hm]
        exact holds_mem regs.2 (mem_factsFrom hm)
    obtain ⟨s,steps,good⟩ := Code.landsU (C := code e L g) (d := ⟨.load,w⟩)
      (u := PTX.next (setReg t 1828 w)) ⟨pc,sub0,acc,fault,keep⟩
      (lane_bits _) trivial rfl rfl
    exact .inl (.inr ⟨_,s,rfl,steps,good⟩)

theorem step_load : (code e L g).StepAtU ⟨.load,v⟩ := by
  apply Code.tcLoadU (C := code e L g) (d := ⟨.load,v⟩) (dn := ⟨.waitLd,v⟩)
    (live := ctlLive 2607) Flow.code_2607 (fun _ h => by cases h)
    (by change Assumptions.all.any (·.tcLdWait 2607) = false; decide +kernel)
    rfl (by decide +kernel) (fun _ _ => rfl) rfl rfl rfl rfl trivial
  exact Lib.control_span (live := ctlLive) (p := 2607) (start := 2608) (stop := 2608)
    (by decide +kernel)

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
