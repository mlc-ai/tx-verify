-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Advance
import Kernels.InklingRelDecode.Gen.StepPrologue
import Lemmas.Flow.SegChain
import Lemmas.Flow.Havoc

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof Arith32

set_option maxRecDepth 100000

private theorem start_segment {Q L g w} (won : Bool) (bcast : Value) :
    let d : D := {elected := won,broadcast := bcast}
    Seg kernel Assumptions.all L g 6 28 (facts Q L g w d 27) 34 (facts Q L g w d 34) := by
  intro d t ht
  seg_fp ht using (
    simp (disch := decide +kernel) only [valueOf_plain]
    seg_close [registerValue,u32,u64,b32,b64,r32,W])

theorem step_entry {Q L g w} (d : D) (hs : d.site = .sMax) : (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,won,bcast⟩ := d
  cases hs
  let d : D := ⟨.sMax,a,x,c,won,bcast⟩
  have prove (hi : Inv (g%L.block) d) : (code Q L g w).StepAtU d := by
    obtain ⟨rfl,rfl,rfl⟩ := hi
    apply straight (d := d) (z := .ld 0) Flow.code_27 rfl (fun _ => trivial)
      (fun h => fires_next (by trivial) h) (fun _ => rfl) rfl rfl ⟨rfl,rfl,rfl⟩ _
    exact SegU.of_seg (start_segment won bcast)
  exact ⟨fun hi => (prove hi).site hi,fun ins ht hi => (prove hi).step ins ht hi⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
