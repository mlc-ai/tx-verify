-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.StepsPaths
import Kernels.InklingRelDecode.Proof.Mma.Offsets
import Kernels.InklingRelDecode.Gen.StepMma
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
import Lemmas.Flow.Footprint
import Lemmas.Flow.Step.SiteCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat} {regs : Nat → Value} {w : Value}
    (hp : Pre Q L m) (i : Nat) (v : Value)
include hp

theorem qk_prepare_step : (code L g regs w).StepAtU ⟨.qkBar2,i,v⟩ := by
  let d : D := ⟨.qkBar2,i,v⟩
  refine crossing (d := d) (dst := {d with site := .qkElect}) Flow.code_2466 rfl trivial
    (by advances) (fun _ => rfl) ?_ (fun hi => hi)
  intro hi
  obtain ⟨hb,hn⟩ := hi
  change i < low v at hb
  change low v ≤ 2147483646 at hn
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  apply SegU.comp (b := 2472) (G := liveFacts L regs w d 2472)
  · apply SegU.of_seg (n := 5)
    dsimp only [d,code, ↓reduceIte]
    mma_arithmetic_span
  · apply qk_base.comp
    apply SegU.of_seg (n := 4)
    dsimp only [d,code, ↓reduceIte]
    mma_arithmetic_span

theorem pv_prepare_step : (code L g regs w).StepAtU ⟨.pvBar2,i,v⟩ := by
  let d : D := ⟨.pvBar2,i,v⟩
  refine crossing (d := d) (dst := {d with site := .pvElect}) Flow.code_2514 rfl trivial
    (by advances) (fun _ => rfl) ?_ (fun hi => hi)
  intro hi
  obtain ⟨hz,hb,hn⟩ := hi
  change 0 < i at hz
  change i ≤ low v at hb
  change low v ≤ 2147483646 at hn
  have hs := hp.sharedRange
  unfold sharedBytes at hs
  apply SegU.comp (b := 2523) (G := liveFacts L regs w d 2523)
  · apply SegU.of_seg (n := 8)
    dsimp only [d,code, ↓reduceIte]
    mma_arithmetic_span
  · apply pv_base.comp
    apply SegU.of_seg (n := 1)
    dsimp only [d,code, ↓reduceIte]
    mma_arithmetic_span

end PTX.Kernels.InklingRelDecode.Proof.Mma
