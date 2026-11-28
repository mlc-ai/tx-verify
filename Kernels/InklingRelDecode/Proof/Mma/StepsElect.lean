-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.StepsPaths
import Kernels.InklingRelDecode.Gen.StepMma01
import Kernels.InklingRelDecode.Gen.StepMma02
import Lemmas.Flow.LandsU
import Kernels.InklingRelDecode.Proof.Lib.MmaBits
import Lemmas.Flow.Footprint
import Lemmas.Flow.Step.SiteCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value}
local notation "MC" => (code L g regs w)
local notation "S" => SegU kernel Assumptions.all L g

private theorem choose_lane {d : D} {p r : Nat} (dest : Bool → D)
    (hc : kernel.code[d.site.pc]? = some ⟨none,.warp ⟨.elect,none,[some r,some p],[],
      some (.imm (-1))⟩⟩) (hr : r ≠ p) (fr : ∀ q ∈ (MC).facts d, q.1 ≠ r)
    (fp : ∀ q ∈ (MC).facts d, q.1 ≠ p)
    (hn : ∀ mask n ld, next L g d ⟨d.site.pc,.elect mask n ld⟩ =
      some (some (dest (laneOf L g == ld))))
    (sp : ∀ b ld, Inv d → S (d.site.pc + 1)
      ((p,.pred b) :: (r,b32 ld) :: (MC).facts d) (dest b).site.pc ((MC).facts (dest b)))
    (valid : ∀ b, Inv d → Inv (dest b)) : (MC).StepAtU d := by
  refine ⟨fun _ => ⟨_,hc,rfl,trivial⟩, ?_⟩
  intro t e u ins ht hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨mk,n,ld,rfl,rfl⟩ := fires_elect hf
  let b := laneOf L g == ld
  let t1 := setReg t r (b32 ld)
  have before := Code.at_of_atD ht rfl rfl
  obtain ⟨hpc,hsub,hacc,hfault,hR⟩ := before
  have h1 : At t1 d.site.pc ((r,b32 ld) :: (MC).facts d) :=
    ⟨hpc,hsub,hacc,hfault,Function.update_self ..,holds_update hR fr⟩
  have fresh : ∀ q ∈ (r,b32 ld) :: (MC).facts d, q.1 ≠ p := by
    rintro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hr
    · exact fp q hq
  obtain ⟨s,hτ,hgood⟩ := Code.landsU (C := MC) (d := dest b)
    (At.set (v := .pred b) h1 fresh) (sp b ld hi) (valid b hi) rfl rfl
  exact .inl (.inr ⟨dest b,s,hn mk n ld,hτ,hgood⟩)

variable {Q : Params} {m : Mem0} (hp : Pre Q L m) (i : Nat) (v : Value)
include hp

theorem qk_election : (MC).StepAtU ⟨.qkElect,i,v⟩ := by
  let d : D := ⟨.qkElect,i,v⟩
  refine choose_lane (d := d) (fun b => if b then {d with site := .qk 0} else afterQk d)
    Flow.code_2477 (by decide) (by fact_free) (by fact_free) ?_ ?_ ?_
  · intro _ _ ld
    by_cases h : laneOf L g = ld <;> simp [next,d,h]
  · intro b ld hi
    have hs := hp.sharedRange
    unfold sharedBytes at hs
    cases b
    · apply SegU.comp (b := 2500) (G := liveFacts L regs w d 2500)
      · apply SegU.of_seg (n := 22)
        dsimp only [d,code, ↓reduceIte]
        mma_arithmetic_span
      · exact after_qk hp.sharedRange hi.left hi.right
    · apply SegU.of_seg (n := 5)
      dsimp only [d,code, ↓reduceIte]
      mma_arithmetic_span
  · intro b hi
    cases b
    · exact inv_after hi.left hi.right
    · exact hi

theorem pv_election : (MC).StepAtU ⟨.pvElect,i,v⟩ := by
  let d : D := ⟨.pvElect,i,v⟩
  refine choose_lane (d := d) (fun b => if b then {d with site := .pv 0} else iterNext d)
    Flow.code_2525 (by decide) (by fact_free) (by fact_free) ?_ ?_ ?_
  · intro _ _ ld
    by_cases h : laneOf L g = ld <;> simp [next,d,h]
  · intro b ld hi
    have hs := hp.sharedRange
    unfold sharedBytes at hs
    cases b
    · apply SegU.comp (b := 2447) (G := liveFacts L regs w d 2447)
      · apply SegU.of_seg (n := 24)
        dsimp only [d,code, ↓reduceIte]
        mma_arithmetic_span
      · exact loop_back hp.sharedRange hi.right.left hi.right.right
    · apply SegU.of_seg (n := 4)
      dsimp only [d,code, ↓reduceIte]
      mma_arithmetic_span
  · intro b hi
    cases b
    · exact inv_iter hi.right.left hi.right.right
    · exact hi

end PTX.Kernels.InklingRelDecode.Proof.Mma
