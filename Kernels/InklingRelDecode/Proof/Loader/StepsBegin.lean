-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Inputs
import Kernels.InklingRelDecode.Proof.Loader.StepsIndex
import Kernels.InklingRelDecode.Proof.Loader.StepsEntry
import Kernels.InklingRelDecode.Proof.Loader.StepsBranch
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.LandsU
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The barrier after the vector read follows both outcomes of the signed compare,
including a fault during setup. -/
theorem beginBar_step {Q : Params} {L : Launch} {g : Nat} {w : Value} {rest : Nat → Value}
    (i n a b : Value) :
    (code L g w (inputs Q L g rest)).StepAtU ⟨.beginBar,i,n,a,b⟩ := by
  by_cases hskip : toSigned 32 (bits n) ≤ toSigned 32 (bits i)
  · exact beginBar_skip i n a b hskip
  let regs := inputs Q L g rest
  let start : D := ⟨.beginBar,i,n,a,b⟩
  let finish : D := ⟨.poll,i,n,a,b⟩
  refine ⟨fun _ => ⟨_, Flow.code_2346, rfl, trivial⟩, ?_⟩
  intro t e u ins ht _ hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_2346)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync _ _) from trivial) hf
  have cmp := compare_entry (L := L) (g := g) (w := w) (regs := regs) i n a b
  simp only [hskip, decide_false] at cmp
  let F := (19, Value.pred false) :: (code L g w regs).facts start
  have br : Seg kernel Assumptions.all L g 1 2348 F 2349 F := by
    intro u hu
    dsimp only [F, start, code] at hu ⊢
    seg_fp hu using rfl
  have run := cmp.comp ((SegU.of_seg br).comp
    ((SegU.of_seg (setup_span i n a b)).comp ((index_span i n a b).comp (ring_head i n a b))))
  obtain ⟨v, hτ, hv⟩ := Code.landsU (C := code L g w regs) (d := finish)
    (At.next (Code.at_of_atD ht rfl rfl)) run (fun h => by cases h) rfl rfl
  exact .inl (.inr ⟨finish, v, by simp [next, hskip, finish], hτ, hv⟩)

end PTX.Kernels.InklingRelDecode.Proof.Loader
