-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.IndexWalk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.ParamSteps
public import Lemmas.Flow.DivStep
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepIndex

@[expose] public section

/-! # The index warp's block heads: the divisions by the page size

The code between a block's next-pair load and the wait on the slot (pcs 2430-2445 of the main
loop, 2518-2533 of the extra loop) divides the lane's two index words by the page size
(`div.u32`: `%r589`, `%r592`; `%r627`, `%r630`) and keeps their remainders. As a UB-tolerant
segment it lands with the quotients and remainders in the facts (`ixPairs`) when the page size is
nonzero, and the thread is dead otherwise (`SegU.div_u32`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {g : Nat}

/-- No assumption has a local rule for one of the head's integer instructions. -/
theorem div_hL {pc : Nat} {i : IntInstr} (h1 : pc ∉ paramAdds) (h2 : pc ∉ prefetchTensorMapSites)
    (h3 : pc ∉ Assumptions.sharedBitsSites)
    (hp : ∀ t : TState, t.pc = pc → Assumptions.peerPackRule t (.int i) = none) :
    ∀ (t : TState), t.pc = pc → ∀ a ∈ asms, a.localRule L g t (.int i) = none :=
  fun t ht a ha => asms_localRule_int (by rw [ht]; exact h1) (by rw [ht]; exact h2)
    (by rw [ht]; exact h3) (hp t ht) a ha

/-- **The main loop's block head** (pcs 2432–2445): the quotients and remainders of the pair's
words by the page size, the position below the length. -/
theorem ixu_head (c : IxCtl) :
    SegU kernel Assumptions.all L g 2432 (factsFrom (ixLive 2432) (ixVal P L g c)) 2446
      (factsFrom (ixLive 2446) (ixVal P L g c)) := by
  refine SegU.div_u32 (F := factsFrom (ixLive 2432) (ixVal P L g c))
    (G := factsFrom (ixLive 2446) (ixVal P L g c)) (d := 589)
    (a := 2974) (r := 497) (x := c.m0) (y := pw P.page)
    Flow.code_2432 (mem_factsFrom_eq (by decide +kernel) rfl)
    (mem_factsFrom_eq (by decide +kernel) rfl)
    (not_mem_factsFrom (by decide +kernel))
    (div_hL (by decide) (by decide) (by decide)
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; rfl))) (h := fun _ => ?_)
  refine SegU.comp (b := 2435) (G := factsFrom (ixLive 2435) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.div_u32 (F := factsFrom (ixLive 2435) (ixVal P L g c))
    (G := factsFrom (ixLive 2446) (ixVal P L g c)) (d := 592)
    (a := 2973) (r := 497) (x := c.m1) (y := pw P.page)
    Flow.code_2435 (mem_factsFrom_eq (by decide +kernel) rfl)
    (mem_factsFrom_eq (by decide +kernel) rfl)
    (not_mem_factsFrom (by decide +kernel))
    (div_hL (by decide) (by decide) (by decide)
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; rfl))) (h := fun _ => ?_)
  ix_seg

/-- **The extra loop's block head** (pcs 2520–2533). -/
theorem ixu_xhead (c : IxCtl) :
    SegU kernel Assumptions.all L g 2520 (factsFrom (ixLive 2520) (ixVal P L g c)) 2534
      (factsFrom (ixLive 2534) (ixVal P L g c)) := by
  refine SegU.div_u32 (F := factsFrom (ixLive 2520) (ixVal P L g c))
    (G := factsFrom (ixLive 2534) (ixVal P L g c)) (d := 627)
    (a := 2982) (r := 502) (x := c.e0) (y := pw P.extraPage)
    Flow.code_2520 (mem_factsFrom_eq (by decide +kernel) rfl)
    (mem_factsFrom_eq (by decide +kernel) rfl)
    (not_mem_factsFrom (by decide +kernel))
    (div_hL (by decide) (by decide) (by decide)
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; rfl))) (h := fun _ => ?_)
  refine SegU.comp (b := 2523) (G := factsFrom (ixLive 2523) (ixVal P L g c)) (by ix_seg) ?_
  refine SegU.div_u32 (F := factsFrom (ixLive 2523) (ixVal P L g c))
    (G := factsFrom (ixLive 2534) (ixVal P L g c)) (d := 630)
    (a := 2981) (r := 502) (x := c.e1) (y := pw P.extraPage)
    Flow.code_2523 (mem_factsFrom_eq (by decide +kernel) rfl)
    (mem_factsFrom_eq (by decide +kernel) rfl)
    (not_mem_factsFrom (by decide +kernel))
    (div_hL (by decide) (by decide) (by decide)
      (fun t ht => Assumptions.peerPackRule_of_none (by rw [ht]; rfl))) (h := fun _ => ?_)
  ix_seg

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
