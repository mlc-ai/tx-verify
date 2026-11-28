-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CtlSteps
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepTma

@[expose] public section

/-! # The landing at a block's first gather

The code before a block's first gather forms the generic pointer to `param_1` (pc 2255) and adds
the descriptor offset of the main or the extra cache (`%rd3051`, pc 2256): the kernel's
parameter-pointer reading turns it into the descriptor's numeric address (`run_paramAddReg`),
which the symbolic walk does not know. `land_g0` crosses these two instructions by hand and the
rest by `seg_ctl`, from the second quadruple's last element to the first gather. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A UB-tolerant segment of the TMA warp, closed by the table's terms. -/
macro "tma_segU" : tactic => `(tactic| (
  try simp only [facts, Site.pc, coordPc, afterCoord, afterGather, Fin.isValue,
    Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte,
    Nat.reduceEqDiff, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Nat.reduceSub, Fin.reduceAdd,
    Fin.val_ofNat, Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  seg_ctl rulesFrame, KernelHavoc.hooks_ok using first | rfl | sym_close))

/-- **From the second quadruple's last element to the first gather.** -/
theorem land_g0 (hp : Pre P L m) (d : D) (_hs : d.site = .coord3 1) (v : Value) :
    SegU kernel Assumptions.all L g 2255
      (factsFrom (Flow.live 2255) (valueOf P L g (afterQuad d 1 v))) 2259
      (facts P L g (afterQuad d 1 v)) := by
  have h2 : Seg kernel Assumptions.all L g 1 2255
      (factsFrom (Flow.live 2255)
        (valueOf P L g (afterQuad d 1 v)))
      2256
      ((3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255)
          (valueOf P L g (afterQuad d 1 v))) :=
      fun t ht =>
    ⟨_, run_cvtaParam (pc := 2255) Flow.code_2255 ht
      (holds_mem (atHolds ht) (r := 2990) (mem_factsFrom (by decide))),
      At.set ht (not_mem_factsFrom (by decide))⟩
  have h3 : Seg kernel Assumptions.all L g 1 2256
      ((3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255)
          (valueOf P L g (afterQuad d 1 v))) 2257
      ((3049, .bits 64
        (BitVec.ofNat 64 (P.param1Base + (sel (scmp .lt .u d.cnt (nmain d.l0)) 768 896).toNat))) ::
        (3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255)
          (valueOf P L g (afterQuad d 1 v))) :=
      fun t ht =>
    ⟨_, run_paramAddReg (pc := 2256) Flow.code_2256 ht (by decide)
      (holds_mem (atHolds ht) (List.mem_cons_self ..))
      (holds_mem (atHolds ht) (r := 3051) (List.mem_cons_of_mem _ (mem_factsFrom (by decide))))
      hp.param1Object, At.set ht (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · decide
        · exact not_mem_factsFrom (by decide) q hq)⟩
  have h4 : SegU kernel Assumptions.all L g 2257
      ((3049, .bits 64
        (BitVec.ofNat 64 (P.param1Base + (sel (scmp .lt .u d.cnt (nmain d.l0)) 768 896).toNat))) ::
        (3052, .ptr 64 true (.param (param "1")) 0) ::
        factsFrom (Flow.live 2255)
          (valueOf P L g (afterQuad d 1 v))) 2259
      (facts P L g (afterQuad d 1 v)) := by
    tma_segU
  exact (SegU.of_seg (h2.comp h3)).comp h4

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
