-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Base

@[expose] public section

/-! # The first block's V arrival: the transition into the later blocks

The arrival ends the first block. Its segment computes the later blocks' first block
`%r56 = %r28 - 2` (pc 907, `add.s32` with the immediate `-2`) and then branches on it: into the
warm rounds (the first page round's row is an offset from `%r56`), or past them (the last Bias
block, the steady rounds or the scheduler's second pass). A term that adds the 32-bit pattern of
`-2` to a free word runs away when evaluated, so the segment is cut at pc 909, after `%r56` and
the first branch's predicate are computed (`cutRegs`: the facts there are the arrival's table
with these four registers), and the rest of the walk runs with `%r56` as a free word `r56`: the
successor's recorded `V.r56` and the register are both `r56`, so no condition the walk decides
contains the literal. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (scmpi addi)

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- The registers the arrival's segment computes before pc 909: the predicates of the last Bias
block (`%p165`, `%p7`), the later blocks' first block `x` (`%r56`) and whether the tile has
fewer than two blocks (`%p166`). -/
def cutRegs (v : V) (x : BitVec 64) : List (Nat × Value) :=
  [(165, .pred (scmpi .gt .s v.su.r28 10)),
   (7, .pred (scmpi .gt .s v.su.r28 10 && scmpi .lt .s v.su.r29 0)),
   (1116, .bits 32 x), (166, .pred (scmpi .lt .s v.su.r28 2))]

/-- The register values at pc 909: `cutRegs`, else the arrival's table. -/
def valCut (p : Params) (L : Launch) (g w : Nat) (ent : Nat → Value) (v : V) (x : BitVec 64)
    (r : Nat) : Value :=
  ((cutRegs v x).lookup r).getD (valueOf p L g w ent (D.mk' (.arrive .prime true) v) r)

set_option hygiene false in
/-- **The first block's V arrival.** The segment to pc 909 by `seg_auto`, the rest by `seg_sym`
with `%r56` generalized to a free word. -/
theorem stepAt_arr_prime (hp : Pre p L m) (_hg : g < L.threads) (hw : w = 14 ∨ w = 15) (d : D)
    (hk : d.k = 0) (hs : d.site = .arrive .prime true) :
    (code p L g w ent).StepAt d := by
  have hparams := Epilogue.params hp
  obtain ⟨_h13, _h12, _h7, _h8⟩ := warp_facts hw
  obtain ⟨s, v, k⟩ := d
  cases hk
  subst hs
  refine PTX.Flow.Code.StepAt.of ?site ?_
  case site => site_event (trivial)
  refine' (PTX.Flow.Code.step_issue (dn := ?dn) ?hc ?hadv ?hn ?hs ?ha ?hl)
  case hc => code_lookup
  case hadv => advances
  case hs => rfl
  case ha => rfl
  case hn => intro e; next_simp [succ, D.mk', afterArrive]
  case hl =>
    intros
    refine ⟨?seg, ?sub, ?acc, ?inv⟩
    case sub => rfl
    case acc => rfl
    case inv => site_norm; load_inv
    case seg =>
      intro _
      site_norm
      refine Seg.comp_ex (q := 909)
        (H := Flow.factsFrom (Flow.live 909) (valCut p L g w ent v (addi (blocks p L g v) (-2))))
        ?_ ?_
      · seg_auto using load_seg
      · simp only [afterPrime, afterWarm, afterTail, passStart, pgEnter, rowCond, D.iteS, D.ite,
          reduceCtorEq, ↓reduceIte]
        generalize addi (blocks p L g v) (-2) = r56
        seg_sym using load_seg

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
