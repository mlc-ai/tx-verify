-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.CloseRound
public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.NextPlain
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsPwE
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTail
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsBiasTailLoop
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsNarrBA
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part075
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Lemmas.Flow.BranchU
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof KernelHavoc
open Epilogue (i32 sub32 addi scmpi)
set_option maxRecDepth 100000
set_option maxHeartbeats 900000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

namespace FirstRound

def bump (v : V) : V :=
  { v with ppar := i32 1, spar := i32 1 }

def loopV (p : Params) (L : Launch) (g : Nat) (v : V) : V :=
  { bump v with
    nb := sub32 (r299 p L g v.scheduler) (r166 p L g v.scheduler),
    bt := r169 p L g v.scheduler, bpar := i32 1 }

abbrev skipBias (p : Params) (L : Launch) (g : Nat) (v : V) :=
  scmpi .lt .s (sub32 (r169 p L g v.scheduler) (r299 p L g v.scheduler)) 1

theorem ofStrict {a b F G} (h : ∃ n, Seg kernel Assumptions.all L g n a F b G) :
    SegU kernel Assumptions.all L g a F b G := h.elim fun _ hs => SegU.of_seg hs

noncomputable def mid (p : Params) (L : Launch) (g : Nat) (v : V) (W : Nat → Value) :=
  (7253,Mma.w32 (i32 1)) :: (7258,Mma.w32 (i32 1)) ::
  (1360,Value.bits 32 (r300 p L g v.scheduler)) ::
  (1359,Value.bits 32 (r299 p L g v.scheduler)) ::
    [(441,W 441), (1062,W 1062), (1069,W 1069), (1215,W 1215),
     (1226,W 1226), (1229,W 1229), (2390,W 2390), (2535,W 2535),
     (5127,W 5127), (6495,W 6495), (6497,W 6497), (7132,W 7132),
     (7500,W 7500), (7501,W 7501), (7502,W 7502), (7503,W 7503),
     (7506,W 7506), (7896,W 7896)]

theorem testBound (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 5006 (entryFacts p L g 5006 (.pwend .first) v) 5024
      ((630,.pred (skipBias p L g v)) ::
       mid p L g v (valueOf p L g (Softmax.D.mk' (.pwend .first) v.scheduler))) := by
  have hparams := params hp
  unfold mid entryFacts
  apply ofStrict
  seg_sym using (soft_seg)

end FirstRound
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
