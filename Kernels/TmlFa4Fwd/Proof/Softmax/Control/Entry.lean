-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine
public import Lemmas.Flow.Havoc
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow PTX.Proof
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
variable {p : Params} {L : Launch} {g : Nat} {m : Mem0}

noncomputable abbrev entryFacts (p : Params) (L : Launch) (g : Nat) (pc : Nat) (s : Site) (v : V) :=
  factsFrom (ctlLive pc) (valueOf p L g (Softmax.D.mk' s v.scheduler))

private theorem ofStrict {a b F G} (h : ∃ n, Seg kernel Assumptions.all L g n a F b G) :
    SegU kernel Assumptions.all L g a F b G := h.elim fun _ hs => SegU.of_seg hs

theorem enterPlain (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 6661 (entryFacts p L g 6661 (.ws .plain) v)
      6676 (entryFacts p L g 6676 (.ws .plain) v) := by
  have hparams := params hp
  apply ofStrict
  unfold entryFacts
  seg_sym using (soft_seg)

theorem enterFinal (hp : Pre p L m) (v : V) :
    SegU kernel Assumptions.all L g 7605 (entryFacts p L g 7605 (.fin 0) v)
      7614 (entryFacts p L g 7614 (.fin 0) v) := by
  have hparams := params hp
  apply ofStrict
  unfold entryFacts
  seg_sym using (soft_seg)

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
