-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ScoreLoad
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part054
import Kernels.TmlFa4Fwd.Gen.StepSoftmax
import Kernels.TmlFa4Fwd.Proof.Common.Havoc
import Lemmas.Flow.SegCtl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow KernelHavoc
set_option maxRecDepth 100000

private theorem span0 {p L g} (v : V) : ScoreSpan p L g .first 0 v := by
  unfold ScoreSpan Softmax.facts
  seg_ctl rules_frame, hooks_ok

private theorem span1 {p L g} (v : V) : ScoreSpan p L g .first 1 v := by
  unfold ScoreSpan Softmax.facts
  seg_ctl rules_frame, hooks_ok

private theorem span2 {p L g} (v : V) : ScoreSpan p L g .first 2 v := by
  unfold ScoreSpan Softmax.facts
  seg_ctl rules_frame, hooks_ok

private theorem span3 {p L g} (v : V) : ScoreSpan p L g .first 3 v := by
  unfold ScoreSpan Softmax.facts
  seg_ctl rules_frame, hooks_ok

theorem stepAt_sld_firstU {p L g} (c : Fin 4) (v : V) :
    (code p L g).StepAtU ⟨.sld .first c,v,0,[]⟩ := by
  apply stepAt_score_of_span false
  fin_cases c
  · exact span0 v
  · exact span1 v
  · exact span2 v
  · exact span3 v

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
