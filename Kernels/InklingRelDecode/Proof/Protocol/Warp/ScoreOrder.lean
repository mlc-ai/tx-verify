-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.PollSynced
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Lib.PollMeetExit
import Kernels.InklingRelDecode.Proof.Softmax.Export.ShuffleRound

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
open PTX PTX.Flow

/-- Two lanes of a Softmax warp at the score poll in different rounds: the lane in the
earlier round precedes the other lane's poll, by the shuffles of the round between them. -/
public theorem score_ordered {Q L m X g h k j l l' p p' ok ok' a a' sc sc'} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hw : SameWarp L g h)
    (ge : X.get (g,k)=some ⟨1257,.wait l p ok a sc⟩)
    (hh : X.get (h,j)=some ⟨1257,.wait l' p' ok' a' sc'⟩)
    (lt : pollRound 1257 ((X.tr g).take k)<pollRound 1257 ((X.tr h).take j)) :
    PollBefore L kernel X (g,k) (h,j) := by
  have len : j<(X.tr h).length := (List.getElem?_eq_some_iff.mp hh).1
  have x := Softmax.Export.score_shuffles hp hX hf ge
  have y := Softmax.Export.score_shuffles hp hX hf hh
  have cta : g/L.block=h/L.block := hw.1.2.2
  rw [cta] at x
  apply Lib.meet_poll_shfl hX hw ge _ len
  have base := Lib.shflBase_lt lt
  omega

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Warp
