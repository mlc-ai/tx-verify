-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.DataDeadline
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Softmax.Producer
import Kernels.InklingRelDecode.Proof.Softmax.Export.Time
import Lemmas.Step.ExitLast

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- **Softmax lane zero that exited polled every block's score slot.** -/
public theorem exited_polls {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (hu : NoUbLane X g)
    (hg : g<L.threads) (leader : g%L.block=0) (exit : X.get (g,k)=some ⟨pc,.exit⟩) :
    Lib.blocksOf Q L (g/L.block)≤pollRound 1257 ((X.tr g).take k) := by
  by_contra! short
  have hi : Lib.blocksOf Q L (g/L.block)-1<Lib.blocksOf Q L (g/L.block) := by omega
  let r := Lib.blocksOf Q L (g/L.block)-1
  have issue {w ent d n j e} (get : X.get (g,j)=some e)
      (hs : stateAt (thread Q L) X g j=some (some (softState w ent d n)))
      (site : d.site=.arrive) (iter : d.i=r) : False := by
    have ref : Ref _ d (softCounts n) := (reached_table hf hg (noUbBefore_of_get hX get) hs).2
    obtain ⟨s,i,v⟩ := d
    obtain rfl : s=.arrive := site
    change i=r at iter
    subst i
    have prev := (fcount hs (.poll 1257)).symm.trans (congrArg Cnt.s ref.ledger)
    change ((X.tr g).take j).countP (okPollAt 1257)=r+1 at prev
    have len := (List.getElem?_eq_some_iff.mp get).1
    have done := Execution.exit_last hX hg exit
    change j<(X.tr g).length at len
    have mono := countP_take_mono (okPollAt 1257) (X.tr g) (show j≤k by omega)
    change _ ≤ pollRound 1257 ((X.tr g).take k) at mono
    omega
  have no : threadTime (schedule Q L) X g≤Lib.Slots.probArrival r ∧
      ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
    apply data_deadline hp hX hu hg (by omega)
      (by unfold Lib.Slots.probArrival Lib.Slots.softmax Lib.Slots.frame; omega)
      (beforeArrival r) ⟨Nat.zero_le _,by decide⟩ (fun _ h => (arrival_clock h).1)
    · intro w ent d n j e get hs old eq
      obtain ⟨site,iter⟩ := (arrival_clock old).2 eq
      exact issue get hs site iter
    · intro w ent d n j e dn get hs old go
      have limit := reached_limit hp hX hg (List.getElem?_eq_some_iff.mp get).1.le hs
      have step := before_arrival_step leader (limit ▸ hi) old (issue get hs) go
      exact ⟨step,step.2⟩
  exact no.2 k pc exit

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
