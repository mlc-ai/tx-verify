-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Observe
import Lemmas.Protocol.UnitNotify

@[expose] public section

/-! # What the dequantized buffer ring's waits observe

* `dequantReady_observes`: a successful poll of `dequantReady s` of CTA `c` with `u` earlier ones
  is the MMA lane's, and it observes every dequant lane's arrival of use `u` on it
  (`KRing.full_observes` of `dqSlot`, `Unit.Obj.wait_obs`);
* `svDone_observes`: a dequant lane's successful poll of `svDone s` with `u + 1` earlier ones
  observes the notification of the MMA lane's commit with `u` earlier commits to it
  (`Notify.Obj.observes`, the reuse paths from `KRing.reachE`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hR hI hB hN

/-- **The ready wait observes the block.** A successful poll of `dequantReady s` of CTA `c` with
`u` earlier ones is the MMA lane's, and it observes every dequant lane's arrival of use `u`. -/
theorem dequantReady_observes {c : Nat} {s : Fin 2} {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c (.dequantReady s)) p true acq sc⟩) :
    h = mmaLane L X c ∧ ∀ a : Fin 128, ∃ i pc' sc', X.get (deqLane L c a, i) =
        some ⟨pc', .arrive (mbarLoc L c (.dequantReady s)) 0 1 true sc'⟩ ∧
      arrivals (mbarLoc L c (.dequantReady s)) ((X.tr (deqLane L c a)).take i) =
        okPolls (mbarLoc L c (.dequantReady s)) ((X.tr h).take j) ∧
      WaitObserves X (.thread (deqLane L c a, i)) (h, j) (mbarLoc L c (.dequantReady s)) acq
        sc := by
  have hh : h = mmaLane L X c := by
    rcases dequantReady_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ | ⟨hon, hc, -⟩ |
      ⟨-, -, hk⟩
    · cases hk
    · have := laneOn_eq (mmaOne hp hX hFw) he (notUb_of_kind (mbar_kind hX hR he rfl)) hon
      rwa [hc] at this
    · cases hk
  subst hh
  have O := dequantReady_obj hp hX hFw hR hI hB c s
  have hu := PairTmaRing.okPolls_lt_of_get he
  refine ⟨rfl, fun a => ?_⟩
  obtain ⟨hS, hub⟩ := (dqSlot hp hX hFw hR hI hB hN c s).full_observes hX
    (b := 0) hu ⟨a.val, a.isLt⟩
  have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.dequantReady s)))
      (.thread (Unit.it X (mbarLoc L c (.dequantReady s)) (deqLane L c) a
        (okPolls (mbarLoc L c (.dequantReady s)) ((X.tr (mmaLane L X c)).take j))))
      (.thread (mmaLane L X c, Poll.nth X (mbarLoc L c (.dequantReady s)) (mmaLane L X c)
        (okPolls (mbarLoc L c (.dequantReady s)) ((X.tr (mmaLane L X c)).take j)))) := hub
  rw [Poll.nth_eq he] at hub'
  exact O.wait_obs hS he hub'

/-- **The reuse paths of `svDone s`** as dequant lane `a` polls it (`KRing.reachE`). -/
theorem svDone_reach (c : Nat) (s : Fin 2) (a : Fin 128) :
    Notify.Reach L kernel Assumptions.all X (mbarLoc L c (.svDone s)) (mmaLane L X c)
      (mbarLoc L c (.svDone s)) 1 (deqLane L c a) :=
  fun _ hx _ hj => (dqSlot hp hX hFw hR hI hB hN c s).reachE hX hx a (by omega) (by omega)

/-- **The free wait observes the commit.** A dequant lane's successful poll of `svDone s` with
`u + 1` earlier ones observes the notification of the MMA lane's commit with `u` earlier commits
to it. -/
theorem svDone_observes {c : Nat} {s : Fin 2} {a : Fin 128} {j pc p u : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (deqLane L c a, j) = some ⟨pc, .wait (mbarLoc L c (.svDone s)) p true acq sc⟩)
    (hq : okPolls (mbarLoc L c (.svDone s)) ((X.tr (deqLane L c a)).take j) = u + 1) :
    ∃ i pc' sp rank, X.get (mmaLane L X c, i) = some ⟨pc', .tc (.commit sp)⟩ ∧
      sp.mbar = mbarLoc L c (.svDone s) ∧
      TcCommit.target sp rank = some (mbarLoc L c (.svDone s)) ∧
      ((X.tr (mmaLane L X c)).take i).countP (commitsTo (mbarLoc L c (.svDone s))) = u ∧
      rank ∈ X.tcNotified (mmaLane L X c, i) ∧
      WaitObserves X (.async (mmaLane L X c, i) (.tcNotify rank)) (deqLane L c a, j)
        (mbarLoc L c (.svDone s)) acq sc :=
  (svDone_obj hp hX hFw hR hI hB (mmaOne hp hX hFw) c s).observes hX
    (svDone_reach hp hX hFw hR hI hB hN c s a) he hq (by have := deqLane_warp hp c a; omega)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
