-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Lag
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Obs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.LagReady
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Obj
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.GatherLt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Lemmas.Protocol.ClusterTrace
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.PollIndex

@[expose] public section

/-! # A tensor load's arrival finishes before its CTA exits

A tensor load is a TMA gather (`life_gather`) or a query load of the MMA lane (`life_query`), by
the load's place (`tensor_place`). -/

/-! # A query load's arrival finishes before its CTA exits

The MMA lane that issued the loads exited, so it made its poll of `qTma` (pc 1931,
`mma_qPollExit`), which observes the arrival and each of its eight loads (`qTma_observes`); the
poll is a canonical spin that resumes the lane's exit (`observed_finished`). -/

/-! # A gather's arrival finishes before its CTA exits

Gather `q` of use `u` of raw tile `s` is observed by the dequant lanes' poll of `rawReady s` with
`u` earlier ones (`rawReady_observes`). Dequant lane 0 of the CTA exits, having polled `rawReady s`
once per use of the slot (`deq_rawReady_polls`), and the gather's use is below the CTA's uses
(`tma_gather_lt`), so the lane made that poll; it is a canonical spin that resumes the lane's exit
(`observed_finished`). -/

/-! # An exited dequant lane has polled every use of `rawReady`

A dequant lane that exited made all its arrivals on `rawFree s` (`deq_rfExit`), and each follows
more successful polls of `rawReady s` than its earlier arrivals (`dequant_freeArr`): so its last
arrival, the one of the CTA's last use of the slot, follows as many polls as there are uses. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An exited dequant lane polled `rawReady s` once per use of the slot.** -/
theorem deq_rawReady_polls (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c k pc : Nat} {b : Fin 128} {s : Fin 2}
    (hx : X.get (deqLane L c b, k) = some ⟨pc, .exit⟩) :
    ringUses 2 s.val (blocksOf P L c) ≤
      okPolls (mbarLoc L c (.rawReady s)) (X.tr (deqLane L c b)) := by
  have hw : 8 ≤ warp L (deqLane L c b) ∧ warp L (deqLane L c b) < 12 := by
    have hb := b.isLt
    simp only [warp, deqLane, tidOf_x_eq hp, hp.block]
    omega
  have hc := deqLane_cta hp c b
  have htot := deq_rfExit hp hX hFw hw hc hx (j := s)
  have htot' : ringUses 2 s.val (blocksOf P L c) ≤
      (X.tr (deqLane L c b)).countP (arrivesOn (mbarLoc L c (.rawFree s))) := htot
  rcases Nat.eq_zero_or_pos (ringUses 2 s.val (blocksOf P L c)) with h0 | hpos
  · omega
  obtain ⟨t, e, het, hpe, hcnt⟩ := MbarRing.Slot.exists_nth_countP
    (arrivesOn (mbarLoc L c (.rawFree s))) (xs := X.tr (deqLane L c b))
    (c := ringUses 2 s.val (blocksOf P L c) - 1) (by omega)
  obtain ⟨pce, kd⟩ := e
  cases kd <;> simp only [arrivesOn, sourceArrive, Bool.false_eq_true] at hpe
  rename_i l' tx cnt rel sc
  simp only [decide_eq_true_eq] at hpe
  subst hpe
  have hlt := dequant_freeArr hp hX hFw hw (g := deqLane L c b) (i := t) het
  have hmono : okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take t) ≤
      okPolls (mbarLoc L c (.rawReady s)) (X.tr (deqLane L c b)) :=
    (List.take_sublist t _).countP_le
  have hc' : arrivals (mbarLoc L c (.rawFree s)) ((X.tr (deqLane L c b)).take t) =
      ringUses 2 s.val (blocksOf P L c) - 1 := hcnt
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hp hX hFw hR hI hB hN

/-- **A TMA gather's arrival finishes before an exit of its CTA**, once the CTA exited. -/
theorem life_gather {g k pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a s⟩) (hat : TmaAt L g pc)
    (hx : CtaExited L X (g / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async (g, k) (.notify .load)) (g / L.block) := by
  obtain ⟨-, b, q, hq, u, hmb, -, -, -, hcnt, -⟩ := tma_gatherUse hp hX hFw he hat rfl
  have hlt := tma_gather_lt hp hX hFw he hat rfl hmb
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hb0 : 0 < L.block := by rw [hp.block]; decide
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb0).2 hg
  have hh : deqLane L (g / L.block) 0 < L.threads := by
    have := Nat.mul_le_mul_right L.block (show g / L.block + 1 ≤ L.grid by omega)
    simp only [deqLane, Launch.threads, hp.block] at this ⊢
    omega
  have hcc := deqLane_cta hp (g / L.block) 0
  obtain ⟨pcx, hlast⟩ := hx _ hh hcc
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (deqLane L (g / L.block) 0, (X.tr (deqLane L (g / L.block) 0)).length - 1) =
      some ⟨pcx, .exit⟩ := hlast
  have hpolls := deq_rawReady_polls hp hX hFw (s := b) hxy
  have hu : u < ringUses 2 b.val (blocksOf P L (g / L.block)) := by omega
  have hEnough : u + 1 ≤ okPolls (mbarLoc L (g / L.block) (.rawReady b))
      ((X.tr (deqLane L (g / L.block) 0)).take (X.tr (deqLane L (g / L.block) 0)).length) := by
    rw [List.take_length]
    omega
  obtain ⟨j, pcj, p, acq, sc, -, hget, hcntj⟩ := MbarRing.Poll.exists_nth hEnough
  obtain ⟨-, -, hloads⟩ := rawReady_observes hp hX hFw hR hI hB hN hget
  obtain ⟨i', pc', al, sp, hget', hsp, -, hcnt', hobs⟩ := hloads ⟨q, hq⟩
  have hqv : ((⟨q, hq⟩ : Fin 16) : Nat) = q := rfl
  rw [hcntj] at hcnt'
  have hgT : g = tmaThread L X (g / L.block) :=
    rawReady_lane hX hR hN hg he hmb (fun _ _ _ _ h => by cases h) (fun _ h => by cases h)
  have hpred : issuesTo (mbarLoc L (g / L.block) (.rawReady b)) ⟨pc, .tensorIssue a s⟩ = true := by
    simp [issuesTo, hmb]
  have hpred' : issuesTo (mbarLoc L (g / L.block) (.rawReady b)) ⟨pc', .tensorIssue al sp⟩ =
      true := by simp [issuesTo, hsp]
  rw [← hgT] at hget' hobs hcnt'
  have hki : i' = k := by
    rcases Nat.lt_trichotomy i' k with h1 | h1 | h1
    · have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := issuesTo
        (mbarLoc L (g / L.block) (.rawReady b))) h1 hget' hpred'
      omega
    · exact h1
    · have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := issuesTo
        (mbarLoc L (g / L.block) (.rawReady b))) h1 he hpred
      omega
  subst hki
  have hx' : CtaExited L X ((deqLane L (g / L.block) 0, j).1 / L.block) := by
    simp only [hcc]
    exact hx
  have hfin := observed_finished hX hobs hx'
  simp only [hcc] at hfin
  exact hfin

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A query load's arrival finishes before an exit of its CTA**, once the CTA exited. -/
theorem life_query (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) :
    QueryNotified L kernel Assumptions.all X := by
  intro g k pc a s he hat hx
  have hw : warp L g = 4 := hat.1
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨hpc, hmb, q, hq, hcnt, -⟩ := mma_qLoad_range hp hX hFw hw he
  have hcnt2 : ((X.tr g).take k).countP (issuesTo (mbarLoc L (g / L.block) .qTma)) = q := hcnt
  have hgm : g = mmaLane L X (g / L.block) :=
    laneOn_eq (mmaOne hp hX hFw) he (fun _ h => by cases h) ⟨hat, hpc⟩
  obtain ⟨pcx, hlast⟩ := hx g hg rfl
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (g, (X.tr g).length - 1) = some ⟨pcx, .exit⟩ := hlast
  have hpoll := mma_qPollExit hp hX hFw he (fun _ h => by cases h) ⟨hpc, hat.2.2⟩ hw hxy
  have hEnough : 0 + 1 ≤ okPolls (mbarLoc L (g / L.block) .qTma)
      ((X.tr g).take (X.tr g).length) := by
    rw [List.take_length]
    exact hpoll
  obtain ⟨j, pcj, p, acq, sc, -, hget, -⟩ := MbarRing.Poll.exists_nth hEnough
  have hN : (X.tr (mmaLane L X (g / L.block))).countP (issuesTo (mbarLoc L (g / L.block) .qTma)) ≤
      8 := by
    rw [← hgm]
    exact mma_issues_le hp hX hFw hw
  have hA : arrivals (mbarLoc L (g / L.block) .qTma) (X.tr (mmaLane L X (g / L.block))) ≤ 1 := by
    rw [← hgm]
    exact mma_arrivals_le hp hX hFw hw _
  obtain ⟨-, -, -, hloads⟩ := qTma_observes hp hX hFw hR hI hB (mmaOne hp hX hFw) hN hA hget
  obtain ⟨i', pc', al, sp, hget', hsp, hcnt', hobs⟩ := hloads ⟨q, by omega⟩
  rw [← hgm] at hget' hobs hcnt'
  have hqv : ((⟨q, by omega⟩ : Fin 8) : Nat) = q := rfl
  have hpred : issuesTo (mbarLoc L (g / L.block) .qTma) ⟨pc, .tensorIssue a s⟩ = true := by
    simp [issuesTo, hmb]
  have hpred' : issuesTo (mbarLoc L (g / L.block) .qTma) ⟨pc', .tensorIssue al sp⟩ = true := by
    simp [issuesTo, hsp]
  have hki : i' = k := by
    rcases Nat.lt_trichotomy i' k with h1 | h1 | h1
    · have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := issuesTo
        (mbarLoc L (g / L.block) .qTma)) h1 hget' hpred'
      omega
    · exact h1
    · have := ClusterTrace.countP_take_lt (xs := X.tr g) (p := issuesTo
        (mbarLoc L (g / L.block) .qTma)) h1 he hpred
      omega
  subst hki
  exact observed_finished hX hobs hx

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every tensor load's arrival finishes before an exit of its CTA**, once the CTA exited. -/
theorem life_loads (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hN : RawInputs L X) :
    LoadNotified L kernel Assumptions.all X := by
  intro i a s hi hx
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inl ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · simp only [Wg0At] at h; omega
  · simp only [Wg1At] at h; omega
  · exact life_query hp hX hFw hR hI hB g k pc a s he h hx
  · exact life_gather hp hX hFw hR hI hB hN he h hx
  · simp only [IndexAt] at h; omega
  · simp only [DequantAt] at h; omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
