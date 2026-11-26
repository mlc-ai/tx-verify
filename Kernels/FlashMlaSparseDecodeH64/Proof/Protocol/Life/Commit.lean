-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Obs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Query.Observe
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Score.LagQk
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CommitSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Commit
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Elect
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.QPoll
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.SvCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Dequant.Final
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Wg0Poll
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SvPoll
import Lemmas.Protocol.UnitHandoff

@[expose] public section

/-! # A commit's arrival finishes before its CTA exits

Every commit of the code is the arrive-on, at rank 0, of its CTA's MMA lane (`commit_kind`). The
query copy's and the QK commits' arrivals are observed by a poll of the exited CTA's lanes
(`commit_q_enabled`, `commit_qk_enabled`). The PV commit of the last block is observed by
warpgroup 0's poll at pc 1184 (`commit_pv_last_enabled`); the PV commit of an earlier block is
followed by a later commit of the lane, and the assumption `commitOrder` orders its arrive-on
before the next commit's (`SharedEnabled.of_commit_next`), whose chain is the induction's
hypothesis (a decreasing distance to the end of the lane's trace). -/

/-! # The commits whose arrival a poll observes

* The query copy's commit (pc 1982): the MMA lane's own poll of `qUtccp` at pc 1983, which the
  exited lane made (`mma_qUtPollExit`), observes it (`qUtccp_observes`).
* A QK commit (pc 2105) of use `u` of `qkDone s`: warpgroup 0's lane that exited made all the
  CTA's uses of the slot (`wg0_svPoll`), among them its `u`-th poll, which observes the commit
  (`Notify.Obj.observes`).

Each is enabled (`SharedEnabled`) before an exit of its CTA by the poll's lane. -/

/-! # What a commit of the code is

Every commit of the code is the arrive-on, at rank 0 of its one-CTA cluster, of the CTA's MMA
lane: at pc 1982 on `qUtccp`, at pc 2105 on a slot of `qkDone`, at pc 2148 on a slot of `svDone`
(`commit_kind`). Two events of a lane with one count of a predicate before them are one event
(`idx_eq_of_count`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A commit's only target rank is 0**, and it targets the mbarrier it names. -/
theorem commit_rank (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {y i pc : Nat} {sp : TcCommit.Spec} {rank : Fin 16} {l : Loc}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (ht : TcCommit.target sp rank = some l) :
    rank = 0 ∧ l = sp.mbar ∧ TcCommit.target sp 0 = some sp.mbar := by
  obtain ⟨r, hr⟩ := mma_commitHit hp hX he rfl
  have h1 := mma_commitOne hp hX he
  have hr1 : r.val < 1 := by
    unfold TcCommit.target at hr
    split_ifs at hr with h
    omega
  have hk1 : rank.val < 1 := by
    unfold TcCommit.target at ht
    split_ifs at ht with h
    omega
  obtain rfl : r = 0 := Fin.ext (by omega)
  obtain rfl : rank = 0 := Fin.ext (by omega)
  exact ⟨rfl, Option.some.inj (ht.symm.trans hr), hr⟩

/-- **The kind of a commit**: the commit of an exited-or-not CTA's MMA lane, by its pc. -/
theorem commit_kind (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hMb : MbarRows P L X) {y i pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) :
    y < L.threads ∧ y = mmaLane L X (y / L.block) ∧
      ((pc = 1982 ∧ sp.mbar = mbarLoc L (y / L.block) .qUtccp) ∨
        (pc = 2105 ∧ ∃ s, sp.mbar = mbarLoc L (y / L.block) (.qkDone s)) ∨
        (pc = 2148 ∧ ∃ s, sp.mbar = mbarLoc L (y / L.block) (.svDone s))) := by
  have hw := mma_commit_warp hp hX hFw he
  have hpc := commit_pcs hX he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
  have hat : MmaOn L y pc := ⟨⟨hw, by omega, by omega⟩, by omega⟩
  obtain ⟨r, htg⟩ := mma_commitHit hp hX he rfl
  have hy := Frame.lt_of_get hX he
  refine ⟨hy, laneOn_eq (mmaOne hp hX hFw) he (fun _ h => by cases h) hat, ?_⟩
  cases hMb.mma hy he hat.1 (l := sp.mbar) ⟨r, htg⟩ with
  | qLoad hq => simp only [qLoadPcs, List.mem_cons, List.not_mem_nil, or_false] at hq; omega
  | qArrive hq => simp only at hq; omega
  | qWait hq => simp only at hq; omega
  | qCommit hq hl => exact .inl ⟨hq, hl⟩
  | qCopyWait hq => simp only at hq; omega
  | kvWait hq => simp only at hq; omega
  | qkCommit hq hl => exact .inr (.inl ⟨hq, _, hl⟩)
  | soWait hq => simp only at hq; omega
  | svCommit hq hl => exact .inr (.inr ⟨hq, _, hl⟩)

/-- **Two events of a thread that satisfy a predicate, with one count of it before them, are one
event.** -/
theorem idx_eq_of_count {p : Event → Bool} {y i j : Nat} {e e' : Event}
    (hi : X.get (y, i) = some e) (hj : X.get (y, j) = some e') (hp : p e = true)
    (hp' : p e' = true) (h : ((X.tr y).take i).countP p = ((X.tr y).take j).countP p) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · have e1 := countP_take_succ hi hp
    have e2 := countP_take_mono p (X.tr y) (show i + 1 ≤ j from h1)
    omega
  · exact h1
  · have e1 := countP_take_succ hj hp'
    have e2 := countP_take_mono p (X.tr y) (show j + 1 ≤ i from h1)
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hMb : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
include hp hX hFw hMb hI hB

/-- **The query copy's commit is enabled before an exit of its CTA.** -/
theorem commit_q_enabled {y i : Nat} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨1982, .tc (.commit sp)⟩)
    (hm : sp.mbar = mbarLoc L (y / L.block) .qUtccp) (hy : y < L.threads)
    (hgm : y = mmaLane L X (y / L.block)) (hx : CtaExited L X (y / L.block)) :
    SharedEnabled L kernel Assumptions.all X (y / L.block) (.async (y, i) (.tcNotify 0)) := by
  obtain ⟨pcx, hlast⟩ := hx y hy rfl
  rw [List.getLast?_eq_getElem?] at hlast
  have hxy : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hlast
  have hw4 := mma_commit_warp hp hX hFw he
  have hpoll := mma_qUtPollExit hp hX hFw he (fun _ h => by cases h)
    ⟨by simp only; omega, by simp only; omega⟩ hw4 hxy
  have hEnough : 0 + 1 ≤ okPolls (mbarLoc L (y / L.block) .qUtccp)
      ((X.tr y).take (X.tr y).length) := by
    rw [List.take_length]
    exact hpoll
  obtain ⟨j, pcj, p, acq, sc, -, hget, -⟩ := MbarRing.Poll.exists_nth hEnough
  have hC1 : (X.tr (mmaLane L X (y / L.block))).countP
      (PTX.Flow.commitsTo (mbarLoc L (y / L.block) .qUtccp)) ≤ 1 := by
    rw [← hgm]
    exact mma_commits_le hp hX hFw hw4
  obtain ⟨-, -, i', sp', rank', hget', hmb', htg', hrank', hobs⟩ :=
    qUtccp_observes hp hX hFw hMb hI hB (mmaOne hp hX hFw) hC1 hget
  rw [← hgm] at hget' hobs hC1
  have hpi : PTX.Flow.commitsTo (mbarLoc L (y / L.block) .qUtccp)
      ⟨1982, .tc (.commit sp)⟩ = true := by
    simp [PTX.Flow.commitsTo, hm]
  have hpi' : PTX.Flow.commitsTo (mbarLoc L (y / L.block) .qUtccp)
      ⟨1982, .tc (.commit sp')⟩ = true := by
    simp [PTX.Flow.commitsTo, hmb']
  have h1 := countP_lt_of_get (p := PTX.Flow.commitsTo (mbarLoc L (y / L.block) .qUtccp)) he hpi
  have h2 := countP_lt_of_get (p := PTX.Flow.commitsTo (mbarLoc L (y / L.block) .qUtccp)) hget' hpi'
  simp only at h1 h2
  obtain rfl := idx_eq_of_count hget' he hpi' hpi (by omega)
  obtain ⟨rfl, -⟩ := commit_rank hp hX hget' htg'
  exact observed_enabled hX hobs hx

/-- **A QK commit is enabled before an exit of its CTA**: the poll of warpgroup 0's lane that
exited, with as many earlier polls of the slot as the commit has earlier commits to it. -/
theorem commit_qk_enabled (hBar : BarRows P L X) {y i : Nat}
    {s : Fin 2} {sp : TcCommit.Spec} (he : X.get (y, i) = some ⟨2105, .tc (.commit sp)⟩)
    (hm : sp.mbar = mbarLoc L (y / L.block) (.qkDone s)) (hy : y < L.threads)
    (hgm : y = mmaLane L X (y / L.block)) (hx : CtaExited L X (y / L.block)) :
    SharedEnabled L kernel Assumptions.all X (y / L.block) (.async (y, i) (.tcNotify 0)) := by
  obtain ⟨-, r, hr, hs, hcnt⟩ := mma_qkBlock hp hX hFw he hm
  obtain ⟨Y, jw, p, hYt, hYc, hY4, hpoll⟩ := exit_poll1184 hp hX hFw hBar hy hx
  obtain ⟨-, -, -, -, hall⟩ := wg0_svPoll hp hX hFw hpoll
  have hpol : r / 2 + 1 ≤ okPolls (mbarLoc L (y / L.block) (.qkDone s)) ((X.tr Y).take jw) := by
    rw [hall s, hs]
    simp only [slot2, ringUses]
    omega
  obtain ⟨j, pcj, pp, acq, sc, hjk, hget, hq⟩ := MbarRing.UnitHandoff.exists_poll hpol
  obtain ⟨b', hbq⟩ := wg0_lane hp (g := Y) (pc := 103) ⟨hY4, by omega, by omega⟩
  rw [hYc] at hbq
  have O := qkDone_obj hp hX hFw hMb hI hB (mmaOne hp hX hFw) (y / L.block) s
  rw [hbq] at hget hq
  obtain ⟨ic, pcc, sp', rank', hcom, hmb, htg, hcnt', hrank, hobs⟩ :=
    O.observes hX (u := r / 2) (qkReach hp hX hFw hMb hI hB (y / L.block) s b') hget hq
  rw [← hbq] at hget hobs
  rw [← hgm] at hcom hobs hcnt'
  have hpi : PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone s))
      ⟨2105, .tc (.commit sp)⟩ = true := by
    simp [PTX.Flow.commitsTo, hm]
  have hpi' : PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.qkDone s))
      ⟨pcc, .tc (.commit sp')⟩ = true := by
    simp [PTX.Flow.commitsTo, hmb]
  obtain rfl := idx_eq_of_count hcom he hpi' hpi (by rw [hcnt, hcnt'])
  obtain ⟨rfl, -⟩ := commit_rank hp hX hcom htg
  have hx' : CtaExited L X ((Y, j).1 / L.block) := by
    simp only [hYc]
    exact hx
  simpa only [hYc] using observed_enabled hX hobs hx'

/-- **The last PV commit is enabled before an exit of its CTA**: warpgroup 0's poll of `svDone`
at pc 1184 observes it. -/
theorem commit_pv_last_enabled (hBar : BarRows P L X) (hN : DequantInputs L X)
    {y i pc : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (he : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = mbarLoc L (y / L.block) (.svDone s)) (hy : y < L.threads)
    (hgm : y = mmaLane L X (y / L.block)) (hx : CtaExited L X (y / L.block))
    (hs : s = slot2 (blocksOf P L (y / L.block) - 1))
    (hcnt : ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone s))) =
      (blocksOf P L (y / L.block) - 1) / 2) :
    SharedEnabled L kernel Assumptions.all X (y / L.block) (.async (y, i) (.tcNotify 0)) := by
  obtain ⟨Y, jw, p, hYt, hYc, hY4, hpoll⟩ := exit_poll1184 hp hX hFw hBar hy hx
  obtain ⟨-, ic, pci, spi, rank, hgc, hmi, hti, hci, hrk, hobs⟩ :=
    svDone_last hp hX hFw hMb hI hB hN hY4 hpoll
  rw [← hs] at hmi hti hci hobs
  rw [← hgm] at hgc hobs hci
  have hpi : PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone s))
      ⟨pc, .tc (.commit sp)⟩ = true := by
    simp [PTX.Flow.commitsTo, hm]
  have hpi' : PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone s))
      ⟨pci, .tc (.commit spi)⟩ = true := by
    simp [PTX.Flow.commitsTo, hmi]
  obtain rfl := idx_eq_of_count hgc he hpi' hpi (by rw [hcnt, hci])
  obtain ⟨rfl, -⟩ := commit_rank hp hX hgc hti
  have hx' : CtaExited L X ((Y, jw).1 / L.block) := by
    simp only [hYc]
    exact hx
  simpa only [hYc] using observed_enabled hX hobs hx'

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.AsyncCopy MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hBar : BarRows P L X) (hMb : MbarRows P L X) (hI : InitRows L X)
  (hB : Bar0Rows L X) (hN : DequantInputs L X)
include hp hX hFw hBar hMb hI hB hN

/-- **Every commit's arrive-on is enabled before an exit of its CTA**, once the CTA exited. -/
theorem commit_enabled {y : Nat} (n : Nat) :
    ∀ {i pc : Nat} {sp : TcCommit.Spec}, (X.tr y).length - i = n →
      X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩ → CtaExited L X (y / L.block) →
      SharedEnabled L kernel Assumptions.all X (y / L.block) (.async (y, i) (.tcNotify 0)) := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i pc sp hn he hx
    obtain ⟨hy, hgm, hk⟩ := commit_kind hp hX hFw hMb he
    rcases hk with ⟨rfl, hm⟩ | ⟨rfl, s, hm⟩ | ⟨rfl, s, hm⟩
    · exact commit_q_enabled hp hX hFw hMb hI hB he hm hy hgm hx
    · exact commit_qk_enabled hp hX hFw hMb hI hB hBar he hm hy hgm hx
    obtain ⟨-, r, hr, hs, hall⟩ := mma_svBlock hp hX hFw he hm
    by_cases hlast : r + 1 < blocksOf P L (y / L.block)
    · obtain ⟨pcx, hl⟩ := hx y hy rfl
      rw [List.getLast?_eq_getElem?] at hl
      have hxy : X.get (y, (X.tr y).length - 1) = some ⟨pcx, .exit⟩ := hl
      obtain ⟨j0, pc0, sp0, hij0, hj0⟩ := mma_svNext hp hX hFw he rfl hxy hlast hs hall hm
      have hex : ∃ j, i < j ∧ ∃ pc' sp', X.get (y, j) = some ⟨pc', .tc (.commit sp')⟩ :=
        ⟨j0, hij0, pc0, sp0, hj0⟩
      obtain ⟨hij, pcj, spj, hj⟩ := Nat.find_spec hex
      have hBetween : ∀ k, i < k → k < Nat.find hex → ¬ ∃ s, X.Commit (y, k) s :=
        fun k hik hkj ⟨s', pc', hk'⟩ => Nat.find_min hex hkj ⟨hik, pc', s', hk'⟩
      have hlen : Nat.find hex < (X.tr y).length := (List.getElem?_eq_some_iff.mp hj).1
      have hE := ih ((X.tr y).length - Nat.find hex) (by omega) rfl hj hx
      have hsel : Assumptions.all.any (·.commitInOrder 2148) = true := by
        rw [Assumptions.all_commitInOrder]
        decide
      have hw := hX.asm Assumptions.commitOrder (by simp [Assumptions.all])
      have hPrev := hw y i (Nat.find hex) 2148 sp 0 he (by decide) hij ⟨spj, pcj, hj⟩
        hBetween hE.1
      exact SharedEnabled.of_commit_next (i := (y, i)) (j := (y, Nat.find hex)) (r := 0)
        ⟨rfl, rfl, hij, hPrev, hE.1, ⟨2148, sp, he, hsel⟩, ⟨spj, pcj, hj⟩, hBetween⟩ hE
    · have hrl : r = blocksOf P L (y / L.block) - 1 := by omega
      subst hrl
      refine commit_pv_last_enabled hp hX hFw hMb hI hB hBar hN he hm hy hgm hx hs ?_
      rw [hall s, hs]
      simp only [slot2, ringUses]
      omega

end

/-- **Every commit's arrival finishes before an exit of its CTA**, once the CTA exited. -/
theorem life_commit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hBar : BarRows P L X) (hMb : MbarRows P L X)
    (hI : InitRows L X) (hB : Bar0Rows L X) (hN : DequantInputs L X) :
    CommitFinished L kernel Assumptions.all X := by
  intro i s rank mm hc htg hx
  obtain ⟨y, i0⟩ := i
  obtain ⟨pc, he⟩ := hc
  obtain ⟨rfl, -⟩ := commit_rank hp hX he htg
  exact (commit_enabled hp hX hFw hBar hMb hI hB hN _ rfl he hx).finished

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
