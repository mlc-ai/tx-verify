-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Exit
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Handoffs
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Role
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Tmem
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The S-full and final O commits' arrive-ons end before their CTA's exit

The MMA lane polls the stage's P-full barrier once for each of its S-full commits before its exit,
so a softmax lane of the stage has arrived on it, after its S-full poll of the same ordinal, which
observes the commit's arrive-on (`s_commit_finished`). A correction lane of the CTA polls the
stage's final O barrier before its exit and observes the commit to it (`o_commit_finished`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **An S-full commit's arrive-on ends before its CTA's exit.** -/
theorem s_commit_finished {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {st : Nat} (hst : st < 2)
    (hc : X.Commit i s)
    (ht : TcCommit.target s rank = some (Tm.sFull L (i.1 / L.block) st))
    (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / L.block) := by
  have hb := hp.block
  obtain ⟨g, k⟩ := i
  simp only at ht hx ⊢
  obtain ⟨pc, he⟩ := id hc
  have ht' : TcCommit.target s rank = some (obj L g (80 + 8 * st)) := ht
  obtain ⟨hg, -, hw, hmb, -⟩ := mma_commit_of hp hX hFw he ht'
  obtain ⟨pcx, hxg⟩ := exit_of_exited hx hg rfl
  obtain ⟨hkx, -⟩ := before_exit he (by simp) hxg
  -- the lane polls P-full for the tile before its exit
  have hpolls := Mma.mma_exit_polls hp hX hFw hw hst hxg
  have hcnt : Tm.sCommits L X g st k + 1 ≤ Tm.sCommits L X g st ((X.tr g).length - 1) := by
    have hg' : (X.tr g)[k]? = _ := he
    have h1 : ((X.tr g).take (k + 1)).countP (commitsTo (Tm.sFull L (g / L.block) st)) =
        ((X.tr g).take k).countP (commitsTo (Tm.sFull L (g / L.block) st)) + 1 := by
      rw [List.take_add_one, hg', Option.toList_some, List.countP_append]
      have : commitsTo (Tm.sFull L (g / L.block) st) ⟨pc, .tc (.commit s)⟩ = true := by
        simp only [commitsTo, decide_eq_true_eq]
        exact hmb
      simp [this]
    have h2 := countP_take_mono (commitsTo (Tm.sFull L (g / L.block) st)) (X.tr g)
      (show k + 1 ≤ (X.tr g).length - 1 by omega)
    unfold Tm.sCommits
    omega
  obtain ⟨j, pcj, par, acq, sc, -, hwj, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := Tm.pFull L (g / L.block) st) (h := g) (f := (X.tr g).length - 1)
    (c := Tm.sCommits L X g st k) (hcnt.trans hpolls)
  -- which a softmax lane's arrival, after its S-full poll of the tile, precedes
  obtain ⟨hhl, hhw, hhst, hhc⟩ := Tm.softRow0_spec hp hg hst
  set h := Tm.softRow0 L (g / L.block) st
  obtain ⟨e, hce, hsy⟩ := Tm.pReadyHandoff hp hX hFw (g / L.block) st hst g j pcj par acq sc _
    ⟨hg, rfl, hw⟩ hwj hq h ⟨hhl, hhc, .inl ⟨hhw, hhst⟩⟩
  obtain ⟨rs, ⟨tx, cnt, pce, hev⟩, -⟩ := id hsy
  have hev' : X.get (h, e) = some ⟨pce,
      .arrive (Tm.pFull L (h / L.block) (Prologue.warpIndex L h / 4)) tx cnt true rs⟩ := by
    rw [hhc, hhst]
    exact hev
  have hsp := Softmax.soft_p hp hX hFw hhw hev'
  have hpa : Tm.pArr L X h st e = Tm.sCommits L X g st k := by
    unfold Tm.pArr
    rw [hhc]
    exact hce
  rw [hhst, hpa] at hsp
  obtain ⟨j', pc', par', acq', sc', -, hwj', hq'⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := Tm.sFull L (h / L.block) (Prologue.warpIndex L h / 4)) (h := h) (f := e)
    (c := Tm.sCommits L X g st k) (by rw [hhst]; exact hsp.le)
  -- the poll observes the commit
  obtain ⟨⟨y, k'⟩, s', rank', ws, ⟨pcy, hy⟩, hcy, hb', hcnt', ht2, hr, hobs, -⟩ :=
    Tm.sFullHandoff hp hX hFw hhl hhw hwj'
  simp only at hcy hb' hcnt' hobs
  rw [hhst] at hb' hcnt' ht2 hobs
  have ht3 : TcCommit.target s' rank' = some (obj L g (80 + 8 * st)) := by
    rw [ht2, hhc]
  obtain rfl : g = y := mma_commit_lane hp hX hFw he ht' hy ht3
  have hcnt3 : Tm.sCommits L X g st k' = Tm.sCommits L X g st k := by
    rw [hcnt']
    unfold Tm.sPolls
    rw [← hq', hhst]
  obtain rfl : k = k' := by
    obtain ⟨-, -, -, hmb', -⟩ := mma_commit_of hp hX hFw hy ht3
    refine nthEv_unique (p := commitsTo (Tm.sFull L (g / L.block) st)) he ?_ hy ?_ hcnt3.symm
    · simp only [commitsTo, decide_eq_true_eq]; exact hmb
    · simp only [commitsTo, decide_eq_true_eq]; exact hmb'
  rw [he] at hy
  cases hy
  obtain rfl : rank = rank' := target_rank ht' ht3
  exact of_observed hX hr hhl hhc hwj' (by rw [hhst]; exact hobs) hx

/-- **A final O commit's arrive-on ends before its CTA's exit.** -/
theorem o_commit_finished {i : EvId} {s : TcCommit.Spec} {rank : Fin 16} {st : Nat} (hst : st < 2)
    (hc : X.Commit i s)
    (ht : TcCommit.target s rank = some (Tm.oFull L (i.1 / L.block) st))
    (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / L.block) := by
  have hb := hp.block
  obtain ⟨g, k⟩ := i
  simp only at ht hx ⊢
  obtain ⟨pc, he⟩ := id hc
  have ht' : TcCommit.target s rank = some (obj L g (144 + 8 * st)) := ht
  obtain ⟨hg, -, hw, hmb, -⟩ := mma_commit_of hp hX hFw he ht'
  obtain ⟨h0, R, hR, -⟩ := mma_o_commit hp hX hFw ⟨st, hst⟩ hw he hmb
  -- the CTA's first correction lane
  have hh : g / L.block * L.block + 256 < L.threads := by
    unfold Launch.threads at hg ⊢
    rw [hb] at hg ⊢
    omega
  have hhc : (g / L.block * L.block + 256) / L.block = g / L.block := by rw [hb]; omega
  have hhw : Prologue.warpIndex L (g / L.block * L.block + 256) = 8 := by
    unfold Prologue.warpIndex
    rw [hb]
    omega
  set h := g / L.block * L.block + 256
  obtain ⟨pch, hxh⟩ := exit_of_exited hx hh hhc
  obtain ⟨r, bal, hP, -⟩ := MmaRounds.cta hhc.symm hR
  have hpoll := Correction.corr_exit_poll hp hX hFw (by omega) (by omega) ⟨st, hst⟩ hxh
    ⟨r, bal, hP⟩
  obtain ⟨j, pcj, par, acq, sc, hjx, hwj, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (m := Tm.oFull L (h / L.block) st) (h := h) (f := (X.tr h).length - 1) (c := 0) hpoll.ge
  obtain ⟨⟨y, k'⟩, s', rank', ws, ⟨pcy, hy⟩, hcy, hb', hcnt', ht2, hr, hobs, -⟩ :=
    Tm.oFullHandoff hp hX hFw hh (by omega) (by omega) hst hwj
  simp only at hcy hb' hcnt' hobs
  have ht3 : TcCommit.target s' rank' = some (obj L g (144 + 8 * st)) := by
    rw [ht2, hhc]
  obtain rfl : g = y := mma_commit_lane hp hX hFw he ht' hy ht3
  obtain rfl : k = k' := by
    obtain ⟨-, -, -, hmb', -⟩ := mma_commit_of hp hX hFw hy ht3
    refine nthEv_unique (p := commitsTo (Tm.oFull L (g / L.block) st)) he ?_ hy ?_ ?_
    · simp only [commitsTo, decide_eq_true_eq]; exact hmb
    · simp only [commitsTo, decide_eq_true_eq]; exact hmb'
    · exact h0.trans (hcnt'.trans hq).symm
  rw [he] at hy
  cases hy
  obtain rfl : rank = rank' := target_rank ht' ht3
  exact of_observed hX hr hh hhc hwj hobs hx

/-- **A commit's arrive-on ends before its CTA's exit**, given the empty barriers'. -/
theorem commit_finished (hempty : EmptiesFinished L kernel Assumptions.all X) {i : EvId}
    {s : TcCommit.Spec} {rank : Fin 16} {l : Loc} (hc : X.Commit i s)
    (ht : TcCommit.target s rank = some l) (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i (.tcNotify rank)) (i.1 / L.block) := by
  by_cases h : ∃ st < 2, l = Tm.sFull L (i.1 / L.block) st ∨ l = Tm.oFull L (i.1 / L.block) st
  · obtain ⟨st, hst, rfl | rfl⟩ := h
    · exact s_commit_finished hp hX hFw hst hc ht hx
    · exact o_commit_finished hp hX hFw hst hc ht hx
  · push Not at h
    exact hempty i s rank l hc ht (fun st hst => h st hst) hx

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life
