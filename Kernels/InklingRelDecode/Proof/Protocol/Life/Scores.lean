-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Commit
public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarReach
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.ScoreCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Count
import Kernels.InklingRelDecode.Proof.Mma.Export.Election
import Kernels.InklingRelDecode.Proof.Softmax.Export.ExitPolls
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # A score commit of an exited CTA is observed

The commit (pc 2499) is the elected lane's, to score slot `s` with `u` earlier commits to it.
Lane zero of the CTA exited, so it polled every block's score slot (`Softmax.Export.exited_polls`):
it made a poll with `u` earlier polls of the slot, which observes the commit with `u` earlier
commits (`Notify.Obj.observes`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Every score commit of an exited CTA is observed** by a score poll of its lane zero. -/
theorem score_observed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (zero : ∀ c, NoUbLane X (c * L.block)) : ScoreObserved L X := by
  intro g k sp rank l he ht hx
  have hg := Frame.lt_of_get hX he
  have warp := Mma.Export.commit_warp hp hX hf he
  obtain ⟨c, hcg⟩ : ∃ c, g / L.block = c := ⟨_, rfl⟩
  have hc : c < L.grid :=
    hcg ▸ Nat.div_lt_of_lt_mul (by simpa [Launch.threads, Nat.mul_comm] using hg)
  have hz : c * L.block < L.threads := by
    simp only [Launch.threads, hp.block] at *; omega
  have hzc : c * L.block / L.block = c := Nat.mul_div_cancel _ (by rw [hp.block]; omega)
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  obtain ⟨ev, mem, won⟩ := Mma.Export.elected hp hX hf he (fun _ => nofun)
    (by change 2499 ∈ _; decide)
  have lead := KV.leader_eq hX hg ⟨ev, (List.take_sublist k _).subset mem, won⟩
  rw [warp, hcg] at lead
  obtain ⟨pos, le, pv⟩ := Mma.Export.score_polls hp hX hf warp he
  obtain ⟨off, rfl, site⟩ := Mma.Export.commit hp hX hf warp he
  rw [hcg] at he ht le
  obtain ⟨-, hoff⟩ : 2499 = 2499 ∧ off =
      Iface.sReady ⟨(pollRound 2462 ((X.tr g).take k) - 1) % 2, by omega⟩ := by
    rcases site with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    all_goals omega
  generalize hs : (⟨(pollRound 2462 ((X.tr g).take k) - 1) % 2, by omega⟩ : Fin 2) = s at hoff
  have obj : (⟨.one, ⟨.shared, c, L.sharedBase + off⟩, 1, c, 1⟩ : TcCommit.Spec).mbar =
      (Scalar.Object.score s).loc L c := by rw [hoff]; rfl
  have ht' := ht
  simp only [TcCommit.target, Option.ite_none_right_eq_some, Option.some.injEq] at ht'
  obtain ⟨h1, h2⟩ := ht'
  have hr : rank.val = 0 := by omega
  rw [hr, Nat.add_zero] at h2
  subst h2
  have u_le := Scalar.score_commits (s := s) hp hX hf rows words hg warp hcg he obj
  have prob := Scalar.count rows hg (Scalar.Object.prob s) k
  simp only [MbarRow.roundAt, Scalar.Object.pc, hcg, pv] at prob
  rw [hcg] at hx
  obtain ⟨pcx, hl⟩ := hx _ hz hzc
  rw [List.getLast?_eq_getElem?] at hl
  have polls := Softmax.Export.exited_polls hp hX hf (zero c) hz (by simp [hp.block])
    (show X.get (c * L.block, (X.tr (c * L.block)).length - 1) = _ from hl)
  rw [hzc] at polls
  have whole : pollRound 1257 ((X.tr (c * L.block)).take ((X.tr (c * L.block)).length - 1)) ≤
      pollRound 1257 (X.tr (c * L.block)) := (List.take_sublist _ _).countP_le
  have total := Scalar.count rows hz (Scalar.Object.score s) (X.tr (c * L.block)).length
  simp only [MbarRow.roundAt, Scalar.Object.pc, hzc, List.take_length] at total
  have lt : ((X.tr g).take k).countP (commitsTo ((Scalar.Object.score s).loc L c)) <
      okPolls ((Scalar.Object.score s).loc L c) (X.tr (c * L.block)) := by
    rw [total]
    have : s.val = (pollRound 2462 ((X.tr g).take k) - 1) % 2 := by rw [← hs]
    simp only [Scalar.Object.visits, Scalar.Object.width, Scalar.Object.index] at *
    omega
  have O := Scalar.notification hp hX hf rows init (c := c) (.inl ⟨s, rfl⟩)
  have R := Reach.notify_reach hX O fun n hn =>
    (Scalar.goals_all hp hX hf rows init words c hc n hn).2.1 s
  obtain ⟨pcw, p, acq, sc, get, cnt⟩ := MbarRing.Poll.nth_spec (X := X)
    (m := (Scalar.Object.score s).loc L c) (g := c * L.block) lt
  obtain ⟨i, pc', sp', rank', hget, hm', ht', hcnt, hrk, hobs⟩ := O.observes hX R get
    (by simpa using cnt)
  rw [lead] at hget hcnt hobs
  have hk : i = k := by
    have a := KV.position_at hget (f := commitsTo ((Scalar.Object.score s).loc L c))
      (by simp [commitsTo, hm'])
    have b := KV.position_at he (f := commitsTo ((Scalar.Object.score s).loc L c))
      (by simpa [commitsTo] using obj)
    rw [hcnt] at a
    exact a.symm.trans b
  subst hk
  have hsp := TcKind.commit.inj (Kind.tc.inj (congrArg Event.kind (Option.some.inj
    (he.symm.trans hget))))
  subst hsp
  have hl : (Scalar.Object.score s).loc L c = ⟨.shared, c, L.sharedBase + off⟩ := by
    rw [hoff]; rfl
  rw [hl] at ht' hobs
  obtain rfl : rank' = rank := Notify.rank_eq ht' ht
  exact ⟨c * L.block, _, acq, sc, hzc.trans hcg.symm, hobs⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
