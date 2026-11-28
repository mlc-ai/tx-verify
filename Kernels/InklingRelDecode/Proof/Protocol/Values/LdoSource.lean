-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvSource
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdCand
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.LdOrderO
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarLane
import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Mma.Export.DoneCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Cover
import Kernels.InklingRelDecode.Proof.Lib.IssueCount
import Kernels.InklingRelDecode.Proof.Common.Export.TcOperand
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl

@[expose] public section

/-! # The PV step an accumulator load reads

The accumulator load of round `r` polls the done slot with `r - 1` earlier polls, so it observes the
`r`-th done commit of the MMA lane, whose ordinal is at least `r` (the earlier commits have distinct
smaller ordinals); the last PV step of that ordinal is before the commit. A PV step of an ordinal
above `r` follows the load, so the ordinal is `r`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.MbarRing PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem Protocol.Scalar

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The `u`-th done commit of a lane has a PV ordinal above `u`.** -/
theorem done_ordinal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (words : RoleBytes L X) {c g ic : Nat} {sp}
    (hy : g < L.threads) (warp : g % L.block / 32 = 7)
    (he : X.get (g, ic) = some ⟨2548, .tc (.commit sp)⟩) :
    ((X.tr g).take ic).countP (commitsTo (Object.done.loc L c)) + 1 ≤
      pollRound 2510 ((X.tr g).take ic) := by
  have pos := (Mma.Export.done_shuffles hp hX hf warp he).1
  have := Lib.count_le_tags (es := (X.tr g).take ic) (p := commitsTo (Object.done.loc L c))
    (n := pollRound 2510 ((X.tr g).take ic) - 1)
    (fun j => pollRound 2510 (((X.tr g).take ic).take j) - 1) ?_ ?_
  · omega
  · intro j e atJ kind
    obtain ⟨ji, atJ'⟩ := take_event atJ
    obtain ⟨sp', get⟩ := Protocol.P.done_receipt hp hX hf rows hy atJ' kind
    obtain ⟨pos', -⟩ := Mma.Export.done_shuffles hp hX hf warp get
    have mono : pollRound 2510 ((X.tr g).take j) ≤ pollRound 2510 ((X.tr g).take ic) :=
      (List.take_sublist_take_left ji.le).countP_le (p := okPollAt 2510)
    have ne : pollRound 2510 ((X.tr g).take j) ≠ pollRound 2510 ((X.tr g).take ic) := fun h => by
      have := Mma.Export.done_unique hp hX hf words warp get he h
      omega
    rw [List.take_take, Nat.min_eq_left ji.le]
    omega
  · intro j j' e f ekh ek ejh ej eq
    obtain ⟨ji, ek'⟩ := take_event ekh
    obtain ⟨ji', ej'⟩ := take_event ejh
    obtain ⟨sp1, get1⟩ := Protocol.P.done_receipt hp hX hf rows hy ek' ek
    obtain ⟨sp2, get2⟩ := Protocol.P.done_receipt hp hX hf rows hy ej' ej
    obtain ⟨p1, -⟩ := Mma.Export.done_shuffles hp hX hf warp get1
    obtain ⟨p2, -⟩ := Mma.Export.done_shuffles hp hX hf warp get2
    rw [List.take_take, List.take_take, Nat.min_eq_left ji.le, Nat.min_eq_left ji'.le] at eq
    exact Mma.Export.done_unique hp hX hf words warp get1 get2 (by omega)

/-- **An accumulator load of round `r` has the last PV step of ordinal `r` written before it.** -/
theorem ld_o_pv7 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) {t k0 a vals sh r}
    (he : X.get (t, k0) = some ⟨2260, .tc (.ld a vals sh)⟩)
    (s1 : pollRound 1257 ((X.tr t).take k0) = r + 1) :
    ∃ g kR, g / L.block = t / L.block ∧ PvAt X g kR 7 ∧
      pollRound 2510 ((X.tr g).take kR) = r ∧ WriteBefore L X (g, kR) (t, k0) := by
  have words : RoleBytes L X := fun h => Protocol.Shared.role_bytes hp hX h
  have ht := Frame.lt_of_get hX he
  obtain ⟨r0, -, s1', s2, -, -, rpos⟩ := Proof.Export.ld_round hp hX hf base he rfl (.inr rfl)
  have hr0 : r0 = r := by omega
  subst hr0
  have r1 := rpos rfl
  simp at s2
  have lt := Proof.Export.tc_data_lane hp hX hf he rfl
  have hbl : 0 < L.block := by rw [hp.block]; decide
  have hc : t / L.block < L.grid := (Nat.div_lt_iff_lt_mul hbl).2 ht
  have lpos := Protocol.Scalar.count rows ht Object.done k0
  change okPolls (Object.done.loc L (t / L.block)) ((X.tr t).take k0) =
    Object.done.visits (pollRound 2239 ((X.tr t).take k0)) at lpos
  rw [s2] at lpos
  have vis : Object.done.visits r0 = (r0 + 1 - 1 - 0) / 1 := rfl
  obtain ⟨jp, pcj, pj, acq, scj, hjk, hwj, hq⟩ := UnitHandoff.exists_poll
    (m := Object.done.loc L (t / L.block)) (h := t) (f := k0) (c := r0 - 1)
    (by rw [lpos, vis]; omega)
  obtain ⟨hy, cy, wy⟩ := Protocol.KV.leader_warp (X := X) hp hc (by decide : 7 < 8)
  have O := notification hp hX hf rows init (c := t / L.block) (.inr rfl)
  obtain ⟨ic, pc', sp, rank, hget, hm, -, hcnt, -, -⟩ := O.observes hX
    (lane_reach hp hX hf safe rows init words hc lt rfl (.inr rfl)) hwj hq
  obtain ⟨sp', get2⟩ := Protocol.P.done_receipt (c := t / L.block) hp hX hf rows hy hget
    (by simp [commitsTo, hm])
  have ordl := done_ordinal hp hX hf rows words (c := t / L.block) hy wy get2
  obtain ⟨kR, ltk, d', s', a', m', gw, q⟩ := Mma.Export.done_history hp hX hf words hu get2
  have lent : k0 < (X.tr t).length := (List.getElem?_eq_some_iff.mp he).1
  have hcnt' : ((X.tr (Protocol.KV.leader L X (t / L.block) 7)).take ic).countP
      (commitsTo (Object.done.loc L (t / L.block))) = r0 - 1 := hcnt
  simp only at ordl q
  have mono := countP_take_mono (commitsTo (Object.done.loc L (t / L.block)))
    (X.tr (Protocol.KV.leader L X (t / L.block) 7)) ltk.le
  have wb : WriteBefore L X (Protocol.KV.leader L X (t / L.block) 7, kR) (t, k0) :=
    .of_done (mma_done_lane hp hX hf safe rows init words hc (o := Object.done) (Or.inr rfl) lt
      rfl hwj hq gw rfl (mono.trans hcnt.le)
      (.single (.inl (po_of_source_not_access rfl hjk lent (by rw [hwj]; rfl)))))
  have ord : pollRound 2510 ((X.tr (Protocol.KV.leader L X (t / L.block) 7)).take kR) = r0 := by
    have hge : r0 ≤ pollRound 2510 ((X.tr (Protocol.KV.leader L X (t / L.block) 7)).take ic) := by
      omega
    by_contra hne
    have big : r0 < pollRound 2510 ((X.tr (Protocol.KV.leader L X (t / L.block) 7)).take kR) := by
      omega
    have rb := ld_pv_big hp hX hf safe base rows init he s1 gw cy.symm rfl big
    have ne : (Protocol.KV.leader L X (t / L.block) 7, kR) ≠ (t, k0) := fun h => by
      rw [h, he] at gw
      simp at gw
    exact tcStep_acyclic hX hG _ ((ReadBefore.tcStep rb ne).trans wb.tcStep)
  exact ⟨_, kR, by rw [cy], ⟨d', s', a', m', gw⟩, ord, wb⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
