-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QkIssueHistory
import Lemmas.Order.OrderWaits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity

@[expose] public section

/-! # Actual QK completion before the Tensor Memory score loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback

open PTX AsyncCopy PTX.Flow PTX.MbarRing GemmRing MachineTracking

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A counted QK acquire observes the commit of its slot use. -/
theorem commit_of_counted_qk_wait
    {cta issuer w tag parity block : Nat} {lane : Fin 128} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hw : X.get (softmax L cta lane, w) = some
      ⟨tag, .wait (qk L cta (rawSlot block)) parity true true scope⟩)
    (hwcount : okPolls (qk L cta (rawSlot block)) ((X.tr (softmax L cta lane)).take w) =
      block / 2) :
    ∃ j commitTag sp rank q,
      X.get (issuer, j) = some ⟨commitTag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (qk L cta (rawSlot block)) ∧
      Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)) ∧
      ctaOf L issuer = cta ∧ q.site = .qkCommit ∧ q.i = block ∧
      Witness L X (.async (issuer, j) (.tcNotify rank)) (softmax L cta lane, w) := by
  let h := softmax L cta lane
  let slot := rawSlot block
  let u := block / 2
  change okPolls (qk L cta slot) ((X.tr h).take w) = u at hwcount
  have hnth : Poll.nth X (qk L cta slot) h u = w := by rw [← hwcount, Poll.nth_eq hw]
  obtain ⟨actual, hIssuer, hWarp⟩ := exists_issuer_in_warp (cta := cta) hpre hX hs
  let R := actualScoreRing (slot := slot) hpre hX hs hIssuer hWarp
  have hp : X.RefPresent (.thread (R.wF lane u)) := by
    change X.RefPresent (.thread (h, Poll.nth X (qk L cta slot) h u))
    rw [hnth]
    exact ⟨_, hw⟩
  obtain ⟨hcounted, hwitness⟩ := R.observes_full hX.depAcyclic hp 0
  let F := actual_qk_obj_of_parity (slot := slot) hpre hX hs hIssuer
    (selected := fun _ => True) (fun _ h => actual_qk_alternates hpre hX hs h)
  obtain ⟨_, src, sp, hc, _, htarget, hordinal⟩ := F.S_rec hcounted
  let j := Notify.cm X actual (qk L cta slot) u
  let rank := Notify.rank X (qk L cta slot) actual (qk L cta slot) u
  have hi := Frame.lt_of_get hX hc
  obtain ⟨_, hcCta, q, hslot, hkind, hq⟩ :=
    actual_notification hpre hX hs hc rfl htarget
  have hqKind : q.site = .qkCommit := by
    rcases hkind with ⟨_, hk⟩ | ⟨hk, _⟩
    · exact hk
    · cases hk
  have hcnt := Wg1MmaGemmTrace.composed_count_here hpre hi .qk
    ((hs actual hi).machine.produces (hX.thr actual hi)) hq hslot
  simp only [hqKind, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at hcnt
  change ((X.tr actual).take j).countP (commitsTo (qk L (ctaOf L actual) slot)) = _ at hcnt
  rw [hcCta] at hcnt
  change ((X.tr actual).take j).countP (commitsTo (qk L cta slot)) = u at hordinal
  change q.i % 2 = block % 2 at hslot
  have hb : q.i = block := by dsimp [u] at hordinal; omega
  change Witness L X (.async (actual, j) (.tcNotify rank))
    (h, Poll.nth X (qk L cta slot) h u) at hwitness
  rw [hnth] at hwitness
  have hId := hmma actual j q hcCta hq (by rw [hqKind]; decide)
  subst issuer
  exact ⟨j, src, sp, rank, q, hc, htarget, hq, hcCta, hqKind, hb, hwitness⟩

/-- A successful QK poll at the actual role state observes the actual commit of that block. -/
theorem commit_of_qk_wait
    {cta issuer w tag parity : Nat} {lane : Fin 128} {d : Wg0.D} {scope : MbarScope}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (softmax L cta lane) w = some (some (.wg0 d)))
    (hsite : d.site = .qkDone)
    (hw : X.get (softmax L cta lane, w) = some
      ⟨tag, .wait (qk L cta (rawSlot d.block)) parity true true scope⟩) :
    ∃ j commitTag sp rank q,
      X.get (issuer, j) = some ⟨commitTag, .tc (.commit sp)⟩ ∧
      TcCommit.target sp rank = some (qk L cta (rawSlot d.block)) ∧
      Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)) ∧
      ctaOf L issuer = cta ∧ q.site = .qkCommit ∧ q.i = d.block ∧
      Witness L X (.async (issuer, j) (.tcNotify rank)) (softmax L cta lane, w) := by
  let h := softmax L cta lane
  let slot := rawSlot d.block
  let u := d.block / 2
  have hCta : ctaOf L h = cta := by
    have := lane.isLt
    simp only [h, softmax, ctaOf, hpre.block]
    omega
  have hg := Frame.lt_of_get hX hw
  have hwcount := Wg0GemmTrace.composed_qk_counts hpre
    ((hs h hg).machine.produces (hX.thr h hg)) hd hsite
  rw [hCta] at hwcount
  change okPolls (qk L cta slot) ((X.tr h).take w) = u at hwcount
  exact commit_of_counted_qk_wait hpre hX hs hmma hw hwcount

/-- The actual successful query-key acquire before a score load establishes completion of
each of that generation's actual QK issues before the load, including the last issue. -/
theorem qk_issue_before_score
    {cta issuer w j tag parity address : Nat} {lane : Fin 128} {d : Wg0.D} {scope : MbarScope}
    {words : List Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (softmax L cta lane) w = some (some (.wg0 d)))
    (hsite : d.site = .qkDone)
    (hw : X.get (softmax L cta lane, w) = some
      ⟨tag, .wait (qk L cta (rawSlot d.block)) parity true true scope⟩)
    (hbefore : w < j) (hload : X.TLd (softmax L cta lane, j) address words .s32x32b)
    (k : Fin 16) :
    ∃ i, Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma ⟨.qkMma k, d.block⟩)) ∧
      X.MmaIssue (issuer, i) Wg1Mma.tmemP (MmaDataTrace.qkOperands L issuer d.block k)
        (MmaDataTrace.qkAccum k) [0, 0, 0, 0] ∧
      TcMma.DoneBefore L X (issuer, i) (softmax L cta lane, j) := by
  let g := softmax L cta lane
  obtain ⟨c, ct, sp, rank, q, hc, htarget, hq, hCta, hqsite, hblock, hobs⟩ :=
    commit_of_qk_wait hpre hX hs hmma hd hsite hw
  obtain ⟨i, hi, hist, hissue⟩ := QkIssueHistory.qk_issue_of_commit hpre hX hs hc hq hqsite k
  rw [hblock] at hist hissue
  have hk := k.isLt
  have htrack : TracksMma X (issuer, i) (issuer, c) :=
    ⟨rfl, by omega, .inl ⟨_, _, _, _, hissue⟩, sp, ct, hc⟩
  obtain ⟨hnotify, hobserve⟩ := hobs.waitObserves_tcNotify hw
  have hI := Frame.lt_of_get hX hc
  have hG := Frame.lt_of_get hX hw
  have hGcta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, softmax, ctaOf, hpre.block]
    omega
  have hCluster : SameCluster L issuer g :=
    ⟨hI, hG, congrArg L.clusterOfCta (hCta.trans hGcta.symm)⟩
  have hsames : ScopesMeet L .cluster issuer scope g := by
    refine ⟨hCluster, ?_⟩
    cases scope <;> first
      | exact ⟨hG, hI, hGcta.trans hCta.symm⟩
      | exact ⟨hG, hI, hCluster.2.2.symm⟩
      | exact ⟨hG, hI⟩
  obtain ⟨_, hget⟩ := hload
  have hpo : po X (g, w) (g, j) :=
    po_of_source_not_access rfl hbefore (PTX.len_of_get hget) (by rw [hw]; rfl)
  exact ⟨i, hist, hissue, .inl ⟨(g, w), scope,
    ⟨_, _, ⟨(issuer, c), sp, rank, rfl, htrack, ⟨ct, hc⟩, htarget, hnotify⟩, hobserve⟩,
    hsames, .single (.inl hpo)⟩⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
