-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseEarlier
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreReadback
import Lemmas.Order.WaitOrderEnables
import Lemmas.Protocol.MbarOneShot

@[expose] public section

/-! # The predecessor generation of an output wait -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy PTX.MBarrier

private theorem checked_record_action {L : Launch} {mem0 : Mem0} {X : Execution}
    {m : Loc} {id : Ref} {act : Action} {k : Nat} {r : Record Ref}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hAct : objectAction X X.async m id = some act)
    (hr : (X.objects m)[k]? = some r) (hid : r.id = id) : r.action = act := by
  obtain ⟨j, q, hq, hqid, hqa⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hEq := ObjectInit.checked_record_index_eq (X.objects_checked hX m) hq hr
    (hqid.trans hid.symm)
  subst j
  rw [hr] at hq
  cases hq
  exact hqa

private theorem wait_phase {L : Launch} {mem0 : Mem0} {X : Execution}
    {m : Loc} {h : EvId} {tag parity k : Nat} {r : Record Ref} {acq : Bool}
    {sc : MbarScope} {st : State} (hX : Consistent L kernel Assumptions.all mem0 X)
    (hInit : PairTmaRing.InitFirst X m 1) (hNI : NoInval (X.objects m))
    (hw : X.get h = some ⟨tag, .wait m parity true acq sc⟩)
    (hr : (X.objects m)[k]? = some r) (hid : r.id = .thread h)
    (hst : stateBefore (X.objects m) k = some st) :
    st.phase % 2 ≠ parity % 2 ∧ r.reply.completed = (if 0 < st.phase then
      some (st.phase - 1) else none) := by
  have hAct := checked_record_action hX
    (show objectAction X X.async m (.thread h) = some (.pollParity parity true) by
      simp [objectAction, hw]) hr hid
  have hm := List.mem_of_getElem? hr
  have hClean := PairTmaRing.poll_clean hX hInit hNI r hm ⟨_, _, hAct⟩
  have hWait := ((hX.tma.2.2.1 m).2.1 r hm).2 parity true hAct hClean
  obtain ⟨s, p, hs, hp, hParity, hCompleted⟩ :=
    (X.objects_checked hX m).okPoll hr hWait
  rw [hst] at hs
  cases hs
  have heq := (Action.pollParity.inj (hp.symm.trans hAct)).1
  subst p
  exact ⟨hParity, hCompleted⟩

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A QK commit for a reused dequant slot depends on that generation's producer reuse wait.
The producer wait has already observed a completed PV phase. -/
theorem reuse_wait_before_qk_commit {cta issuer i : Nat} {slot : Fin 2} {d : Wg1Mma.D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.machine P L h).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer) (hCta : ctaOf L issuer = cta)
    (he : X.get (issuer, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X issuer i = some (some (.mma d)))
    (hSite : d.site = .qkCommit) (hSlot : d.i % 2 = slot.val) (hReuse : 1 ≤ d.i / 2) :
    let m := GemmRing.empty L cta slot
    let g := GemmRing.producer L cta 0
    let u := d.i / 2
    ∃ (k : Nat) (r : Record Ref) (st : State), (X.objects m)[k]? = some r ∧
      r.id = .thread (g, Poll.nth X m g u) ∧ stateBefore (X.objects m) k = some st ∧
      u ≤ st.phase ∧ st.phase % 2 = u % 2 ∧
      (∀ n < u, Notify.ph X m issuer m (0, n) < st.phase) ∧
      Relation.TransGen (DepStep L kernel X) (r.id, true)
        (.thread (issuer, i), false) := by
  dsimp only
  let R := GemmRing.dequantRing (slot := slot) hpre hX hs hmma
  let u := d.i / 2
  have hg := Frame.lt_of_get hX he
  have hCount := Wg1MmaGemmTrace.composed_count_here hpre hg .dequant
    ((hs issuer hg).produces (hX.thr issuer hg)) hState hSlot
  simp only [hSite, Wg1MmaGemmTrace.completed, ↓reduceIte] at hCount
  change okPolls (GemmRing.full L (ctaOf L issuer) slot) ((X.tr issuer).take i) = u + 1 at hCount
  rw [hCta] at hCount
  have hGuard : ∀ j ≤ u, Resumes kernel X (R.wF 0 j) (issuer, i) := by
    intro j hj
    change Resumes kernel X
      (issuer, Poll.nth X (GemmRing.full L cta slot) issuer j) (issuer, i)
    exact Poll.guard (fun _ _ _ _ _ _ h => RingSpins.successful_poll hX h)
      (PTX.len_of_get he) (by omega)
  obtain ⟨hPresent, hEarlier⟩ :=
    R.reach_consumer_op hX.depAcyclic 0 (b := 0) hGuard hReuse le_rfl
  let m := GemmRing.empty L cta slot
  let g := GemmRing.producer L cta 0
  let O := GemmRing.reuse_obj (slot := slot) hpre hX hs hmma
  have hPollPresent : u < okPolls m (X.tr g) := Poll.nth_present.mp hPresent
  have hProducer := GemmRing.producer_wg2 hpre cta (0 : Fin 128)
  obtain ⟨k, r, st, hr, hid, _, _, hState, hPos, _, hObs⟩ :=
    O.poll_obs hX hReuse hPollPresent hProducer
  obtain ⟨tag, parity, acq, scope, hw, hCount⟩ := Poll.nth_spec hPollPresent
  have hInputParity := O.parityOf hProducer hw
  rw [hCount] at hInputParity
  have hDifferent := (wait_phase hX O.init O.noInval hw hr hid hState).1
  have hStParity : st.phase % 2 = u % 2 := by omega
  have hEarlierPhases (n : Nat) (hn : n < u) : Notify.ph X m issuer m (0, n) < st.phase := by
    obtain ⟨hEarlierPresent, hOrd⟩ : X.RefPresent (.thread (R.wE 0 (n + 1))) ∧
        R.oE 0 (n + 1) ≤ R.oE 0 u := by
      rcases Nat.lt_or_eq_of_le (show n + 1 ≤ u by omega) with h | h
      · obtain ⟨present, hLt⟩ := R.ltE 0 (n + 1) u (by omega) h hPresent
        exact ⟨present, hLt.le⟩
      · rw [h]
        exact ⟨hPresent, le_rfl⟩
    have hPhase := ((R.content_empty (a := 0) (n := n) hX.depAcyclic hEarlierPresent).2 0).2
    change Notify.ph X m issuer m (0, n) = R.oE 0 (n + 1) at hPhase
    rw [hPhase]
    change Unit.obsOf X m g u = st.phase - 1 at hObs
    change R.oE 0 u = st.phase - 1 at hObs
    rw [hObs] at hOrd
    omega
  have hOrd : ∀ n < u, n ≤ R.oE 0 (n + 1) := by
    intro n
    induction n with
    | zero => exact fun _ => Nat.zero_le _
    | succ n ih =>
      intro hn
      have hHere : X.RefPresent (.thread (R.wE 0 (n + 1 + 1))) := by
        rcases Nat.lt_or_eq_of_le (show n + 1 + 1 ≤ u by omega) with h | h
        · exact (R.ltE 0 _ _ (by omega) h hPresent).1
        · rwa [h]
      have hLt := (R.ltE 0 (n + 1) (n + 1 + 1) (by omega) (by omega) hHere).2
      have hBase := ih (by omega)
      omega
  have hBound := hOrd (u - 1) (by omega)
  rw [show u - 1 + 1 = u by omega] at hBound
  change u - 1 ≤ Unit.obsOf X m g u at hBound
  rw [hObs] at hBound
  refine ⟨k, r, st, hr, hid, hState, by omega, hStParity, hEarlierPhases, ?_⟩
  rw [hid]
  exact hEarlier

/-- The lane has already observed the QK commit from the last block's slot use. -/
def QkBeforeFinalPoll (P : Params) (L : Launch) (X : Execution)
    (cta issuer block j : Nat) (lane : Fin 128) : Prop :=
  let g := GemmRing.softmax L cta lane
  let m := GemmRing.qk L cta (rawSlot block)
  ∃ q < j, ∃ qtag parity sc c ctag sp rank, ∃ mma : Wg1Mma.D,
    X.get (g, q) = some ⟨qtag, .wait m parity true true sc⟩ ∧
    X.get (issuer, c) = some ⟨ctag, .tc (.commit sp)⟩ ∧
    Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma mma)) ∧
    ctaOf L issuer = cta ∧ mma.site = .qkCommit ∧ mma.i = block ∧
    Witness L X (.async (issuer, c) (.tcNotify rank)) (g, q)

/-- The output wait on a reused slot follows a producer's reuse wait in the object history.
This gives a lower bound on the output wait's phase from the last block's QK dependency. -/
private theorem reuse_wait_before_output_wait {cta issuer j tag block : Nat} {lane : Fin 128}
    {slot : Fin 2} {scope : MbarScope} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hQk : QkBeforeFinalPoll P L X cta issuer block j lane) (hSlot : block % 2 = slot.val)
    (hReuse : 1 ≤ block / 2)
    (hw : X.get (GemmRing.softmax L cta lane, j) = some
      ⟨tag, .wait (GemmRing.empty L cta slot) (block / 2 % 2) true true scope⟩) :
    let m := GemmRing.empty L cta slot
    ∀ k (r : Record Ref) (st : State), (X.objects m)[k]? = some r →
      r.id = .thread (GemmRing.softmax L cta lane, j) →
      stateBefore (X.objects m) k = some st →
      block / 2 < st.phase ∧
        ∀ n < block / 2, Notify.ph X m issuer m (0, n) < st.phase - 1 := by
  dsimp only
  let g := GemmRing.softmax L cta lane
  let m := GemmRing.empty L cta slot
  obtain ⟨q, hq, qtag, parity, sc, c, ctag, sp, rank, mma,
    hQWait, hCommit, hMma, hCta, hQk, hMatch, hObs⟩ := hQk
  obtain ⟨kPrev, rPrev, stPrev, hRecord, hId, hPrevState, hLower, hParity, hEarlier, hPath⟩ :=
    reuse_wait_before_qk_commit hpre hX (fun h hh => (hs h hh).machine)
      hmma hCta hCommit hMma hQk (hMatch.symm ▸ hSlot) (hMatch.symm ▸ hReuse)
  rw [hMatch] at hLower hParity hEarlier
  obtain ⟨hNotify, _⟩ := hObs.waitObserves_tcNotify hQWait
  have hIssued : DepStep L kernel X (.thread (issuer, c), false)
      (.async (issuer, c) (.tcNotify rank), false) :=
    DepStep.issue ⟨_, hCommit⟩ hNotify (by intro _ h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
  obtain ⟨exit, hSpin⟩ := RingSpins.successful_poll hX hQWait
  have hTrace : TraceBefore X (g, q) (g, j) :=
    ⟨rfl, hq, PTX.len_of_get hw⟩
  have hResume : Resumes kernel X (g, q) (g, j) := by
    refine ⟨hTrace, ?_⟩
    change (match ((X.get (GemmRing.softmax L cta lane, q)).map
      (fun ev => ev.kind.resume) : Option Resume) with
      | some (Resume.blocking _) => True
      | some Resume.observing => SpinExit kernel X (g, q) (g, j)
      | _ => False)
    rw [hQWait]
    exact ⟨_, exit, _, _, _, _, hQWait, hSpin, hTrace⟩
  have hDep : Relation.TransGen (DepStep L kernel X) (rPrev.id, true) (.thread (g, j), false) :=
    ((hPath.tail hIssued).tail (DepStep.of_witness L hObs)).tail (DepStep.of_resumes L hResume)
  have hBefore := MbarRing.Round.Slot.not_before_of_reach (m := m) hX hDep
  intro kWait rWait stWait hRecordWait hIdWait hStateWait
  have hIndex : kPrev ≤ kWait := by
    by_contra! hLt
    exact hBefore ⟨kWait, kPrev, rWait, rPrev, hRecordWait, hIdWait, hRecord, rfl, hLt⟩
  let O := GemmRing.reuse_obj (slot := slot) hpre hX (fun h hh => (hs h hh).machine) hmma
  obtain ⟨adv, hAdv, hLe⟩ := (X.objects_checked hX m).phase_mono O.noInval
    hIndex (List.getElem?_eq_some_iff.mp hRecordWait).1.le hPrevState
  rw [hStateWait] at hAdv
  cases hAdv
  have hOpposite := (wait_phase hX O.init O.noInval hw hRecordWait hIdWait hStateWait).1
  have hStrict : stPrev.phase < stWait.phase := by
    rcases Nat.lt_or_eq_of_le hLe with h | h
    · exact h
    · exact (hOpposite (by rw [← h, hParity, Nat.mod_mod])).elim
  exact ⟨hLower.trans_lt hStrict, fun n hn => by have := hEarlier n hn; omega⟩

/-- A successful final PV wait observes the PV commit of its own block. For a reused slot,
all earlier uses precede the phase observed by the output lane. -/
private theorem final_pv_observed_of_qk {cta issuer j tag block : Nat} {lane : Fin 128}
    {slot : Fin 2} {scope : MbarScope} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hLast : block + 1 = Wg0.blocksOf P L (GemmRing.softmax L cta lane))
    (hQk : QkBeforeFinalPoll P L X cta issuer block j lane) (hSlot : block % 2 = slot.val)
    (hw : X.get (GemmRing.softmax L cta lane, j) = some
      ⟨tag, .wait (GemmRing.empty L cta slot) (block / 2 % 2) true true scope⟩) :
    let m := GemmRing.empty L cta slot
    ∃ commit ctag spec rank pv,
      X.get (issuer, commit) = some ⟨ctag, .tc (.commit spec)⟩ ∧
      TcCommit.target spec rank = some m ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer commit = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = block ∧
      Witness L X (.async (issuer, commit) (.tcNotify rank)) (GemmRing.softmax L cta lane, j) := by
  dsimp only
  let g := GemmRing.softmax L cta lane
  let m := GemmRing.empty L cta slot
  let u := block / 2
  let hMachine (h : Nat) (hh : h < L.threads) := (hs h hh).machine
  let O := GemmRing.reuse_obj (slot := slot) hpre hX hMachine hmma
  have hAct : objectAction X X.async m (.thread (g, j)) = some (.pollParity (u % 2) true) := by
    simp [objectAction, hw, g, m, u]
  obtain ⟨k, r, hr, hid, ha⟩ := MbarOneShot.Hist.record_of_action hX hAct
  have hmem := List.mem_of_getElem? hr
  have hClean := PairTmaRing.poll_clean hX O.init O.noInval r hmem ⟨_, _, ha⟩
  have hWait := ((hX.tma.2.2.1 m).2.1 r hmem).2 (u % 2) true ha hClean
  obtain ⟨st, _, hst, _, _, _⟩ := (X.objects_checked hX m).okPoll hr hWait
  obtain ⟨hParity, hReply⟩ := wait_phase hX O.init O.noInval hw hr hid hst
  have hOlder : u < st.phase ∧ ∀ n < u, Notify.ph X m issuer m (0, n) < st.phase - 1 := by
    by_cases hn : 1 ≤ u
    · exact reuse_wait_before_output_wait hpre hX hs hmma hQk hSlot hn hw k r st
        hr hid hst
    · have hz : u = 0 := by omega
      change st.phase % 2 ≠ u % 2 % 2 at hParity
      rw [hz] at hParity ⊢
      exact ⟨by omega, fun n hn => (Nat.not_lt_zero n hn).elim⟩
  have hpos : 0 < st.phase := by omega
  obtain ⟨c, ctag, sp, rank, pv, hc, htarget, hpv, hCta, hPvSite, hPvSlot, hWitness⟩ :=
    GemmRing.actual_pv_wait_observes_commit hpre hX hs hmma hw
      (.inr ⟨r, hmem, hid, by rw [hReply, ite_eq_left hpos]; rfl⟩)
  obtain ⟨hNotify, hObserved⟩ := hWitness.waitObserves_tcNotify hw
  obtain ⟨a, b, update, waiter, phase, ha', hu, hFault, hb', hWaitId, _, _, _, hPhase, hObs, _⟩ :=
    hObserved.2
  have hIndex := ObjectInit.checked_record_index_eq (X.objects_checked hX m) hb' hr
    (hWaitId.trans hid.symm)
  rw [hIndex] at hObs
  have hPhaseEq : phase = st.phase - 1 := by
    have hObs' : observedAt (X.objects m) k = some (st.phase - 1) := by
      simp [observedAt, hr, hReply, hpos]
    exact Option.some.inj (hObs.symm.trans hObs')
  have hUpdateAct := checked_record_action hX
    (show objectAction X X.async m (.async (issuer, c) (.tcNotify rank)) = some (.arrive 1 0) by
      simp [objectAction, hc, htarget, hNotify, m]) ha' hu
  obtain ⟨n, hn, hUpdateId⟩ := O.rec_S ha' hFault hUpdateAct
  have hSameCommit : Notify.cm X issuer m n.2 = c := by
    have h := congrArg (Prod.snd ∘ Ref.issuer) (hUpdateId.symm.trans hu)
    exact h
  have hPhaseOf : Notify.ph X m issuer m n = st.phase - 1 := by
    unfold Notify.ph
    rw [← hUpdateId, Poll.phaseOf_eq hX ha' hPhase, hPhaseEq]
  have hNotEarlier : u ≤ n.2 := by
    by_contra! hn'
    have hnEq : n = (0, n.2) := Prod.ext (Subsingleton.elim _ _) rfl
    exact (Nat.ne_of_lt (hOlder.2 n.2 hn')) (hnEq ▸ hPhaseOf)
  obtain ⟨_, _, _, _, hMmaInv, _, _⟩ := Frame.fired_site hs hX hc hpv
  have hMmaBound := (show Wg1Mma.Inv P L issuer pv from hMmaInv).i_lt
    (by rw [hPvSite]; trivial)
  have hgCta : ctaOf L g = cta := by
    have hl := lane.isLt
    simp only [g, GemmRing.softmax, ctaOf, hpre.block]
    omega
  have hBatch : Wg1Mma.eOf L issuer = Wg0.eOf L g := by
    change ctaidY L issuer = ctaidY L g
    simp only [ctaidY, hCta, hgCta]
  have hPads (n : Nat) : Wg1Mma.pad64 n = Result.ceilToMultiple n Result.topkBlock := by
    unfold Wg1Mma.pad64 Result.ceilToMultiple Result.topkBlock
    rw [show n + 64 - 1 = n + 63 by omega]
  have hBlocks : Wg1Mma.blocks P L issuer = Wg0.blocksOf P L g := by
    unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.len0 Wg1Mma.len1 Wg0.blocksOf
    rw [hBatch, hPads, hPads, Result.blocks_eq_kernel]
    rfl
  rw [hBlocks, ← hLast] at hMmaBound
  have hCount := (O.S_rec hn).2
  obtain ⟨_, _, _, _, _, hCount⟩ := hCount
  rw [hSameCommit] at hCount
  have hMmaCount := Wg1MmaGemmTrace.composed_count_here hpre (Frame.lt_of_get hX hc) .pv
    ((hMachine issuer (Frame.lt_of_get hX hc)).produces (hX.thr issuer (Frame.lt_of_get hX hc)))
    hpv hPvSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at hMmaCount
  change ((X.tr issuer).take c).countP
    (commitsTo (GemmRing.empty L (ctaOf L issuer) slot)) = pv.i / 2 at hMmaCount
  rw [hCta] at hMmaCount
  change ((X.tr issuer).take c).countP (commitsTo m) = n.2 at hCount
  have hGeneration : n.2 = pv.i / 2 := hCount.symm.trans hMmaCount
  rw [hGeneration] at hNotEarlier
  have hBlockEq : pv.i = block := by dsimp [u] at hNotEarlier; omega
  exact ⟨c, ctag, sp, rank, pv, hc, htarget, hCta, hpv, hPvSite, hBlockEq, hWitness⟩

theorem actual_final_pv_observed {cta issuer j tag : Nat} {lane : Fin 128} {slot : Fin 2}
    {d : Wg0.D} {scope : MbarScope} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hState : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 d))) (hSite : d.site = .svDone) (hSlot : d.block % 2 = slot.val)
    (hw : X.get (GemmRing.softmax L cta lane, j) = some
      ⟨tag, .wait (GemmRing.empty L cta slot) (d.block / 2 % 2) true true scope⟩) :
    let m := GemmRing.empty L cta slot
    ∃ commit ctag spec rank pv,
      X.get (issuer, commit) = some ⟨ctag, .tc (.commit spec)⟩ ∧
      TcCommit.target spec rank = some m ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer commit = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = d.block ∧
      Witness L X (.async (issuer, commit) (.tcNotify rank)) (GemmRing.softmax L cta lane, j) := by
  dsimp only
  let g := GemmRing.softmax L cta lane
  have hg := Frame.lt_of_get hX hw
  obtain ⟨p, hp, prior, k, event, hPrior, hBlock, hProb, hStore, _⟩ :=
    Wg0ProbabilityHistory.before_pv_wait hX hg (hs g hg).machine hState hSite
  obtain ⟨q, hq, qtag, parity, sc, c, ctag, sp, rank, mma,
    hQWait, hCommit, _, hMma, hCta, hQk, hSame, _, hObs⟩ :=
    GemmRing.actual_qk_commit_before_probability hpre hX hs hmma hPrior hProb hStore
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hw hState
  have hLast : d.block + 1 = Wg0.blocksOf P L g :=
    (show Wg0.Inv P L g d from hInv).epilogueLast (by rw [hSite]; rfl)
  exact final_pv_observed_of_qk hpre hX hs hmma hLast
    ⟨q, hq.trans hp, qtag, parity, sc, c, ctag, sp, rank, mma, hBlock ▸ hQWait,
      hCommit, hMma, hCta, hQk, hSame.trans hBlock, hObs⟩ hSlot hw

/-- The actual epilogue wait observes the last block, including on dismissed lanes. -/
theorem final_pv_observed_of_counts {cta issuer j tag block : Nat} {lane : Fin 128}
    {scope : MbarScope} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hLast : block + 1 = Wg0.blocksOf P L (GemmRing.softmax L cta lane))
    (hw : X.get (GemmRing.softmax L cta lane, j) = some
      ⟨tag, .wait (GemmRing.empty L cta (rawSlot block)) (block / 2 % 2) true true scope⟩)
    (hCount : block / 2 + 1 ≤ okPolls (GemmRing.qk L cta (rawSlot block))
      ((X.tr (GemmRing.softmax L cta lane)).take j)) :
    let m := GemmRing.empty L cta (rawSlot block)
    ∃ commit ctag spec rank pv,
      X.get (issuer, commit) = some ⟨ctag, .tc (.commit spec)⟩ ∧
      TcCommit.target spec rank = some m ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer commit = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = block ∧
      Witness L X (.async (issuer, commit) (.tcNotify rank)) (GemmRing.softmax L cta lane, j) := by
  let g := GemmRing.softmax L cta lane
  have hWg : wgOf L g = 0 := by
    have hl := lane.isLt
    simp only [g, GemmRing.softmax, wgOf, tidOf_eq hpre, hpre.block]
    omega
  obtain ⟨q, qtag, parity, acq, sc, hq, hGet, hOrdinal⟩ := Poll.exists_nth hCount
  have hAcq := MachineTracking.actual_qk_wait_is_acquire hpre hX hs hWg hGet
  subst acq
  obtain ⟨c, ctag, sp, rank, d, hc, _, hd, hCta, hSite, hBlock, hObs⟩ :=
    ScoreReadback.commit_of_counted_qk_wait hpre hX hs hmma hGet hOrdinal
  exact final_pv_observed_of_qk hpre hX hs hmma hLast
    ⟨q, hq, qtag, parity, sc, c, ctag, sp, rank, d, hGet, hc,
      hd, hCta, hSite, hBlock, hObs⟩ rfl hw

theorem final_pv_observed {cta issuer j tag : Nat} {lane : Fin 128} {slot : Fin 2} {d : Wg0.D}
    {scope : MbarScope} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (_ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hState : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 d))) (hSite : d.site = .svDone) (hSlot : d.block % 2 = slot.val)
    (hw : X.get (GemmRing.softmax L cta lane, j) = some
      ⟨tag, .wait (GemmRing.empty L cta slot) (d.block / 2 % 2) true true scope⟩) :
    let m := GemmRing.empty L cta slot
    ∃ commit ctag spec rank pv,
      X.get (issuer, commit) = some ⟨ctag, .tc (.commit spec)⟩ ∧
      TcCommit.target spec rank = some m ∧ ctaOf L issuer = cta ∧
      Frame.stateAt (Machine.code P L) X issuer commit = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = d.block ∧
      Witness L X (.async (issuer, commit) (.tcNotify rank)) (GemmRing.softmax L cta lane, j) :=
  actual_final_pv_observed hpre hX hs hmma hState hSite hSlot hw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputReuseAudit
