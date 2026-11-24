-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputWaitGeneration
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingStageQkHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaBlockOrder
import Lemmas.Order.OrderBaseCausality

@[expose] public section

/-! # Completion of GEMM operands before output staging -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv

open PTX PTX.Flow GemmRing AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i issuer : Nat} {out : Wg0.D} {e : Event} {tile : Fin 4} {chunk : Fin 8}

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : MmaIssuer P L X (ctaOf L g) issuer) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 out)))
include hpre hX hs ht hmma he hd

private theorem final_commit_before_tail
    (hWait : ∃ w < i, ∃ tag sc, X.get (g, w) = some
      ⟨tag, .wait (empty L (ctaOf L g) (rawSlot out.block)) (out.block / 2 % 2) true true sc⟩ ∧
      ∃ q : Wg0.D, Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)) ∧
        q.site = .svDone ∧ q.block = out.block) :
    let m := empty L (ctaOf L g) (rawSlot out.block)
    ∃ (w wt c ct : Nat) (sc : MbarScope) (sp : TcCommit.Spec) (rank : Fin 16) (d : Wg1Mma.D),
      w < i ∧ X.get (g, w) = some ⟨wt, .wait m (out.block / 2 % 2) true true sc⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      ctaOf L issuer = ctaOf L g ∧ d.site = .pvCommit ∧ d.i = out.block ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) ∧
      baseCausality L X (g, w) (g, i) := by
  dsimp only
  let slot := rawSlot out.block
  let m := empty L (ctaOf L g) slot
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  have h : Wg0.Inv P L g out := hInv
  obtain ⟨lane, hLane⟩ := softmax_thread hpre rfl h.wg
  obtain ⟨w, hwlt, wt, sc, hw, q, hWaitState, hWaitSite, hWaitBlock⟩ := hWait
  have hState : Frame.stateAt (Machine.code P L) X (softmax L (ctaOf L g) lane) w =
      some (some (.wg0 q)) := by
    rwa [← hLane]
  have hWait : X.get (softmax L (ctaOf L g) lane, w) =
      some ⟨wt, .wait m (q.block / 2 % 2) true true sc⟩ := by
    rw [← hLane, hWaitBlock]
    exact hw
  have hSlot : q.block % 2 = slot.val := by rw [hWaitBlock]; rfl
  obtain ⟨c, ct, sp, rank, d, hc, hTarget, hCta, hD, hSite, hBlock, hObs⟩ :=
    OutputReuseAudit.final_pv_observed hpre hX hs ht hmma hState hWaitSite hSlot hWait
  rw [← hLane] at hObs
  have hbase : baseCausality L X (g, w) (g, i) :=
    .single (.inl (po_of_source_not_access rfl hwlt (PTX.len_of_get he) (by rw [hw]; rfl)))
  exact ⟨w, wt, c, ct, sc, sp, rank, d, hwlt, hw, hc, hTarget, hCta, hSite,
    hBlock.trans hWaitBlock, hD, hObs, hbase⟩

/-- The successful acquire before any actual staging write observes its block's final PV commit. -/
theorem final_commit_before_stage (hsite : out.site = .oStage tile chunk) :
    let m := empty L (ctaOf L g) (rawSlot out.block)
    ∃ (w wt c ct : Nat) (sc : MbarScope) (sp : TcCommit.Spec) (rank : Fin 16) (d : Wg1Mma.D),
      w < i ∧ X.get (g, w) = some ⟨wt, .wait m (out.block / 2 % 2) true true sc⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      ctaOf L issuer = ctaOf L g ∧ d.site = .pvCommit ∧ d.i = out.block ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) ∧
      baseCausality L X (g, w) (g, i) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  exact final_commit_before_tail hpre hX hs ht hmma he hd
    (Wg0OutputVisits.pvWaitBeforeStage_state hpre hX hg (hs g hg).machine hInv hd hsite)

/-- The final PV commit is also observed before the lane arrives at its closing barrier. -/
theorem final_commit_before_closing (hsite : out.site = .everyone) :
    let m := empty L (ctaOf L g) (rawSlot out.block)
    ∃ (w wt c ct : Nat) (sc : MbarScope) (sp : TcCommit.Spec) (rank : Fin 16) (d : Wg1Mma.D),
      w < i ∧ X.get (g, w) = some ⟨wt, .wait m (out.block / 2 % 2) true true sc⟩ ∧
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧ TcCommit.target sp rank = some m ∧
      ctaOf L issuer = ctaOf L g ∧ d.site = .pvCommit ∧ d.i = out.block ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)) ∧
      Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w) ∧
      baseCausality L X (g, w) (g, i) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hd
  exact final_commit_before_tail hpre hX hs ht hmma he hd
    (Wg0OutputVisits.pvWaitBeforeClosing_state hpre hX hg (hs g hg).machine hInv hd hsite)
end

/-- The issuer and the softmax lane in one CTA have the same sparse block count. -/
theorem block_count_eq {h : Nat} (hc : ctaOf L h = ctaOf L g) :
    Wg1Mma.blocks P L h = Wg0.blocksOf P L g := by
  have hb : Wg1Mma.eOf L h = Wg0.eOf L g := by
    change ctaidY L h = ctaidY L g
    simp only [ctaidY, hc]
  have hpad (n : Nat) : Wg1Mma.pad64 n = Result.ceilToMultiple n Result.topkBlock := by
    unfold Wg1Mma.pad64 Result.ceilToMultiple Result.topkBlock
    rw [show n + 64 - 1 = n + 63 by omega]
  unfold Wg1Mma.blocks Wg1Mma.total Wg1Mma.len0 Wg1Mma.len1 Wg0.blocksOf
  rw [hb, hpad, hpad, Result.blocks_eq_kernel]
  rfl

private theorem tc_async_get {h k : Nat} (ho : X.TcAsync (h, k)) :
    ∃ ev, X.get (h, k) = some ev := by
  rcases ho with ⟨_, _, _, _, _, he⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩ <;> exact ⟨_, he⟩

/-- The final PV commit follows every QK or PV issue of its own or an earlier block. -/
theorem issue_before_final_commit {k c : Nat} {old d : Wg1Mma.D} {ct : Nat}
    {sp : TcCommit.Spec} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : (Machine.code P L issuer).Sound)
    (hOld : Frame.stateAt (Machine.code P L) X issuer k = some (some (.mma old)))
    (hOldSite : (∃ t, old.site = .qkMma t) ∨ (∃ t, old.site = .pvMma t))
    (hLe : old.i ≤ d.i)
    (hc : X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩)
    (hCommit : Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma d)))
    (hSite : d.site = .pvCommit) (hSlot : d.i % 2 = slot.val)
    (hMbar : sp.mbar = empty L (ctaOf L issuer) slot) : k < c := by
  by_contra! hge
  have hSame : old.i = d.i := Nat.le_antisymm hLe (Wg1Mma.block_order hge hCommit hOld)
  have hne : c ≠ k := by
    intro heq
    subst c
    rw [hCommit] at hOld
    have heq := Machine.ThreadD.mma.inj (Option.some.inj (Option.some.inj hOld))
    rw [← heq, hSite] at hOldSite
    rcases hOldSite with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
  have hh := Frame.lt_of_get hX hc
  have trace := hs.machine.produces (hX.thr issuer hh)
  have hOldOpen : Wg1MmaGemmTrace.completed .pv old.site = false := by
    rcases hOldSite with ⟨t, h⟩ | ⟨t, h⟩ <;> rw [h] <;> rfl
  have hOldSlot : old.i % 2 = slot.val := by rwa [hSame]
  have hCount := Wg1MmaGemmTrace.composed_count_here hpre hh .pv trace hOld hOldSlot
  simp only [hOldOpen, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hSame] at hCount
  have hCommitCount := Wg1MmaGemmTrace.composed_count_here hpre hh .pv trace hCommit hSlot
  simp only [Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    at hCommitCount
  let m := empty L (ctaOf L issuer) slot
  change ((X.tr issuer).take c).countP (commitsTo m) = d.i / 2 at hCommitCount
  change ((X.tr issuer).take k).countP (commitsTo m) = d.i / 2 at hCount
  have hMono := countP_take_mono (commitsTo m) (X.tr issuer) (show c + 1 ≤ k by omega)
  have hTick : commitsTo m ⟨ct, .tc (.commit sp)⟩ = true := by simp [commitsTo, m, hMbar]
  rw [countP_take_succ hc hTick, hCommitCount, hCount] at hMono
  omega

/-- All QK and PV issues of the output lane's CTA are complete before its staged overwrite,
including both operation families in the final block and all earlier blocks. -/
theorem operand_completed {h k index : Nat} {old : Wg1Mma.D} {isB : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : MmaIssuer P L X (ctaOf L g) issuer)
    (hCta : ctaOf L h = ctaOf L g) (hOp : X.TcAsync (h, k))
    (hOld : Frame.stateAt (Machine.code P L) X h k = some (some (.mma old)))
    (hOldSite : (∃ t, old.site = .qkMma t) ∨ (∃ t, old.site = .pvMma t))
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 out)))
    (hsite : out.site = .oStage tile chunk) :
    X.AsyncPresent (h, k) .mmaDone ∧
      ∃ w < i, AsyncFinished L X (h, k) (.mmaRead isB index) (g, w) ∧
        baseCausality L X (g, w) (g, i) := by
  have hNotElect : old.site ≠ .elect := by
    rcases hOldSite with ⟨t, h⟩ | ⟨t, h⟩ <;> simp [h]
  have hIssuer := hmma h k old hCta hOld hNotElect
  subst h
  have hLoop : Wg1Mma.LoopSite old.site := by
    rcases hOldSite with ⟨t, hs⟩ | ⟨t, hs⟩ <;> rw [hs] <;> trivial
  obtain ⟨_, hIssue⟩ := tc_async_get hOp
  obtain ⟨_, _, _, _, hMmaInv, _, _⟩ := Frame.fired_site hs hX hIssue hOld
  obtain ⟨_, _, _, _, hOutInv, _, _⟩ := Frame.fired_site hs hX he hd
  have hLt := (show Wg1Mma.Inv P L issuer old from hMmaInv).i_lt hLoop
  have hLast := (show Wg0.Inv P L g out from hOutInv).epilogueLast (by rw [hsite]; rfl)
  rw [block_count_eq (P := P) hCta, ← hLast] at hLt
  obtain ⟨w, wt, c, ct, sc, sp, rank, d, hwlt, hw, hc, hTarget, hcCta, hcSite, hBlock, hCommit,
    hObs, hBase⟩ := final_commit_before_stage hpre hX hs ht hmma he hd hsite
  have hI := Frame.lt_of_get hX hc
  let slot := rawSlot out.block
  have hSlot : d.i % 2 = slot.val := by rw [hBlock]; rfl
  obtain ⟨hMbar, _, _⟩ := GemmRing.notification hpre hX (hs issuer hI).machine ht hc rfl hTarget
  rw [← hcCta] at hMbar
  have hOrder := issue_before_final_commit hpre hX (hs issuer hI) hOld hOldSite
    (show old.i ≤ d.i by omega) hc hCommit hcSite hSlot hMbar
  have hTracks : TracksMma X (issuer, k) (issuer, c) := ⟨rfl, hOrder, hOp, sp, ⟨ct, hc⟩⟩
  have hg := Frame.lt_of_get hX he
  have hScopes : ScopesMeet L .cluster issuer sc g := by
    refine ⟨⟨hI, hg, congrArg L.clusterOfCta hcCta⟩, ?_⟩
    cases sc
    · exact ⟨hg, hI, hcCta.symm⟩
    · exact ⟨hg, hI, congrArg L.clusterOfCta hcCta.symm⟩
    · exact ⟨hg, hI⟩
    · exact ⟨hg, hI⟩
  obtain ⟨hDone, hFinished⟩ := completed_read hX ⟨ct, hc⟩ hTarget hTracks hScopes hw hObs
  exact ⟨hDone, w, hwlt, hFinished, hBase⟩

/-- An actual epilogue endpoint follows completion of all its CTA’s QK and PV operand reads. -/
theorem actual_operand_completed {h k index : Nat} {old : Wg1Mma.D} {isB : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ t < L.threads, (Machine.code P L t).Sound)
    (hmma : MmaIssuer P L X (ctaOf L g) issuer)
    (hCta : ctaOf L h = ctaOf L g) (hOp : X.TcAsync (h, k))
    (hOld : Frame.stateAt (Machine.code P L) X h k = some (some (.mma old)))
    (hOldSite : (∃ t, old.site = .qkMma t) ∨ (∃ t, old.site = .pvMma t))
    (he : X.get (g, i) = some e) (hStage : MachineTracking.EpiloguePvHistory P L X g i) :
    X.AsyncPresent (h, k) .mmaDone ∧
      ∃ w < i, AsyncFinished L X (h, k) (.mmaRead isB index) (g, w) ∧
        baseCausality L X (g, w) (g, i) ∧ TcMma.DoneBefore L X (h, k) (g, i) := by
  have hNotElect : old.site ≠ .elect := by
    rcases hOldSite with ⟨t, h⟩ | ⟨t, h⟩ <;> simp [h]
  have hIssuer := hmma h k old hCta hOld hNotElect
  subst h
  have hLoop : Wg1Mma.LoopSite old.site := by
    rcases hOldSite with ⟨t, hs⟩ | ⟨t, hs⟩ <;> rw [hs] <;> trivial
  obtain ⟨_, hIssue⟩ := tc_async_get hOp
  obtain ⟨_, _, _, _, hMmaInv, _, _⟩ := Frame.fired_site hs hX hIssue hOld
  have hLt := (show Wg1Mma.Inv P L issuer old from hMmaInv).i_lt hLoop
  let block := Wg0.blocksOf P L g - 1
  have hLast : block + 1 = Wg0.blocksOf P L g := by
    have := Wg0.blocksOf_pos P L g
    dsimp only [block]
    omega
  rw [block_count_eq (P := P) hCta, ← hLast] at hLt
  obtain ⟨lane, hLane⟩ := softmax_thread hpre rfl hStage.softmax
  obtain ⟨w, hwi, wt, sc, hw, hCounts⟩ := hStage.acquired
  have hw' : X.get (softmax L (ctaOf L g) lane, w) = some
      ⟨wt, .wait (empty L (ctaOf L g) (rawSlot block)) (block / 2 % 2) true true sc⟩ := by
    simpa only [← hLane] using hw
  have hCount : block / 2 + 1 ≤ okPolls (qk L (ctaOf L g) (rawSlot block))
      ((X.tr (softmax L (ctaOf L g) lane)).take w) := by
    rw [← hLane]
    have h := hCounts (rawSlot block)
    rw [← hLast] at h
    change (block + 1 + (1 - block % 2)) / 2 ≤
      okPolls (qk L (ctaOf L g) (rawSlot block)) ((X.tr g).take w) at h
    omega
  obtain ⟨c, ct, sp, rank, d, hc, hTarget, hcCta, hCommit, hcSite, hBlock, hObs⟩ :=
    OutputReuseAudit.final_pv_observed_of_counts hpre hX hs hmma
      (by simpa only [← hLane] using hLast) hw' hCount
  rw [← hLane] at hObs
  have hI := Frame.lt_of_get hX hc
  have hSlot : d.i % 2 = (rawSlot block).val := by rw [hBlock]; rfl
  obtain ⟨hMbar, _, _⟩ := GemmRing.actual_notification hpre hX hs hc rfl hTarget
  rw [← hcCta] at hMbar
  have hOrder := issue_before_final_commit hpre hX (hs issuer hI) hOld hOldSite
    (show old.i ≤ d.i by omega) hc hCommit hcSite hSlot hMbar
  have hTracks : TracksMma X (issuer, k) (issuer, c) := ⟨rfl, hOrder, hOp, sp, ⟨ct, hc⟩⟩
  have hg := Frame.lt_of_get hX he
  have hScopes : ScopesMeet L .cluster issuer sc g := by
    refine ⟨⟨hI, hg, congrArg L.clusterOfCta hcCta⟩, ?_⟩
    cases sc
    · exact ⟨hg, hI, hcCta.symm⟩
    · exact ⟨hg, hI, congrArg L.clusterOfCta hcCta.symm⟩
    · exact ⟨hg, hI⟩
    · exact ⟨hg, hI⟩
  obtain ⟨hDone, hFinished⟩ := completed_read hX ⟨ct, hc⟩ hTarget hTracks hScopes hw hObs
  have hBase : baseCausality L X (g, w) (g, i) :=
    .single (.inl (po_of_source_not_access rfl hwi (PTX.len_of_get he) (by rw [hw]; rfl)))
  obtain ⟨hNotify, hObserve⟩ := hObs.waitObserves_tcNotify hw
  have hComplete : TcMma.DoneBefore L X (issuer, k) (g, i) :=
    .inl ⟨(g, w), sc,
      ⟨_, _, ⟨(issuer, c), sp, rank, rfl, hTracks, ⟨ct, hc⟩, hTarget, hNotify⟩, hObserve⟩,
      hScopes, hBase⟩
  exact ⟨hDone, w, hwi, hFinished, hBase, hComplete⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.StageAfterPv
