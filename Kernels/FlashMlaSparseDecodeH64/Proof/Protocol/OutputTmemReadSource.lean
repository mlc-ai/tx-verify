-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmDequantRing
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvAccumulatorSource
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputWaitGeneration
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PvIssueHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.FollowedPrefix
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxPvWait
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Lemmas.Tcgen05.TcDataCell
import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # The PV result cell supplying each output register -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputTmemReadSource

open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy Wg0 MmaDataTrace
open Wg1Mma (pvDest tmemO)
open PvAccumulatorSource (Issue)
open Result (pvHalfIssue pvWriteCell)

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat} {d : D}

/-- The issued PV output half containing the addressed tile. -/
def tileHalf (tile : Fin 4) : Fin 2 := ⟨tile.val / 2, by have := tile.isLt; omega⟩

/-- The PV row corresponding to a softmax lane. -/
def resultRow (L : Launch) (g : Nat) : Fin 64 :=
  ⟨head L g, Nat.mod_lt _ (by decide)⟩

/-- The PV result column contains the lane's upper/lower 64-lane datapath and the column
within the issue's output half. -/
def resultColumn (L : Launch) (g : Nat) (tile : Fin 4) (reg : Fin 64) : Fin 256 :=
  ⟨128 * (tidOf L g % 128 / 64) + (64 * tile.val + reg.val) % 128, by
    have hLane := Nat.mod_lt (tidOf L g) (by decide : 0 < 128)
    have hCol := Nat.mod_lt (64 * tile.val + reg.val) (by decide : 0 < 128)
    omega⟩

/-- The last issue contributing to a tile's output half. -/
def lastIssue (tile : Fin 4) : Fin 8 := pvHalfIssue (tileHalf tile) 3

/-- The Tensor Memory cell read by a softmax tile register. -/
def outputCell (L : Launch) (g : Nat) (tile : Fin 4) (reg : Fin 64) : TcMma.Cell :=
  tcDataCell L g .s32x32b (64 * tile.val) reg.val

/-- The last issue writes the half addressed by the tile. -/
theorem lastIssue_half (tile : Fin 4) : (lastIssue tile).val % 2 = tile.val / 2 := by
  change (2 * 3 + tile.val / 2) % 2 = tile.val / 2
  have := tile.isLt
  omega

private theorem lastIssue_val (tile : Fin 4) : (lastIssue tile).val = 6 + tile.val / 2 := rfl

/-- A softmax tile register selects its thread's lane and the tile-relative column. -/
theorem outputCell_eq (hpre : Pre P L mem0) (hLane : tidOf L g < 128)
    (tile : Fin 4) (reg : Fin 64) :
    outputCell L g tile reg = ⟨ctaOf L g, tidOf L g, 64 * tile.val + reg.val⟩ := by
  have hAddr : 64 * tile.val < 2 ^ 16 := by have := tile.isLt; omega
  have htid := tidOf_eq (g := g) hpre
  have hwarp : g % 384 / 32 < 4 := by rw [← htid]; omega
  rw [outputCell, tcDataCell_s32x32b]
  simp only [tcDataCell32, laneBase, PTX.laneOf, ctaOf, Nat.mod_eq_of_lt hAddr,
    htid, hpre.block, Nat.mod_eq_of_lt hwarp]
  congr 1
  omega

/-- The output register and the PV result at its row, half and column refer to the same cell. -/
theorem outputCell_eq_pv {issuer : Nat}
    (hpre : Pre P L mem0) (hLane : tidOf L g < 128) (hCta : ctaOf L issuer = ctaOf L g)
    (tile : Fin 4) (reg : Fin 64) :
    outputCell L g tile reg = ⟨ctaOf L issuer,
      (resultRow L g).val + 64 * ((resultColumn L g tile reg).val / 128),
      tmemO + 128 * (tileHalf tile).val + (resultColumn L g tile reg).val % 128⟩ := by
  rw [outputCell_eq hpre hLane tile reg, hCta]
  simp only [TcMma.Cell.mk.injEq, true_and]
  constructor
  · symm
    have h := Nat.mod_lt (64 * tile.val + reg.val) (by decide : 0 < 128)
    change tidOf L g % 64 + 64 * ((128 * (tidOf L g % 128 / 64) +
      (64 * tile.val + reg.val) % 128) / 128) = tidOf L g
    omega
  · symm
    have hr := reg.isLt
    change tmemO + 128 * (tile.val / 2) + (128 * (tidOf L g % 128 / 64) +
      (64 * tile.val + reg.val) % 128) % 128 = 64 * tile.val + reg.val
    simp only [tmemO, Nat.zero_add]
    omega

/-- The last PV issue for the tile writes this register's cell. -/
theorem output_cell_written {issuer block src : Nat}
    (hpre : Pre P L mem0) (hLane : tidOf L g < 128) (hCta : ctaOf L issuer = ctaOf L g)
    (tile : Fin 4) (reg : Fin 64) (hi : Issue L X issuer src block (lastIssue tile)) :
    X.MmaCell (issuer, src) (outputCell L g tile reg) := by
  let row := resultRow L g
  let col := resultColumn L g tile reg
  have hw := pvWriteCell L issuer block (lastIssue tile) row col
  refine ⟨_, _, _, _, row.val, col.val, hi, ?_⟩
  rw [hw, outputCell_eq_pv hpre hLane hCta tile reg]
  simp only [pvDest, lastIssue_half, tileHalf, row, col]

private theorem scopes_of_cta {h : Nat} (hc : SameCta L h g) (scope : MbarScope) :
    ScopesMeet L .cluster h scope g := by
  have hc' : SameCluster L h g := ⟨hc.1, hc.2.1, congrArg L.clusterOfCta hc.2.2⟩
  refine ⟨hc', ?_⟩
  cases scope
  · exact ⟨hc.2.1, hc.1, hc.2.2.symm⟩
  · exact ⟨hc.2.1, hc.1, hc'.2.2.symm⟩
  · exact ⟨hc.2.1, hc.1⟩
  · exact ⟨hc.2.1, hc.1⟩

/-- An observed commit orders a prior PV result before the later Tensor Memory load. -/
theorem done_before_event_of_observed {issuer src c w wt ct : Nat} {block : Nat}
    {issue : Fin 8} {sp : TcCommit.Spec} {rank : Fin 16} {scope : MbarScope}
    {m : Loc} {parity : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : Issue L X issuer src block issue) (hpc : src < c)
    (hc : X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩)
    (hTarget : TcCommit.target sp rank = some m)
    (hw : X.get (g, w) = some ⟨wt, .wait m parity true true scope⟩)
    (hObs : Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w))
    (hCta : ctaOf L issuer = ctaOf L g) (hwi : w < i)
    (he : X.get (g, i) = some e) :
    TcMma.DoneBefore L X (issuer, src) (g, i) := by
  have hTrack : TracksMma X (issuer, src) (issuer, c) :=
    ⟨rfl, hpc, .inl ⟨_, _, _, _, hi⟩, sp, ct, hc⟩
  obtain ⟨hNotify, hObserved⟩ := hObs.waitObserves_tcNotify hw
  have hScopes := scopes_of_cta
    ⟨Frame.lt_of_get hX hi.choose_spec, Frame.lt_of_get hX hw, hCta⟩ scope
  have hBase : baseCausality L X (g, w) (g, i) := .single (.inl
    (po_of_source_not_access rfl hwi (PTX.len_of_get he) (by rw [hw]; rfl)))
  exact .inl ⟨(g, w), scope,
    ⟨_, _, ⟨(issuer, c), sp, rank, rfl, hTrack, ⟨ct, hc⟩, hTarget, hNotify⟩, hObserved⟩,
    hScopes, hBase⟩

theorem done_before_of_observed {issuer src c w wt ct : Nat} {block : Nat}
    {issue : Fin 8} {sp : TcCommit.Spec} {rank : Fin 16} {scope : MbarScope}
    {m : Loc} {parity : Nat} {words : List Value} {tile : Fin 4}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hi : Issue L X issuer src block issue) (hpc : src < c)
    (hc : X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩)
    (hTarget : TcCommit.target sp rank = some m)
    (hw : X.get (g, w) = some ⟨wt, .wait m parity true true scope⟩)
    (hObs : Witness L X (.async (issuer, c) (.tcNotify rank)) (g, w))
    (hCta : ctaOf L issuer = ctaOf L g) (hwi : w < i)
    (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b) :
    TcMma.DoneBefore L X (issuer, src) (g, i) :=
  done_before_event_of_observed hX hi hpc hc hTarget hw hObs hCta hwi hload.choose_spec

private theorem block_count_eq {h : Nat} (hc : ctaOf L h = ctaOf L g) :
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

/-- Any earlier-block writer or same-block writer of this half precedes its last issue. -/
theorem actual_prior_pv_index {issuer src j block : Nat} {q : Wg1Mma.D} {k : Fin 8}
    {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hblock : q.i ≤ block)
    (hold : Issue L X issuer j q.i k) (hsrc : Issue L X issuer src block (lastIssue tile))
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .pvMma k)
    (hS : Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.pvMma (lastIssue tile), block⟩)))
    (hhalf : k.val % 2 = (lastIssue tile).val % 2) : j ≤ src := by
  by_contra! hlt
  have hb := Wg1Mma.block_order hlt.le hS hq
  change block ≤ q.i at hb
  have hEq : q.i = block := Nat.le_antisymm hblock hb
  have hg := Frame.lt_of_get hX hsrc.choose_spec
  have hr := Wg0ProbabilityUnique.actual_rank_strict_of_counted hpre hX (hs issuer hg).machine
    hsrc.choose_spec rfl (PTX.len_of_get hold.choose_spec).le hS hq hlt
  simp only [Bound.rank, Bound.mmaRank, Bound.mmaOrdinal, hqSite, hEq, lastIssue_val] at hr
  have hk := k.isLt
  rw [lastIssue_half] at hhalf
  omega

theorem prior_pv_index {issuer src j block : Nat} {q : Wg1Mma.D} {k : Fin 8}
    {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hblock : q.i ≤ block)
    (hold : Issue L X issuer j q.i k) (hsrc : Issue L X issuer src block (lastIssue tile))
    (hq : Frame.stateAt (Machine.code P L) X issuer j = some (some (.mma q)))
    (hqSite : q.site = .pvMma k)
    (hS : Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.pvMma (lastIssue tile), block⟩)))
    (hhalf : k.val % 2 = (lastIssue tile).val % 2) : j ≤ src :=
  actual_prior_pv_index hpre hX hs hblock hold hsrc hq hqSite hS hhalf

private theorem output_write_order {issuer src w : Nat} {wait : Wg0.D} {tile : Fin 4} {reg : Fin 64}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hI : Issue L X issuer src d.block (lastIssue tile))
    (hS : Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.pvMma (lastIssue tile), d.block⟩)))
    (hCta : ctaOf L issuer = ctaOf L g) (hLane : tidOf L g < 128)
    (hWait : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 wait)))
    (hWaitSite : wait.site = .svDone)
    (hLast : d.block + 1 = Wg0.blocksOf P L g)
    (other : EvId) (hwrite : TcMma.TmemWrite L X other (outputCell L g tile reg)) :
    other = (issuer, src) ∨ TcMma.WriteBefore L X other (issuer, src) := by
  obtain ⟨t, j⟩ := other
  have hCell := outputCell_eq hpre hLane tile reg
  have hCol : (outputCell L g tile reg).column < 256 := by
    rw [hCell]
    have := tile.isLt
    have := reg.isLt
    change 64 * tile.val + reg.val < 256
    omega
  obtain ⟨hOwner, hRole⟩ := PvAccumulatorSource.actual_output_writer hpre hX hs hCol hwrite
  have hCt : ctaOf L t = ctaOf L g :=
    hOwner.symm.trans (congrArg TcMma.Cell.cta hCell)
  rcases hRole with hm | hr
  · obtain ⟨q, k, hq, hqSite, hqIssue, hHalf⟩ := hm
    have htEq := hmma t j q hCt hq (by rw [hqSite]; simp)
    subst t
    obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hqIssue.choose_spec hq
    have hb := (show Wg1Mma.Inv P L issuer q from hInv).i_lt (by rw [hqSite]; trivial)
    rw [block_count_eq (P := P) hCta, ← hLast] at hb
    have hColHalf : (outputCell L g tile reg).column / 128 = tile.val / 2 := by
      rw [hCell]
      have := reg.isLt
      change (64 * tile.val + reg.val) / 128 = tile.val / 2
      omega
    have hSameHalf : k.val % 2 = (lastIssue tile).val % 2 := by
      rw [lastIssue_half, ← hColHalf, hHalf]
    have hJ := actual_prior_pv_index hpre hX hs (show q.i ≤ d.block by omega)
      hqIssue hI hq hqSite hS hSameHalf
    rcases Nat.eq_or_lt_of_le hJ with rfl | hJ
    · exact .inl rfl
    · refine .inr (.inl (TcMma.Before.of_mma_po hqIssue hI
        (Frame.lt_of_get hX hqIssue.choose_spec) rfl hJ ?_))
      exact ⟨congrArg (fun n => tmemO + 128 * n) hSameHalf, rfl, rfl, rfl, rfl⟩
  · obtain ⟨k, words, hStore, hStoreCell, _, hTid, _⟩ := hr
    rw [hCell] at hTid
    change tidOf L g = tidOf L t at hTid
    have htEq : t = g := by
      rw [tidOf_eq hpre, tidOf_eq hpre] at hTid
      change t / L.block = g / L.block at hCt
      rw [hpre.block] at hCt
      omega
    subst t
    have hjw := MachineTracking.rescale_store_before_final_wait hX hs hWait hWaitSite hStore
    obtain ⟨s, hs'⟩ := FollowedPrefix.state_at hWait hjw.le
    obtain ⟨q, r, hstore⟩ := PvAccumulatorSource.followed_output_store hpre hX hs
      (by rw [hs']; simp) hStore hStoreCell
    obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX hstore.store.choose_spec hstore.state
    have hb := (show Wg0.Inv P L g q from hInv).blockLt
    rw [← hLast] at hb
    exact .inr (PvAccumulatorSource.actual_earlier_rescale hpre hX hs hI hS rfl
      hstore hCta.symm (show q.block ≤ d.block by omega))

section
variable {issuer w wt : Nat} {q : D} {scope : MbarScope} {tile : Fin 4} {words : List Value}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- A load following the final PV acquire takes each output register from its half's last
MMA issue. The caller supplies the release order for this load. -/
theorem actual_final_pv_source_of_wait (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hState : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)))
    (hWsite : q.site = .svDone) (hBlock : q.block = d.block)
    (hw : X.get (g, w) = some
      ⟨wt, .wait (GemmRing.empty L (ctaOf L g) (rawSlot q.block))
        (q.block / 2 % 2) true true scope⟩) (hwi : w < i) (hInv : Wg0.Inv P L g d)
    (hLast : d.block + 1 = Wg0.blocksOf P L g) (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b)
    (hWords : words.length = 64) (reg : Fin 64) :
    ∃ (c ct : Nat) (sp : TcCommit.Spec) (rank : Fin 16) (pv : Wg1Mma.D) (src : Nat),
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = d.block ∧ rank ∈ X.tcNotified (issuer, c) ∧
      src + (8 - (lastIssue tile).val) = c ∧
      Issue L X issuer src d.block (lastIssue tile) ∧
      TcMma.LoadCell L X (g, i) reg.val (outputCell L g tile reg) ∧
      (TcMma.SourceLive L X (issuer, src) (g, i) (outputCell L g tile reg) →
        TcMma.ReadSource L X .ld (issuer, src) (g, i) (outputCell L g tile reg)) := by
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre rfl hInv.wg
  have hState' : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L (ctaOf L g) lane) w =
      some (some (.wg0 q)) := by rwa [← hLane]
  have hw' : X.get (GemmRing.softmax L (ctaOf L g) lane, w) =
      some ⟨wt, .wait (GemmRing.empty L (ctaOf L g) (rawSlot q.block))
        (q.block / 2 % 2) true true scope⟩ := by simpa only [← hLane] using hw
  obtain ⟨c, ct, sp, rank, pv, hc, hTarget, hCta, hPv, hSite, hI, hObs⟩ :=
    OutputReuseAudit.actual_final_pv_observed hpre hX hs hmma hState' hWsite rfl hw'
  rw [← hLane] at hObs
  obtain ⟨src, hIdx, hSrc, hIssue⟩ :=
    PvIssueHistory.pv_issue_of_commit hpre hX hs hc hPv hSite (lastIssue tile)
  have hFinal : pv.i = d.block := hI.trans hBlock
  rw [hFinal] at hSrc hIssue
  have hSrcLt : src < c := by have := (lastIssue tile).isLt; omega
  have hDone := done_before_of_observed hX hIssue hSrcLt hc hTarget hw hObs hCta hwi hload
  have hLaneLt : tidOf L g < 128 := by have := hInv.warpLt; unfold warpOf at *; omega
  have hWrite := output_cell_written hpre hLaneLt hCta tile reg hIssue
  have hReg : reg.val < words.length := hWords.symm ▸ reg.isLt
  refine ⟨c, ct, sp, rank, pv, src, hc, hPv, hSite, hFinal, (hObs.waitObserves_tcNotify hw).1,
    hIdx, hIssue, ⟨_, _, _, hload, hReg, rfl⟩, ?_⟩
  intro hLive
  have hneq : (issuer, src) ≠ (g, i) := by
    intro h
    obtain ⟨_, he⟩ := hIssue
    rw [h] at he
    cases congrArg Event.kind (Option.some.inj (he.symm.trans hload.choose_spec))
  refine ⟨hneq, .inl hWrite, .inl (.inl hDone), ?_, hLive⟩
  intro other hwrite
  exact (output_write_order hpre hX hs hmma hIssue hSrc hCta hLaneLt hState hWsite hLast
    other hwrite).imp id Or.inl

theorem final_pv_source_of_wait (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X) (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hState : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 q)))
    (hWsite : q.site = .svDone) (hBlock : q.block = d.block)
    (hw : X.get (g, w) = some
      ⟨wt, .wait (GemmRing.empty L (ctaOf L g) (rawSlot q.block))
        (q.block / 2 % 2) true true scope⟩) (hwi : w < i) (hInv : Wg0.Inv P L g d)
    (hLast : d.block + 1 = Wg0.blocksOf P L g) (hload : X.TLd (g, i) (64 * tile.val) words .s32x32b)
    (hWords : words.length = 64) (reg : Fin 64) :
    ∃ (c ct : Nat) (sp : TcCommit.Spec) (rank : Fin 16) (pv : Wg1Mma.D) (src : Nat),
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = d.block ∧ rank ∈ X.tcNotified (issuer, c) ∧
      src + (8 - (lastIssue tile).val) = c ∧
      Issue L X issuer src d.block (lastIssue tile) ∧
      TcMma.LoadCell L X (g, i) reg.val (outputCell L g tile reg) ∧
      (TcMma.SourceLive L X (issuer, src) (g, i) (outputCell L g tile reg) →
        TcMma.ReadSource L X .ld (issuer, src) (g, i) (outputCell L g tile reg)) :=
  actual_final_pv_source_of_wait hpre hX hs hmma hState hWsite hBlock hw hwi hInv hLast
    hload hWords reg
end

/-- Each word held at the actual epilogue load wait has its output half's final PV issue as
its live Tensor Memory source. -/
theorem actual_final_source_at_wait {issuer tag : Nat} {tile : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .oWait tile) (hwait : X.get (g, i) = some ⟨tag, .tc .waitLd⟩)
    (reg : Fin 64) :
    ∃ (ld c ct : Nat) (sp : TcCommit.Spec) (rank : Fin 16) (pv : Wg1Mma.D) (src : Nat),
      X.get (issuer, c) = some ⟨ct, .tc (.commit sp)⟩ ∧
      Frame.stateAt (Machine.code P L) X issuer c = some (some (.mma pv)) ∧
      pv.site = .pvCommit ∧ pv.i = d.block ∧ rank ∈ X.tcNotified (issuer, c) ∧
      src + (8 - (lastIssue tile).val) = c ∧
      Issue L X issuer src d.block (lastIssue tile) ∧
      X.TLd (g, ld) (64 * tile.val) d.oWords .s32x32b ∧ d.oWords.length = 64 ∧
      TcMma.LoadCell L X (g, ld) reg.val (outputCell L g tile reg) ∧
      TcMma.ReadSource L X .ld (issuer, src) (g, ld) (outputCell L g tile reg) := by
  have hg := Frame.lt_of_get hX hwait
  obtain ⟨ld, hlt, q, e, words, hq, hqs, he, hk, hWords, hFields⟩ :=
    Wg0OutputPayload.at_wait hpre hX hg (hs g hg).machine hd hsite
  have hload : X.TLd (g, ld) (64 * tile.val) words .s32x32b := by
    cases e
    exact ⟨_, he.trans (congrArg some (congrArg (Event.mk _) hk))⟩
  obtain ⟨_, _, _, _, hInv, _, _⟩ := Frame.fired_site hs hX he hq
  have hInv : Wg0.Inv P L g q := hInv
  have hLast := hInv.epilogueLast (by rw [hqs]; rfl)
  obtain ⟨w, hwLt, wt, sc, hw, t, hWaitState, hWaitSite, hBlock⟩ :=
    Wg0OutputVisits.pvWaitBeforeLoad_state hpre hX hg (hs g hg).machine hInv hq hqs
  have hw' : X.get (g, w) = some
      ⟨wt, .wait (GemmRing.empty L (ctaOf L g) (rawSlot t.block))
        (t.block / 2 % 2) true true sc⟩ := by
    rw [hBlock]
    exact hw
  obtain ⟨c, ct, sp, rank, pv, src, hc, hPv, hPvSite, hPvBlock, hNotify, hIdx, hIssue,
    hLoadCell, hSource⟩ :=
    actual_final_pv_source_of_wait hpre hX hs hmma hWaitState hWaitSite hBlock hw'
      hwLt hInv hLast hload hWords reg
  have hSourceLive : TcMma.SourceLive L X (issuer, src) (g, ld) (outputCell L g tile reg) :=
    ScoreLifetime.sourceLive_of_actual_load_wait hpre hX hs hLoadCell hd
      (by rw [hsite]; rfl) hlt hwait
  have hdBlock := congrArg D.block hFields
  have hdWords := congrArg D.oWords hFields
  change d.block = q.block at hdBlock
  change d.oWords = words at hdWords
  rw [hdBlock, hdWords]
  exact ⟨ld, c, ct, sp, rank, pv, src, hc, hPv, hPvSite, hPvBlock, hNotify, hIdx, hIssue,
    hload, hWords, hLoadCell, hSource hSourceLive⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputTmemReadSource
