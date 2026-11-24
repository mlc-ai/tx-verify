-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.ResourceTmem
public import Kernels.Fp16Gemm8192.Proof.Safety.EventKinds

@[expose] public section

/-! # The Tensor Memory access branch of `Unsafe`, from the interface

The kernel's Tensor Memory accesses are its MMAs' accumulator writes and reads, in columns
`256 * (w % 2)` to `256 * (w % 2) + 255` of the cluster's CTA pair (`mma_source`, `result_cell`),
and its consumers' loads of sixteen words at column `256 * (w / 4) + 16 j` of their own CTA
(`ThreadFacts.tc_coll`, `data_loop`); no store, copy or shift is issued. Each is a role event of its
cluster.

*Allocation.* Thread 0 of each CTA of the cluster allocates at its event 20, which happens before
every role event of the cluster and has events past it (`ThreadFacts.alloc_before`), so it is
complete (`Tmem.Pair.Blocking`) and recorded in its CTA's history (`alloc_recorded`). The history
does not block, so the allocation is of all 512 columns at column 0 (`alloc_zero`): it covers the
access (`access_allocated`).

*Release.* The first deallocation after a covering allocation, or after its paired peer
allocation, is made by a lane of warp 0 of a CTA of the pair (`peer_pair`), past its thread's exit
wait (`ThreadFacts.dealloc_waited`); an MMA is observed complete and a load is finished by its wait
before it (`TmemExitDone`, `release_done`): in particular an MMA is complete before every release
of its accumulator's allocation (`mma_released`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX Tmem.Pair TcMma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An access of a role event's cluster pair, in its first 512 columns, is allocated.** -/
theorem access_allocated (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {e : EvId} {ev : Event} {r : Prologue.Role}
    (he : X.get e = some ev) (hσ : Frame.stateAt (code L) X e.1 e.2 = some (some (.inr r)))
    {cell : Cell}
    (hcta : cell.cta / 2 = e.1 / L.block / 2) (hcol : cell.column < 512) :
    ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column := by
  have hblock := hpre.block
  have hgrid := hpre.grid
  have hg := Frame.lt_of_get hX he
  have hT : cell.cta < L.grid := by
    have : e.1 / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    rw [hgrid] at this ⊢
    omega
  have hcl : L.clusterOfCta cell.cta = L.clusterOfCta (e.1 / L.block) := by
    simp only [clusterOfCta_eq hpre]
    omega
  obtain ⟨⟨pc, grp, dst, n, h20⟩, hlen, hhb⟩ :=
    ht.alloc_before (h := e.1) (j := e.2) he hσ hT hcl
  have hcov := hX.tmemPairBlocking.covered ⟨pc, _, _, _, h20, trivial⟩ (by simp only; omega)
  obtain ⟨rq, hrq, hev, hz⟩ := alloc_recorded hX (ht.warpOps hpre) (cta := cell.cta) (by
    rw [Nat.zero_mul, Nat.add_zero]
    exact hcov)
  simp only [Nat.zero_mul, Nat.add_zero] at hev
  obtain ⟨hc, -, -, hreq, -⟩ := record_info hX (ht.warpOps hpre) hrq
  have hget := ((hX.tmemPair.1 _).1 rq hrq).2.2.2.2.1 0
  rw [hev, h20] at hget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hget
  obtain ⟨col, hwa⟩ := Tmem.Action.request_eq_alloc (hreq.trans hget.2.2.2.symm)
  obtain ⟨rfl, rfl⟩ := alloc_zero hX (ht.warpOps hpre) hrq _ _ hwa
  refine ⟨cell.cta, rq, hrq, Covers.own ⟨512, 0, hwa, hc.symm, Nat.zero_le _, by omega, ?_⟩⟩
  rw [hev]
  exact hhb

/-- An access's footprint: a role event of its cluster, at a cell of its cluster's CTA pair in
the first 512 columns. -/
theorem access_cell (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {e : EvId} {cell : Cell} (hacc : Access L X e cell) :
    (∃ ev r, X.get e = some ev ∧ Frame.stateAt (code L) X e.1 e.2 = some (some (.inr r))) ∧
      cell.cta / 2 = e.1 / L.block / 2 ∧ cell.column < 512 := by
  have hblock := hpre.block
  -- an MMA's result cell
  have hmma : ∀ {d s acc mask r c}, X.MmaIssue e d s acc mask → resultCell s d r c = some cell →
      (∃ ev r, X.get e = some ev ∧ Frame.stateAt (code L) X e.1 e.2 = some (some (.inr r))) ∧
        cell.cta / 2 = e.1 / L.block / 2 ∧ cell.column < 512 := by
    intro d s acc mask r c hi hc
    obtain ⟨-, -, hw, ⟨sl, j, rfl⟩, rfl, -⟩ := mma_source hX ht hi
    obtain ⟨c1, c2⟩ := result_cell hc
    obtain ⟨pc, hget⟩ := hi
    obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
    obtain ⟨m, -, -, rfl, -⟩ := ht.mma_issue (Frame.lt_of_get hX hget) hget hσ rfl
    have := Nat.mod_lt (e.1 % L.block / 32) (show 0 < 2 by decide)
    exact ⟨⟨_, _, hget, hσ⟩, c1, by omega⟩
  rcases hacc with (⟨d, s, acc, mask, r, c, hi, hw⟩ | ⟨d, s, mask, r, c, hi, hc⟩ |
      ⟨d, s, acc, mask, idx, b, hi, ha⟩) | ⟨j, a, vals, sh, ⟨pc, hget⟩, hj, rfl⟩ |
      ⟨a, vals, sh, j, ⟨pc, hget⟩, -⟩ | ⟨a, src, cta, idx, ⟨pc, hget⟩, -⟩ | ⟨sp, hsh, -⟩ |
      ⟨sp, hsh, -⟩
  · exact hmma hi (writeCell_resultCell hw)
  · exact hmma hi hc
  · obtain ⟨-, -, -, ⟨sl, j, rfl⟩, -⟩ := mma_source hX ht hi
    simp [aCell, InputRing.mmaSpec] at ha
  · -- a load of sixteen words at its warp group's column of its chunk
    have hg := Frame.lt_of_get hX hget
    obtain rfl := ht.ld_shape hg hget
    obtain ⟨c, hσ, -, hlen⟩ := ht.data_loop hg hget rfl
    have h16 := hlen pc a vals rfl
    obtain ⟨hw8, p, -, hkind, -⟩ := ht.tc_coll hg hget rfl
    have ha : a = 256 * (e.1 % L.block / 32 / 4) + 16 * (p / 2) ∧ p < 32 := by
      unfold TcCollKind at hkind
      split_ifs at hkind with h1 h2 h3 h4
      · obtain ⟨vals', hk⟩ := hkind
        simp only [TcKind.ld.injEq] at hk
        exact ⟨hk.1, h1⟩
      all_goals simp_all
    obtain ⟨rfl, hp⟩ := ha
    refine ⟨⟨_, _, hget, hσ⟩, rfl, ?_⟩
    simp only [tcDataCell_s32x32b, tcDataCell32]
    have : 256 * (e.1 % L.block / 32 / 4) + 16 * (p / 2) < 2 ^ 16 := by omega
    rw [Nat.mod_eq_of_lt this]
    omega
  · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
    exact absurd rfl (ht.no_tc_st (Frame.lt_of_get hX hget) hget hσ)
  · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hget nofun
    exact absurd rfl (ht.no_tc_cp (Frame.lt_of_get hX hget) hget hσ)
  · exact (no_shift hX ht hsh).elim
  · exact (no_shift hX ht hsh).elim

/-- A paired peer of a record of this kernel is in its CTA pair. -/
theorem peer_pair (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    {q : WarpRequest × WarpRequest} (hq : q ∈ X.tmemPairing) : q.1.cta / 2 = q.2.cta / 2 := by
  obtain ⟨⟨⟨-, -, hc⟩, -⟩, -⟩ := (hX.tmemPair.2.1 q hq).1.2.2.2
  simpa only [clusterOfCta_eq hpre] using hc

/-- **An access is done before a release of its pair's allocation.** -/
theorem release_done (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hdone : TmemExitDone L X) {cta : Nat} {r : Requests}
    (hr : r ∈ X.tmemHistory cta) {e d : EvId} (hrel : ReleaseOf L X r d)
    (hc : e.1 / L.block / 2 = cta / 2) : TcMma.CompletedBefore L X e d := by
  have hblock := hpre.block
  obtain ⟨hlc, -⟩ := record_info hX (ht.warpOps hpre) hr
  -- the release: a deallocation of a lane of warp 0 of a CTA of the pair
  have hd : ∃ s : Requests, s.own.cta / 2 = cta / 2 ∧ s.own.warp = 0 ∧ OwnRelease L X s d := by
    rcases hrel with h | ⟨q, hq, s, hs, hpair, h⟩
    · exact ⟨r, by rw [hlc], (record_info hX (ht.warpOps hpre) hr).2.1, h⟩
    · refine ⟨s, ?_, (record_info hX (ht.warpOps hpre) hs).2.1, h⟩
      have hp := peer_pair hpre hX hq
      rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h2, ← hlc, ← h1, hp]
      · rw [← h2, ← hlc, ← h1, hp]
  obtain ⟨s, hwc, hw0, n, base, pc, -, ⟨grp, hget⟩, hlane⟩ := hd
  have hdg := Frame.lt_of_get hX hget
  have hEW := ht.dealloc_waited hdg hget
  have hdcta : d.1 / L.block = s.own.cta := by
    rcases hlane with ⟨lane, hd1, -⟩ | ⟨h, -⟩
    · simp only [WarpRequest.event, hw0] at hd1
      have := lane.isLt
      rw [hd1, hblock]
      omega
    · exact h
  have hdc : d.1 / L.block / 2 = e.1 / L.block / 2 := by
    clear hlane
    rw [hdcta, hc, hwc]
  refine ⟨fun ⟨a, vals, sh, hld⟩ => hdone.2 e d a vals sh _ hld hget hEW hdc,
    fun ⟨a, vals, sh, ⟨pcs, hst⟩⟩ => ?_, fun hasync => ?_⟩
  · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hst nofun
    exact absurd rfl (ht.no_tc_st (Frame.lt_of_get hX hst) hst hσ)
  · rcases hasync with ⟨dm, s, acc, mask, hmma⟩ | ⟨cp, pcc, hcp⟩ | ⟨sp, hsh⟩
    · exact hdone.1 e d dm s acc mask _ hmma hget hEW hdc
    · obtain ⟨dd, hσ⟩ := Frame.event_state ht.sound hX ht.tracked hcp nofun
      exact absurd rfl (ht.no_tc_cp (Frame.lt_of_get hX hcp) hcp hσ)
    · exact (no_shift hX ht hsh).elim

/-- A record covering a cell, by its own allocation event or through its paired peer allocation,
is of the cell's CTA. -/
theorem covers_key (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {cta owner col : Nat} {r : Requests} {e : EvId}
    (hr : r ∈ X.tmemHistory cta) (hcov : Covers L X r owner e col) : owner = cta := by
  obtain ⟨hlc, -⟩ := record_info hX (ht.warpOps hpre) hr
  obtain ⟨-, -, -, hown, -⟩ := hcov
  rw [hown, hlc]

/-- **No Tensor Memory access is unallocated or outlives its allocation.** -/
theorem no_access_unsafe (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hdone : TmemExitDone L X) :
    ¬ AccessUnsafe L X := by
  refine fun hn => hn fun e cell hacc => ?_
  obtain ⟨⟨ev, r, he, hσ⟩, hcta, hcol⟩ := access_cell hpre hX ht hacc
  refine ⟨access_allocated hpre hX ht he hσ hcta hcol,
    fun key rq hrq hcov d hrel => ?_⟩
  have hk := covers_key hpre hX ht hrq hcov
  exact .inl (release_done hpre hX ht hdone hrq hrel (by rw [← hk]; omega))

/-- **An MMA is complete before every release of an allocation covering its accumulator** (the
accumulators' lifetimes of the MMA instruction branch). -/
theorem mma_released (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hdone : TmemExitDone L X) :
    ∀ i d sp acc mask row col cell, X.MmaIssue i d sp acc mask →
      resultCell sp d row col = some cell → ∀ key r, r ∈ X.tmemHistory key →
        Covers L X r cell.cta i cell.column → ∀ release, ReleaseOf L X r release →
          DoneBefore L X i release := by
  intro i d sp acc mask row col cell hi hc key r hr hcov release hrel
  obtain ⟨-, -, -, ⟨sl, j, rfl⟩, rfl, -⟩ := mma_source hX ht hi
  obtain ⟨c1, -⟩ := result_cell hc
  have hk := covers_key hpre hX ht hr hcov
  exact (release_done hpre hX ht hdone hr hrel (by rw [← hk]; omega)).2.2 (.inl ⟨_, _, _, _, hi⟩)

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
