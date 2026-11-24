-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ProgressWg0Election
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.OutputPublication
import Lemmas.Order.ElectOrdinal
import Lemmas.Step.CtaBarNamed

public section

/-! # Availability of the output warp at a released tile election -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress

open PTX PTX.Flow Protocol

private instance : Fact kernel.NoBarArrive := ⟨by unfold Kernel.NoBarArrive; decide +kernel⟩

private theorem tail_barrier_releases {L : Launch} {X : Execution} {g tag : Nat}
    (he : X.IsBarrier (g, (X.tr g).length - 1) 9 (some 128) tag)
    (hr : PTX.Step.Released L X g) :
    ∃ key, CtaBarK L X (g, (X.tr g).length - 1) key ∧ CtaBarDone L X (g / L.block) key := by
  refine hr.ready tag (.bar 9 (some 128) .sync) he rfl (.cond _) ?_
  change X.get (g, (X.tr g).length - 1) = some ⟨tag, .bar 9 (some 128) .sync⟩ at he
  simp [Needs, he, KindNeeds, ctaBarNeeds]

set_option maxRecDepth 100000 in
private theorem site_of_output_election {s : Wg0.Site} {j : Fin 4}
    (h : s.pc = (Wg0.Site.elect j).pc) : s = .elect j := by
  cases s <;>
    first
    | rename_i k; revert k j h; decide
    | rename_i a k; revert a k j h; decide
    | revert j h; decide

set_option maxRecDepth 100000 in
private theorem prologue_before_election (s : Site) (j : Fin 4) :
    s.pc ≠ (Wg0.Site.elect j).pc := by
  cases s <;>
    first
    | rename_i k; revert k j; decide
    | revert j; decide

variable {P : Params} {L : Launch}

private theorem prior_election_impossible {mem0 : Mem0} {X : Execution} {g i inst leader : Nat}
    {d : Wg0.D} {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hwg : wgOf L g = 0)
    (hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .elect j) (he : X.Elect (g, i) (Wg0.Site.elect j).pc (2 ^ 32 - 1) inst leader)
    : False := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨p, hP⟩ := Frame.event_state hs hX ht he (by intros; simp)
  have hAt := Frame.event_pc hs hX he hP
  rcases Wg0OutputVisits.softmax_state_cases hX hg (hs g hg).machine hwg hP with
    ⟨s, rfl⟩ | ⟨q, rfl⟩ | rfl
  · exact prologue_before_election s j hAt.symm
  · have hQ : q.site = .elect j := site_of_output_election hAt.symm
    have hLt : i < (X.tr g).length := len_of_get he
    obtain ⟨bi, e, v, hbi, hb, hbar, hV, hv⟩ :=
      Wg0OutputControl.barrierBeforeElection hpre hX (hs g hg).machine hLt.le hP hQ
    obtain ⟨bt, f, t, hbt, hf, hbar', hT, ht'⟩ :=
      Wg0OutputControl.barrierBeforeElection hpre hX (hs g hg).machine le_rfl hTail hSite
    have hOrd := Wg0BarrierCount.epiOrdinal hpre hX (hs g hg).machine hb hV hv
    have hOrd' := Wg0BarrierCount.epiOrdinal hpre hX (hs g hg).machine hf hT ht'
    obtain ⟨tag, kind⟩ := e
    cases hbar
    obtain ⟨tag', kind'⟩ := f
    cases hbar'
    have hSame := NamedBar.source_ordinal_unique hb hf (hOrd.trans hOrd'.symm)
    omega
  · have hPC : (Wg0.Site.elect j).pc = 3611 := hAt
    have hNe : ∀ j : Fin 4, (Wg0.Site.elect j).pc ≠ 3611 := by decide
    exact hNe j hPC

private theorem election_after_barrier {X : Execution} {g i tag : Nat} {d : Wg0.D} {j : Fin 4}
    (hw : warpOf L g < 2) (he : X.IsBarrier (g, i) 9 (some 128) tag)
    (hσ : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hd : d.site = .epiBar j) :
    ∃ q, Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) ∧
      q.site = .elect j := by
  rw [Frame.stateAt_succ he, hσ]
  let q := { d with site := Wg0.Site.elect j }
  refine ⟨q, ?_, rfl⟩
  change Machine.next P L g (.wg0 d) ⟨tag, .bar 9 (some 128) .sync⟩ = some (some (.wg0 q))
  simp [Machine.next, Wg0.next, Wg0.nextSite, Wg0.epiAfterBar, hd,
    show ¬ 2 ≤ warpOf L g by omega, q]

private theorem peer_election_missing {mem0 : Mem0} {X : Execution} {g h k : Nat} {d q : Wg0.D}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hw : SameWarp L g h)
    (hwg : wgOf L g = 0)
    (hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .elect j)
    (hPeer : Frame.stateAt (Machine.code P L) X h k = some (some (.wg0 q)))
    (hPeerSite : q.site = .elect j) :
    k ≥ (X.tr h).length := by
  by_contra hShort
  have hlt : k < (X.tr h).length := by omega
  have he : X.get (h, k) = some (X.tr h)[k] := List.getElem?_eq_getElem hlt
  obtain ⟨inst, leader, heq⟩ := softmax_election_event hs hX hPeer hPeerSite he
  rw [heq] at he
  have hPeerElect : X.Elect (h, k) (Wg0.Site.elect j).pc (2 ^ 32 - 1) inst leader := he
  have hMask : electMember (2 ^ 32 - 1) (PTX.laneOf L g) := by
    have hl := Nat.mod_lt (g % L.block) (show 0 < 32 by decide)
    refine ⟨hl, ?_⟩
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hl
  obtain ⟨_, _, i, tag, l, _, he'⟩ := elect_ready hX hPeerElect _
    (elect_need_mem (L := L) hPeerElect hMask)
  rw [PTX.Step.warpLane_of_sameWarp (sameWarp_symm hw)] at he'
  have hLocalElect : X.Elect (g, i) tag (2 ^ 32 - 1) inst l := he'
  have hSame := (hX.elect.2.1 _ _ _ _ _ _ _ _ _ hPeerElect hLocalElect (sameWarp_symm hw)).1
  exact prior_election_impossible hpre hX hs ht hwg hTail hSite (hSame ▸ hLocalElect)

private theorem warp_at_output_election {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg0.D}
    {j : Fin 4} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X) (hp : Frame.Pending L X g)
    (hr : PTX.Step.Released L X g)
    (hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .elect j) :
    ∀ h, SameWarp L g h → ∃ q, Frame.Pending L X h ∧ PTX.Step.Released L X h ∧
      Frame.stateAt (Machine.code P L) X h (X.tr h).length = some (some (.wg0 q)) ∧
      q.site = .elect j := by
  have hSound := (hs g hp.1).machine
  have hwg : warpOf L g < 2 := Wg0OutputControl.outputElectionWarp hX hp.1 hSound hTail hSite
  obtain ⟨k, ev, u, hk, he, hbar, hU, hBarSite⟩ :=
    Wg0OutputControl.barrierBeforeElection hpre hX hSound le_rfl hTail hSite
  have hkEq : k = (X.tr g).length - 1 := by omega
  subst k
  have hOrd := Wg0BarrierCount.epiOrdinal hpre hX hSound he hU hBarSite
  obtain ⟨tag, kind⟩ := ev
  cases hbar
  have hsources := OutputPublication.sources hpre hX (fun x hx => (hs x hx).machine) ht
  have hshape := OutputPublication.shape hpre
  obtain ⟨key, hKey, hDone⟩ := tail_barrier_releases he hr
  have hKeyEq := hsources.key hX hshape he hKey
  let phase := 2 * Wg0.blocksOf P L g + 2 + j.val
  rw [hOrd] at hKeyEq
  subst key
  have hMod : (9 + 16 * phase) % 16 = 9 := by omega
  have hDiv : (9 + 16 * phase) / 16 = phase := by omega
  have hReleased : CtaBarrier.Released L.block (X.barriers (g / L.block)) 9 phase := by
    change CtaBarrier.Released L.block (X.barriers (g / L.block))
      ((9 + 16 * phase) % 16) ((9 + 16 * phase) / 16) at hDone
    rw [hMod, hDiv] at hDone
    exact hDone
  intro h hWarp
  have hh : h < L.threads := hWarp.1.2.1
  have hCta : h / L.block = g / L.block := hWarp.1.2.2.symm
  have hCoreWarp (x : Nat) : warpOf L x = x % L.block / 32 := by
    simp [warpOf, tidOf_eq hpre, hpre.block]
  have hGt : g % L.block / 32 < 2 := hCoreWarp g ▸ hwg
  have hHt : h % L.block / 32 < 2 := hWarp.2 ▸ hGt
  have hw : warpOf L h < 2 := (hCoreWarp h).symm ▸ hHt
  have hWg : wgOf L g = 0 := by
    unfold wgOf
    rw [tidOf_eq hpre, ← hpre.block]
    omega
  have hWh : wgOf L h = 0 := by
    unfold wgOf
    rw [tidOf_eq hpre, ← hpre.block]
    omega
  have hSoundPeer := (hs h hh).machine
  have hNoExit : ∀ i exTag, X.get (h, i) ≠ some ⟨exTag, .exit⟩ := by
    intro i exTag hExit
    have hEnd := Wg0OutputVisits.doneAtExit hX hSoundPeer ht hWh hExit rfl
    obtain ⟨k, hKi, q, e, hQ, hQSite, he', hKind⟩ :=
      Wg0OutputVisits.barrierBeforeDone hpre hX hh hSoundPeer hWh hEnd j
    obtain ⟨barTag, knd⟩ := e
    cases hKind
    obtain ⟨q', hQ', hQ'Site⟩ := election_after_barrier hw he' hQ hQSite
    have hMissing := peer_election_missing hpre hX hs ht hWarp hWg hTail hSite hQ' hQ'Site
    have hILt : i < (X.tr h).length := len_of_get hExit
    omega
  have hCtaLt := NamedBar.cta_lt hp.1
  have hb : 0 < L.block := by rw [hpre.block]; decide
  have hIdx : h % L.block < L.block := Nat.mod_lt _ hb
  have hMember : h % L.block / 32 ∈ OutputPublication.stagingWarps :=
    Finset.mem_range.mpr (by omega)
  have hRebuild : g / L.block * L.block + h % L.block = h := by
    rw [← hCta, Nat.mul_comm]
    exact Nat.div_add_mod h L.block
  obtain ⟨v, vt, hV, hVBar, hVOrd, hVKey⟩ :=
    hsources.member_key hX hshape hCtaLt hReleased hIdx hMember
      (fun i t => by rw [hRebuild]; exact hNoExit i t)
  rw [hRebuild] at hV
  obtain ⟨h', b⟩ := v
  change h' = h at hV
  subst h'
  have hRow : Wg0.blocksOf P L h = Wg0.blocksOf P L g := by
    simp [Wg0.blocksOf, Wg0.eOf, ctaidY, ctaOf, hCta]
  obtain ⟨q, hQ, hQSite⟩ := Wg0BarrierCount.epiSite_of_ordinal hpre hX hSoundPeer ht
    hVBar rfl (by rw [hRow]; exact hVOrd)
  obtain ⟨q', hQ', hQ'Site⟩ := election_after_barrier hw hVBar hQ hQSite
  have hMissing := peer_election_missing hpre hX hs ht hWarp hWg hTail hSite hQ' hQ'Site
  have hBLt : b < (X.tr h).length := len_of_get hVBar
  have hLen : b + 1 = (X.tr h).length := by omega
  have hbLast : b = (X.tr h).length - 1 := by omega
  subst b
  rw [hLen] at hQ'
  have hPend : Frame.Pending L X h := by
    refine ⟨hh, ?_, ?_⟩
    · rintro ⟨_, _, hCan⟩
      obtain ⟨i, s, tg, _, hi, _⟩ := hX.clc.canceled_has_issue hCan
      exact GlobalWrites.no_clc (i := i) (s := s) (tg := tg) hX hi
    · intro exTag hLast
      apply hNoExit ((X.tr h).length - 1) exTag
      simpa only [Execution.get, List.getLast?_eq_getElem?] using hLast
  have hVRel : CtaBarDone L X (h / L.block) (9 + 16 * phase) := by
    rw [hCta]
    exact hDone
  exact ⟨q', hPend, NamedBar.released_of_key hX.ctaBar rfl hVBar hVKey hVRel, hQ', hQ'Site⟩

/-- A released softmax lane at an output election can issue that whole warp election. -/
theorem softmax_election_extension {mem0 : Mem0} {X : Execution} {g : Nat} {d : Wg0.D} {j : Fin 4}
    (hpre : Pre P L mem0) (hs : SoundThreads P L) (hX : Consistent L kernel Assumptions.all mem0 X)
    (ht : Frame.Tracked (Machine.code P L) X) (hub : ¬ HasUb X) (hp : Frame.Pending L X g)
    (hr : PTX.Step.Released L X g)
    (hTail : Frame.stateAt (Machine.code P L) X g (X.tr g).length = some (some (.wg0 d)))
    (hSite : d.site = .elect j) :
    ∃ Y, Consistent L kernel Assumptions.all mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  softmax_election_batch hpre hs hX hp.1 hub
    (warp_at_output_election hpre hX hs ht hp hr hTail hSite)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Progress
