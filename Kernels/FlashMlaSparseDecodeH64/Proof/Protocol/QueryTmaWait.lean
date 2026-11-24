-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.RawReadyCounts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Protocol.MbarOneShot
import Lemmas.Protocol.PairTmaRing.Order
import Mathlib.Data.Fintype.EquivFin

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # The actual query wait observes every tile's tensor completion -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem tile_spec_inj (g : Nat) {a b : Fin 8}
    (h : MmaDataTrace.queryTmaSpec P L g a = MmaDataTrace.queryTmaSpec P L g b) : a = b := by
  have haddr := congrArg (fun s : TensorCopy.Spec => s.sharedBase.addr) h
  simp only [MmaDataTrace.queryTmaSpec, Wg1Mma.qDstOff] at haddr
  exact Fin.ext (by omega)

/-- The successful phase-zero query wait observes the actual notification of each tile issued
by its elected producer. All eight completion records are needed to balance the 65536 bytes. -/
theorem actual_tile_observed {g t w tag : Nat} {tile : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hissue : X.TensorIssue (g, t) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile))
    (hwait : X.get (g, w) = some
      ⟨tag, .wait (QueryTmaRecords.object L (ctaOf L g)) 0 true true .cta⟩) :
    AsyncObserved X (g, t) (.notify .load) (g, w) true .cta := by
  classical
  let cta := ctaOf L g
  let m := QueryTmaRecords.object L cta
  let log := X.objects m
  have hfirst := QueryTmaRecords.actual_init_first (cta := cta) hpre hX hs
  have hni : NoInval log := objects_single_lifetime hX m
  have hchecked : CheckedLog log := X.objects_checked hX m
  have haction : objectAction X X.async m (.thread (g, w)) = some (.pollParity 0 true) := by
    simp [objectAction, hwait, m, cta]
  obtain ⟨k, r, hr, hrid, hra⟩ := MbarOneShot.Hist.record_of_action hX haction
  have hrf := PairTmaRing.poll_clean hX hfirst hni r (List.mem_of_getElem? hr) ⟨_, _, hra⟩
  have hreply := ((hX.tma.2.2.1 m).2.1 r (List.mem_of_getElem? hr)).2 0 true hra hrf
  obtain ⟨st, parity, hst, hpar, _, hcompleted⟩ := hchecked.okPoll hr hreply
  obtain ⟨rfl, _⟩ := Action.pollParity.inj (hpar.symm.trans hra)
  have hpos : 0 < st.phase := by omega
  let phase := st.phase - 1
  have ho : observedAt log k = some phase := by
    change observedAt (X.objects m) k = some phase
    simp only [observedAt, hr, Option.bind_some, hcompleted, ite_eq_left hpos, phase]
  obtain ⟨C, hmem, hcard⟩ := transaction_completion_count
    (arriveBytes := 65536) (completionBytes := 8192) (completions := 8)
    (q := phase) (by decide) (by decide) hchecked hni
    (fun s hmem _ c tx ha => by
      obtain ⟨hc, htx, _⟩ := QueryTmaRecords.actual_arrival_record hpre hX hs hmem ha
      exact ⟨hc, htx⟩)
    (fun s hs' _ n ha => (QueryTmaRecords.actual_completion_source hpre hX hs hs' ha).1)
    (fun _ _ _ hs' => PairTmaRing.expected_of_init hX hfirst hni hs')
    (objects_no_pending_increment hX m)
    (List.getElem?_eq_some_iff.mp hr).1.le hst (by dsimp [phase]; omega)
  obtain ⟨leader, hleader⟩ :=
    Wg1MmaLeader.cta_issuer (cta := cta) hpre hX (fun g hg => (hs g hg).machine)
  obtain ⟨_, hget⟩ := hissue
  have hm : (MmaDataTrace.queryTmaSpec P L g tile).mbar = m := by
    simp [MmaDataTrace.queryTmaSpec, Wg1Mma.qTmaAddr_eq, m, cta]
  obtain ⟨_, dq, tile', hstate, hdq, hspec⟩ :=
    QueryTmaRecords.actual_issue_source hpre hX hs hget rfl hm
  have hsame : tile' = tile := tile_spec_inj g hspec.symm
  subst tile'
  have hg := hleader g t dq rfl hstate (by rw [hdq]; simp)
  have hrecords (a : C) :
      ∃ (r' : Record Ref) (j : Nat) (e : Event) (d : Wg1Mma.D) (tile : Fin 8),
        log[a.val]? = some r' ∧ r'.action = .completeTx 8192 ∧ r'.fault = none ∧
        phaseAt log a.val = some phase ∧ r'.id = .async (g, j) (.notify .load) ∧
        X.get (g, j) = some e ∧
        Frame.stateAt (Machine.code P L) X g j = some (some (.mma d)) ∧ d.site = .qLoad tile := by
    obtain ⟨_, r', hr', ha, hf, hp⟩ := (hmem a.val).mp a.property
    obtain ⟨_, g', j, e, _, _, d, tile, hid, he, _, hc, hd, hsite, _⟩ :=
      QueryTmaRecords.actual_completion_source hpre hX hs (List.mem_of_getElem? hr') ha
    have hg' := hleader g' j d hc hd (by rw [hsite]; simp)
    have hthread := hg'.trans hg.symm
    rw [hthread] at hid he hd
    exact ⟨r', j, e, d, tile, hr', ha, hf, hp, hid, he, hd, hsite⟩
  choose rec pos ev state kind hrec hact hfault hphase hid hget' hstate' hsite using hrecords
  have hinj : Function.Injective kind := by
    intro a b hab
    have hsame := QueryTmaSites.load_site_unique (hget' a) (hget' b) (hstate' a) (hstate' b)
      (hsite a) (by rw [hab]; exact hsite b)
    apply Subtype.ext
    have hidEq : (rec a).id = (rec b).id := by rw [hid a, hid b, hsame]
    exact object_record_index_unique hX.tma.2.2.1 (hrec a) (hrec b) hidEq
  have hcard' : Fintype.card ↥C = Fintype.card (Fin 8) := by simpa using hcard
  have hsurj := ((Fintype.bijective_iff_injective_and_card kind).mpr ⟨hinj, hcard'⟩).2
  obtain ⟨a, ha⟩ := hsurj tile
  have hposEq := QueryTmaSites.load_site_unique (hget' a) hget (hstate' a) hstate
    (hsite a) (by rw [ha]; exact hdq)
  have hon := ((hX.tma.2.2.1 m).2.1 (rec a) (List.mem_of_getElem? (hrec a))).1
  rw [hid a, hposEq, hact a] at hon
  have hbefore := MbarRing.Slot.updateBeforeWait_of_phase hchecked hni (hrec a) (hfault a)
    hr hrf hreply (hphase a) ho
  rw [hid a, hposEq, hrid] at hbefore
  exact PairTmaRing.tensorObserved_of_notified hX hon hwait hbefore

/-- The actual tile witness applies to the tracked interface. -/
theorem tile_observed {g t w tag : Nat} {tile : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (_hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (_ht : Frame.Tracked (Machine.code P L) X)
    (hissue : X.TensorIssue (g, t) (P.param1Base + Wg1Mma.qMapOff)
      (MmaDataTrace.queryTmaSpec P L g tile))
    (hwait : X.get (g, w) = some
      ⟨tag, .wait (QueryTmaRecords.object L (ctaOf L g)) 0 true true .cta⟩) :
    AsyncObserved X (g, t) (.notify .load) (g, w) true .cta :=
  actual_tile_observed hpre hX (fun _ hg => Machine.code_sound hpre hg) hissue hwait

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaWait
