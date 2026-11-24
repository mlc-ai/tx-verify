-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilityOldWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvProbabilityLaterWrites
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.PvCausalCut
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Lemmas.Tcgen05.MmaObservedReads
import Lemmas.Order.Order

@[expose] public section

/-! # Actual reads-from for the shared probabilities consumed by PV -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace Protocol Protocol.GemmRing Protocol.PvProbabilitySource
open MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem competing_probability_at_cut {g i consumer cut h j : Nat}
    {d : Wg1Mma.D} {issue : Fin 8} {w : Wg0.D} {e : Event} {site : Fin 4}
    {a fp : Acc} {bs raw : List Byte} {other : Ref}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hCut : PvCausalCut.Cut P L X consumer cut d.i) (hCta : ctaOf L g = ctaOf L consumer)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    (hh : h = probabilityLane L (ctaOf L g) row ⟨pvSlot issue k, by unfold pvSlot; omega⟩)
    (he : X.get (h, j) = some e)
    (hw : Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)))
    (hBlock : w.block = d.i) (hSite : w.site = .pStore site)
    (hSiteIndex : site.val = pvSlot issue k % 32 / 8)
    (hSub : w.sub = pvSlot issue k / 2 % 4) (hWrite : X.Writes (h, j) a bs)
    (hOther : X.MemWrites other fp raw) :
    let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩
    let index := 2 * (row.val * 16 + k.val) + b.val
    fp.Covers loc → X.MmaFootprint (g, i) false index loc →
      other = .thread (h, j) ∨ ByteCausality L X loc other (.thread (h, j)) ∨
        ByteCausality L X loc (.async (g, i) (.mmaRead false index)) other := by
  dsimp only
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let loc : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  intro hCover hFoot
  change fp.Covers loc at hCover
  change X.MmaFootprint (g, i) false index loc at hFoot
  obtain ⟨hl, hu⟩ := probability_byte_bounds L row slot b
  obtain ⟨s, t, rfl, hwr, hc, hWg, _, _⟩ :=
    Wg0PeerWrites.actual_covered_write hpre hX hs hOther hCover rfl hl hu
  have hSc : ctaOf L s = ctaOf L g := hc.symm
  have hGet := hwr.choose_spec
  have hS := Frame.lt_of_get hX hGet
  have hH : ctaOf L h = ctaOf L g :=
    hh.symm ▸ (probabilityLane_coords hpre (ctaOf L g) row slot).1
  have future {n : Nat} (hn : d.i < n)
      (hCount : n / 2 + 1 ≤ okPolls (qk L (ctaOf L s) (rawSlot n)) ((X.tr s).take t)) :
      ByteCausality L X loc (.async (g, i) (.mmaRead false index)) (.thread (s, t)) := by
    obtain ⟨_, _, wait, hlt, hFinish, hBefore⟩ :=
      prior_pv_read_finished_of_count hpre hX hs hi hd hsite hn hGet hWg hSc.symm hCount
    exact completed_mma_source_before_store hi hFoot hFinish rfl hlt hBefore rfl hwr hCover
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X s t = some none
  · obtain ⟨p, hp, q, f, hf, hq, hData, hNonBar, hBad⟩ :=
      dismissed_softmax_guard hpre hX hs hWg hGet hDismiss
    have hNotEpi : q.site.inEpilogue = false := by
      cases hepi : q.site.inEpilogue
      · rfl
      · have hTooEarly := Wg0PeerWrites.body_write_before_epilogue hpre hX hs hwr hCover
          rfl hl hu hDismiss hq hepi
        omega
    have hb : d.i < q.block := by
      by_contra! hEarlier
      exact PvCausalCut.no_earlier_dismissal hpre hX hs hCut (hSc.trans hCta)
        hf hq hData hNonBar hNotEpi hEarlier hBad
    have hCount := PvCausalCut.guard_qk_count hpre hX hs hf hq hData hNotEpi
    exact .inr (.inr (future hb (hCount.ge.trans
      (List.take_sublist_take_left hp.le).countP_le)))
  · obtain ⟨z, _, hz, _⟩ :=
      RingSourceSites.fired_at_followed hX (hs s hS).machine hDismiss hGet (by simp)
    rcases competing_followed_base_or_later hpre hX hs he hH hw hSite row slot b hz hwr hCover with
      hOld | ⟨q, hq, hqSite⟩
    · exact .inr (.inl (.direct (.inl hOld)))
    have hTrace := (hs s hS).machine.produces (hX.thr s hS)
    rcases hqSite with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩
    · have hCount := Wg0GemmTrace.composed_exchange_qk_count hpre hTrace hq hr
      exact .inr (.inr (future (hBlock ▸ hb) hCount.ge))
    · rcases lt_or_eq_of_le hb with hLater | hSame
      · have hCount := (Wg0GemmTrace.composed_probability_counts hpre hTrace hq ⟨r, hr⟩).2
        exact .inr (.inr (future (hBlock ▸ hLater) hCount.ge))
      · obtain ⟨hLane, hrVal, hqSub⟩ := probability_store_coordinates hpre hX
          (hs s hS).machine hwr hq hr row slot b hCover
        have hLane' : s = h := hLane.trans hh.symm
        clear hLane
        subst s
        have hrEq : r = site := Fin.ext (hrVal.trans hSiteIndex.symm)
        subst r
        have hj := Wg0ProbabilityUnique.actual_write_unique hpre hX (hs h hS).machine
          hWrite hwr hw hq hSite hr hSame (hSub.trans hqSub.symm)
        exact .inl (congrArg (fun n => Ref.thread (h, n)) hj.symm)

/-- Each observed PV A byte reads from its own block's selected packed probability write. -/
theorem pv_probability_byte_source {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    {value : Option Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    (hr : X.MmaRead (g, i) false (2 * (row.val * 16 + k.val) + b.val)
      ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩ value) :
    let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
    let h := probabilityLane L (ctaOf L g) row slot
    let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
    ∃ j w e u, X.get (h, j) = some e ∧
      Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)) ∧
      w.block = d.i ∧ w.site = .pStore site ∧ w.sub = slot.val / 2 % 4 ∧
      (Wg0.code P L h).toMachine.Fired (some w) e (some u) ∧
      X.rf (.async (g, i) (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))) 0 =
        some (.thread (h, j)) := by
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let h := probabilityLane L (ctaOf L g) row slot
  let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
  let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  let reader : Ref := .async (g, i) (.mmaRead false index)
  obtain ⟨j, w, e, u, a, bs, he, hw, hBlock, hSite, hSub, hFired, hMem, _, hFoot, hProxy⟩ :=
    selected_byte_before_pv hpre hX hs ht hi hd hsite row k b
  obtain ⟨hWrite, hCover⟩ :=
    selected_write_covers hpre he hSite hFired row slot b rfl rfl hSub hMem
  have hCta : ctaOf L h = ctaOf L g := (probabilityLane_coords hpre (ctaOf L g) row slot).1
  let write : Ref := .thread (h, j)
  let acc : Acc := {loc := l, size := 1}
  have hRead : X.MemReads reader acc [value] := ⟨value, hr, rfl, rfl⟩
  have hAsync : AsyncCovers X (g, i) (.mmaRead false index) l :=
    ⟨acc, false, hRead.intent, Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  have hBefore : ByteCausality L X l write reader := .direct ⟨hAsync, .inl hProxy⟩
  have hz : 0 < acc.size := Nat.zero_lt_succ 0
  have hZero : acc.loc.at 0 = l := by simp [acc, Loc.at]
  have hHidden := hX.hidden reader acc [value] 0 write a bs hRead hz hMem
    (by rw [hZero]; exact hCover) (by rw [hZero]; exact hBefore)
  have hRf : X.rf reader 0 = some write := by
    cases hSource : X.rf reader 0 with
    | none => rw [hSource] at hHidden; exact hHidden.elim
    | some source =>
      have hSourceOk := (hX.rf reader acc [value] hRead).2 0 hz
      rw [hSource] at hSourceOk hHidden
      obtain ⟨fp, raw, hSrc, hCovered, _⟩ := hSourceOk
      rw [hZero] at hCovered hHidden
      rcases competing_older_or_later hpre hX hs ht he hCta hw hSite row slot b hSrc hCovered with
        older | ⟨⟨s, t⟩, q, rfl, hqWrite, hq, _, hqCta, hClass⟩
      · exact (hHidden older).elim
      have hQ := Frame.lt_of_get hX hqWrite.choose_spec
      have later (hb : d.i < q.block)
          (hqSite : (∃ k : Fin 8, q.site = .exchStore k) ∨ (∃ k : Fin 4, q.site = .pStore k)) :
          False := by
        obtain ⟨_, wait, hlt, hFinish⟩ :=
          prior_pv_read_finished (index := index) hpre hX hs ht hi hd hsite hb
            hqWrite.choose_spec hq hqSite hqCta.symm
        have hGet : ∃ wt m parity scope,
            X.get (s, wait) = some ⟨wt, .wait m parity true true scope⟩ := by
          rcases hFinish with ⟨kind, hp, _⟩ | ⟨scope, ⟨_, m, _, htObs⟩, _⟩
          · cases kind with
            | cpAsync => cases hp
            | bulk mode => cases mode <;> cases hp
          · obtain ⟨wt, parity, hGet⟩ := htObs.1
            exact ⟨wt, m, parity, scope, hGet⟩
        obtain ⟨wt, m, parity, scope, hGet⟩ := hGet
        have hPo : po X (s, wait) (s, t) := po_of_source_not_access rfl hlt
          (PTX.len_of_get hqWrite.choose_spec) (by rw [hGet]; rfl)
        have hFuture := completed_mma_source_before_store (f := (s, t)) hi hFoot hFinish rfl hlt
          (.single (.inl hPo)) (show l.space = .shared from rfl) hqWrite hCovered
        exact hX.noFuture reader acc [value] 0 _ hRead hz hSource
          (by rw [hZero]; exact hFuture)
      rcases hClass with ⟨grp, hGrp, hb⟩ | ⟨qsite, hqSite, hb⟩
      · exact (later (hBlock ▸ hb) (.inl ⟨grp, hGrp⟩)).elim
      rcases lt_or_eq_of_le hb with hlater | hSame
      · exact (later (hBlock ▸ hlater) (.inr ⟨qsite, hqSite⟩)).elim
      obtain ⟨hS, hK, hQSub⟩ :=
        probability_store_coordinates hpre hX (hs s hQ).machine hqWrite hq hqSite
          row slot b hCovered
      change s = h at hS
      subst s
      have hsiteEq : qsite = site := Fin.ext hK
      subst qsite
      have hJ := Wg0ProbabilityUnique.write_unique hpre hX (hs h hQ).machine ht hWrite hqWrite
        hw hq hSite hqSite hSame (hSub.trans hQSub.symm)
      cases hJ
      rfl
  exact ⟨j, w, e, u, he, hw, hBlock, hSite, hSub, hFired, hRf⟩

/-- Causal induction supplies all probability writes needed by this observed PV issue. -/
theorem actual_pv_probability_byte_source {g i consumer cut : Nat} {d : Wg1Mma.D} {issue : Fin 8}
    {value : Option Byte}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hCut : PvCausalCut.Cut P L X consumer cut d.i) (hCta : ctaOf L g = ctaOf L consumer)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (row : Fin 128) (k : Fin 16) (b : Fin 2)
    (hr : X.MmaRead (g, i) false (2 * (row.val * 16 + k.val) + b.val)
      ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) (pvSlot issue k) b.val⟩ value) :
    let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
    let h := probabilityLane L (ctaOf L g) row slot
    let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
    ∃ j w e u, X.get (h, j) = some e ∧
      Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)) ∧
      w.block = d.i ∧ w.site = .pStore site ∧ w.sub = slot.val / 2 % 4 ∧
      (Wg0.code P L h).toMachine.Fired (some w) e (some u) ∧
      X.rf (.async (g, i) (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))) 0 =
        some (.thread (h, j)) := by
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let h := probabilityLane L (ctaOf L g) row slot
  let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
  let l : Loc := ⟨.shared, ctaOf L g, pLinearByte L (row.val % 64) slot.val b.val⟩
  let index := 2 * (row.val * 16 + k.val) + b.val
  let reader : Ref := .async (g, i) (.mmaRead false index)
  obtain ⟨j, w, e, u, a, bs, he, hw, hBlock, hSite, hSub, hFired, hMem, _, hFoot, hProxy⟩ :=
    selected_byte_before_pv_of_followed hpre hX hs hi hd hsite row k b (by
      intro a tag
      dsimp only
      intro ha hCount
      have hCc : ctaOf L h = ctaOf L g :=
        (probabilityLane_coords hpre (ctaOf L g) row slot).1
      have hWG : wgOf L h = 0 := by
        unfold wgOf
        have hl := slot.isLt
        simp only [h, probabilityLane, tidOf_eq hpre, hpre.block]
        omega
      exact PvCausalCut.publication_followed hpre hX hs hCut (hCc.trans hCta)
        hWG (by rwa [hCc]) (by rwa [hCc]))
  obtain ⟨hWrite, hCover⟩ :=
    selected_write_covers hpre he hSite hFired row slot b rfl rfl hSub hMem
  let write : Ref := .thread (h, j)
  let acc : Acc := {loc := l, size := 1}
  have hRead : X.MemReads reader acc [value] := ⟨value, hr, rfl, rfl⟩
  have hAsync : AsyncCovers X (g, i) (.mmaRead false index) l :=
    ⟨acc, false, hRead.intent, Acc.covers_at (k := 0) (show 0 < 1 by decide)⟩
  have hBefore : ByteCausality L X l write reader := .direct ⟨hAsync, .inl hProxy⟩
  have hz : 0 < acc.size := Nat.zero_lt_succ 0
  have hZero : acc.loc.at 0 = l := by simp [acc, Loc.at]
  have hHidden := hX.hidden reader acc [value] 0 write a bs hRead hz hMem
    (by rw [hZero]; exact hCover) (by rw [hZero]; exact hBefore)
  have hRf : X.rf reader 0 = some write := by
    cases hSource : X.rf reader 0 with
    | none => rw [hSource] at hHidden; exact hHidden.elim
    | some source =>
      have hSourceOk := (hX.rf reader acc [value] hRead).2 0 hz
      rw [hSource] at hSourceOk hHidden
      obtain ⟨fp, raw, hSrc, hCovered, _⟩ := hSourceOk
      rw [hZero] at hCovered hHidden
      rcases competing_probability_at_cut hpre hX hs hCut hCta hi hd hsite row k b
          rfl he hw hBlock hSite rfl hSub hWrite hSrc hCovered hFoot with
        rfl | older | future
      · rfl
      · exact (hHidden older).elim
      · exact (hX.noFuture reader acc [value] 0 _ hRead hz hSource
          (by rw [hZero]; exact future)).elim
  exact ⟨j, w, e, u, he, hw, hBlock, hSite, hSub, hFired, hRf⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
