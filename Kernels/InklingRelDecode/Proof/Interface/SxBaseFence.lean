-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ScFence

@[expose] public section

/-!
# An early event of the common start before every tensor copy's write

`base_before_copy` (`ScFence.lean`) for any event of the common start with at most one
barrier-0 event before it that is no barrier-0 event itself: the allocation's store of the base
word (no barrier-0 event before it) as well as the reads of the word (one). `early_before_late`:
such an event is before every event of a thread of its CTA past the common start;
`early_before_copy`: it is before a `fence.proxy.async` that is before the issue of every tensor
copy of the CTA (`ProxyBefore`). The proofs are those of `base_read_before_late` and
`base_before_copy` with the read's two facts (`baseRead_facts`) as hypotheses.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Bar

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **An event of the common start with at most one barrier-0 event before it is before every
event of a thread of its CTA whose state is past the common start.** -/
theorem early_before_late (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    {h kr u kc : Nat} {s : TSt} (hsame : SameCta L h u) (hr : kr < (X.tr h).length)
    (hc1 : ((X.tr h).take kr).countP (Execution.isBarId 0) ≤ 1)
    (hn1 : ∀ ev, (X.tr h)[kr]? = some ev → ¬ Execution.isBarId 0 ev = true)
    (hσ : St Q L X u kc = some (some s)) (hl : ¬ tLb s < 2)
    (hkc : kc < (X.tr u).length) : baseCausality L X (h, kr) (u, kc) := by
  have h2 : 2 ≤ ((X.tr u).take kc).countP (Execution.isBarId 0) :=
    bar0_ordinal_two hX hS hkc.le hσ hl
  obtain ⟨j1, pc1, hj1, hf, hord⟩ := arrival_before hX hS ht (h := u) (k := kc) (r := 1)
    (by omega) le_rfl
  exact bar0_chain hpre hX hS ht hsame hf (by omega) (by omega) hr hn1 hj1 hkc

/-- **`ProxyBefore` for the issue of every tensor copy**: an early event of the common start is
before a `fence.proxy.async` that is before the copy's issue, for every byte of the CTA's shared
memory. -/
theorem early_before_copy (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (ht : Frame.Tracked (code L Q) X)
    (hE : Bar1Exits L X) (hRR : RoleReads L X) {h kr : Nat} (hr : kr < (X.tr h).length)
    (hc1 : ((X.tr h).take kr).countP (Execution.isBarId 0) ≤ 1)
    (hn1 : ∀ ev, (X.tr h)[kr]? = some ev → ¬ Execution.isBarId 0 ev = true)
    {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a sp⟩) (hcta : i.1 / L.block = h / L.block)
    (hh : h < L.threads) {l : Loc} (hls : l.space = .shared) (hlc : l.cta = h / L.block) :
    ProxyBefore L X (h, kr) i l := by
  have hgi : i.1 < L.threads := Frame.lt_of_get hX he
  have hsame : SameCta L h i.1 := ⟨hh, hgi, hcta.symm⟩
  have hli : i.2 < (X.tr i.1).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simpa using this
  have hcover : AsyncFenceCovers L (some (.shared .cta)) i.1 l := ⟨hls, by rw [hlc, hcta]⟩
  rcases copy_event_stateW hpre hX hS ht hgi he ⟨a, sp, rfl⟩ with
    ⟨d, hσ, j, hj, hsite, -⟩ | ⟨d, P, hσ, -⟩
  · -- the prologue's copy: after its own `fnc0`
    have hpast : PastPro ProA.Site.fnc0 (.d (.pro d)) := by
      show ProA.Site.fnc0.pc < d.site.pc
      rw [hsite]
      exact ptc_pc_gt j hj
    obtain ⟨j0, hj0, d0, hσ0, hs0⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc0 h' a b) (by decide) (by decide) i.2 _ hσ hpast
    have hj0' : j0 < (X.tr i.1).length := by omega
    obtain ⟨e0, he0⟩ : ∃ e0, X.get (i.1, j0) = some e0 :=
      ⟨_, List.getElem?_eq_getElem hj0'⟩
    obtain ⟨pcf, hev⟩ := fnc_event hX hS hT hgi he0 hσ0 (Or.inl hs0)
    have hfence : X.IsProxyFence (i.1, j0) (.async (some (.shared .cta))) none :=
      ⟨pcf, by rw [he0, hev]⟩
    refine ⟨(i.1, j0), _, _, hfence, hgi, hcover, ⟨hgi, hgi, rfl⟩, ?_, ?_⟩
    · exact early_before_late hpre hX hS ht hsame hr hc1 hn1 hσ0 (by simp [tLb_pro])
        (by omega)
    · exact .single (.inl (po_of_source_not_access (X := X) rfl hj0 hli (by
        rw [he0, hev]; rfl)))
  · -- the loader's copy: after the barrier-1 arrival of ordinal 0, which follows `fnc1`
    have hwk : 128 ≤ i.1 % L.block := by
      have := (cls_inv i.2 _ hli.le hσ).not.mp (by exact fun h => h)
      omega
    have hbk : L.block = 256 := hpre.block
    have hblk : 0 < L.block := by omega
    have hb1 : 1 ≤ b1N X i.1 i.2 := by
      obtain ⟨-, t, -, h2, -, -, -, -⟩ := phase_inv hpre hX hS hRR i.2 _ hli.le hσ
      rw [h2]
      have : 1 ≤ (tPh (.w (.loader d P))).2 := by
        simp only [tPh]
        cases hs : d.site <;> simp [wPh, hs]
      omega
    obtain ⟨j0, pcf, hj0, hf0, hc0⟩ := arrival1_before hpre hX (h := i.1) (k := i.2) (r := 0)
      (by omega)
    have hp : j0 + 1 < (X.tr i.1).length := by omega
    have hg0 : i.1 / L.block * L.block < L.threads :=
      lt_of_le_of_lt (Nat.div_mul_le_self i.1 L.block) hgi
    have hd0 : i.1 / L.block * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
    have hcta0 : i.1 / L.block * L.block / L.block = i.1 / L.block := Nat.mul_div_cancel _ hblk
    obtain ⟨i0, pc0, hf00, hc00⟩ := bar1_has hpre hX hE (g := i.1 / L.block * L.block)
      (h := i.1) hf0 hp hcta0
    have hc00' : ((X.tr (i.1 / L.block * L.block)).take i0).countP (Execution.isBarId 1) = 0 := by
      rw [hc00]
      exact hc0
    have he00 : X.get (i.1 / L.block * L.block, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hf00
    have hli0 : i0 < (X.tr (i.1 / L.block * L.block)).length :=
      (List.getElem?_eq_some_iff.mp he00).1
    have hprev : i0 = 0 ∨ ∃ k', i0 = k' + 1 ∧ TT Q L X (i.1 / L.block * L.block, k') := by
      rcases Nat.eq_zero_or_pos i0 with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ⟨i0 - 1, by omega, ?_⟩
        have := ht (i.1 / L.block * L.block) (i0 - 1 + 1) hg0
        exact this
    obtain ⟨s0, hσ0⟩ := state_of_prev hS hX he00 bar_not_ub hprev
    obtain ⟨dd, rfl, hb1'⟩ := dphase_inv hpre hX hS hd0 i0 s0 hli0.le hσ0
    have hbar := event_b1 hpre hX hS he00 hσ0
    rw [isBarId_bar] at hbar
    have h0 : (dPh dd).2 = 0 := by rw [← hb1']; exact hc00'
    obtain ⟨dd', rfl, hs⟩ := dB1_phase0 h0 hbar.symm
    obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_pastPro (X := X)
      (fun h' a b => ProA.next_cross_fnc1 h' a b) (by decide) (by decide) i0 _ hσ0
      (by show ProA.Site.fnc1.pc < dd'.site.pc; rw [hs]; decide)
    have hj1' : j1 < (X.tr (i.1 / L.block * L.block)).length := by omega
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (i.1 / L.block * L.block, j1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem hj1'⟩
    obtain ⟨pcf1, hev⟩ := fnc_event hX hS hT hg0 he1 hσ1 (Or.inr hs1)
    have hfence : X.IsProxyFence (i.1 / L.block * L.block, j1) (.async (some (.shared .cta)))
        none := ⟨pcf1, by rw [he1, hev]⟩
    have hsame0 : SameCta L h (i.1 / L.block * L.block) :=
      ⟨hh, hg0, by rw [hcta0]; exact hcta.symm⟩
    have hcover0 : AsyncFenceCovers L (some (.shared .cta)) (i.1 / L.block * L.block) l :=
      ⟨hls, by rw [hlc, hcta0, hcta]⟩
    refine ⟨(i.1 / L.block * L.block, j1), _, _, hfence, hg0, hcover0,
      ⟨hg0, hgi, by rw [hcta0]⟩, ?_, ?_⟩
    · exact early_before_late hpre hX hS ht hsame0 hr hc1 hn1 hσ1 (by simp [tLb_pro])
        (by omega)
    · exact Bar.bar1_baseCausality hpre hX ⟨hg0, hgi, hcta0⟩ hf00 hf0 hp
        (by rw [hc00, hc0]) hj1 hj0 hli



/-- **`ProxyBefore` for every event of a worker after its first barrier-1 event**: an early event
of the common start is before thread 0's `fence.proxy.async` (`fnc1`), which is before the
worker's barrier-1 arrival of ordinal 0 (the loader branch of `early_before_copy`). -/
theorem early_before_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (ht : Frame.Tracked (code L Q) X)
    (hE : Bar1Exits L X) {h kr : Nat} (hr : kr < (X.tr h).length)
    (hc1 : ((X.tr h).take kr).countP (Execution.isBarId 0) ≤ 1)
    (hn1 : ∀ ev, (X.tr h)[kr]? = some ev → ¬ Execution.isBarId 0 ev = true)
    {i : EvId} (hgi : i.1 < L.threads) (hli : i.2 < (X.tr i.1).length)
    (hb1 : 1 ≤ b1N X i.1 i.2) (hcta : i.1 / L.block = h / L.block)
    (hh : h < L.threads) {l : Loc} (hls : l.space = .shared) (hlc : l.cta = h / L.block) :
    ProxyBefore L X (h, kr) i l := by
  have hbk : L.block = 256 := hpre.block
  have hblk : 0 < L.block := by omega
  obtain ⟨j0, pcf, hj0, hf0, hc0⟩ := arrival1_before hpre hX (h := i.1) (k := i.2) (r := 0)
    (by omega)
  have hp : j0 + 1 < (X.tr i.1).length := by omega
  have hg0 : i.1 / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self i.1 L.block) hgi
  have hd0 : i.1 / L.block * L.block % L.block < 128 := by rw [Nat.mul_mod_left]; omega
  have hcta0 : i.1 / L.block * L.block / L.block = i.1 / L.block := Nat.mul_div_cancel _ hblk
  obtain ⟨i0, pc0, hf00, hc00⟩ := bar1_has hpre hX hE (g := i.1 / L.block * L.block)
    (h := i.1) hf0 hp hcta0
  have hc00' : ((X.tr (i.1 / L.block * L.block)).take i0).countP (Execution.isBarId 1) = 0 := by
    rw [hc00]
    exact hc0
  have he00 : X.get (i.1 / L.block * L.block, i0) = some ⟨pc0, .bar 1 none .sync⟩ := hf00
  have hli0 : i0 < (X.tr (i.1 / L.block * L.block)).length :=
    (List.getElem?_eq_some_iff.mp he00).1
  have hprev : i0 = 0 ∨ ∃ k', i0 = k' + 1 ∧ TT Q L X (i.1 / L.block * L.block, k') := by
    rcases Nat.eq_zero_or_pos i0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨i0 - 1, by omega, ?_⟩
      have := ht (i.1 / L.block * L.block) (i0 - 1 + 1) hg0
      exact this
  obtain ⟨s0, hσ0⟩ := state_of_prev hS hX he00 bar_not_ub hprev
  obtain ⟨dd, rfl, hb1'⟩ := dphase_inv hpre hX hS hd0 i0 s0 hli0.le hσ0
  have hbar := event_b1 hpre hX hS he00 hσ0
  rw [isBarId_bar] at hbar
  have h0 : (dPh dd).2 = 0 := by rw [← hb1']; exact hc00'
  obtain ⟨dd', rfl, hs⟩ := dB1_phase0 h0 hbar.symm
  obtain ⟨j1, hj1, d1, hσ1, hs1⟩ := exists_pastPro (X := X)
    (fun h' a b => ProA.next_cross_fnc1 h' a b) (by decide) (by decide) i0 _ hσ0
    (by show ProA.Site.fnc1.pc < dd'.site.pc; rw [hs]; decide)
  have hj1' : j1 < (X.tr (i.1 / L.block * L.block)).length := by omega
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (i.1 / L.block * L.block, j1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem hj1'⟩
  obtain ⟨pcf1, hev⟩ := fnc_event hX hS hT hg0 he1 hσ1 (Or.inr hs1)
  have hfence : X.IsProxyFence (i.1 / L.block * L.block, j1) (.async (some (.shared .cta)))
      none := ⟨pcf1, by rw [he1, hev]⟩
  have hsame0 : SameCta L h (i.1 / L.block * L.block) :=
    ⟨hh, hg0, by rw [hcta0]; exact hcta.symm⟩
  have hcover0 : AsyncFenceCovers L (some (.shared .cta)) (i.1 / L.block * L.block) l :=
    ⟨hls, by rw [hlc, hcta0, hcta]⟩
  refine ⟨(i.1 / L.block * L.block, j1), _, _, hfence, hg0, hcover0,
    ⟨hg0, hgi, by rw [hcta0]⟩, ?_, ?_⟩
  · exact early_before_late hpre hX hS ht hsame0 hr hc1 hn1 hσ1 (by simp [tLb_pro])
      (by omega)
  · exact Bar.bar1_baseCausality hpre hX ⟨hg0, hgi, hcta0⟩ hf00 hf0 hp
      (by rw [hc00, hc0]) hj1 hj0 hli

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
