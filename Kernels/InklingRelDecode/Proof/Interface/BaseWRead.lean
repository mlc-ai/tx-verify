-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BaseWLate
public import Kernels.InklingRelDecode.Proof.Interface.ScBase

@[expose] public section

/-!
# The base word's read under the tracking up to the base-word stops

`base_read_w`: a read at a base-read state (`BaseReadAt`: `DStart.ld0`, `Worker.ld0`), which is
before both base-word stops, returns the zero word, under the tracking up to those stops
(`WeakTracked`). The writers of a base byte are the allocation's store and the tensor copies into K
slot 0 (`source_class`); a write may be at an event the machines no longer follow (after its
thread's stop). The visible write is the allocation's store by the CTA's thread 0, before its
barrier-0 arrival of ordinal 0 (`allocWr_anchor`). Two facts are premises here (`BaseSources`), each
named for what it says:

* `allocZero`: the allocation's store writes the zero word (`AllocWordZero`);
* `copy`: a read of the base word is before a proxy fence before the issue of every tensor copy
  that writes the read's CTA (`ProxyBefore`).

A thread write at an event its machine does not follow is a write of a thread of the reader's CTA
(`thread_write_cta`) and has its stop, and so two barrier-0 events, before it: the read is causally
before it (`base_read_before_count`), so `noFuture` excludes it as the read's source.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Bar PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The writer facts `base_read_w` takes (see the module comment). -/
structure BaseSources (Q : Params) (L : Launch) (X : Execution) : Prop where
  allocZero : AllocWordZero Q L X
  copy : ∀ {h kr : Nat}, kr < (X.tr h).length → BaseReadAt Q L X h kr →
    ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec}, X.get i = some ⟨pc, .tensorIssue a sp⟩ →
    h < L.threads →
    ∀ {l : Loc}, l.space = .shared → l.cta = h / L.block →
      (∃ x y z dst bs, X.MemWrites (.async i (.write (.load x y z))) dst bs ∧ dst.Covers l) →
      ProxyBefore L X (h, kr) i l

/-- **A write after its thread's stop is after every read of the base word in its CTA.** -/
theorem late_after (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hW : WeakTracked Q L X)
    {h kr u kc : Nat} (hsame : SameCta L h u) (hr : kr < (X.tr h).length)
    (hb : BaseReadAt Q L X h kr) (hkc : kc < (X.tr u).length) (hn : ¬ TT Q L X (u, kc)) :
    baseCausality L X (h, kr) (u, kc) := by
  have hE := earlyTT_of_weak hX hS hW
  have h2 : 2 ≤ ((X.tr u).take kc).countP (Execution.isBarId 0) := by
    by_contra hlt
    exact hn (hE u kc hsame.2.1 (by omega))
  exact base_read_before_count hpre hX hS hE hsame hr hb h2 hkc

/-- **The read of the base word at a base-read state returns the 32-bit zero**, under the tracking
up to the base-word stops and the writer facts `BaseSources`. -/
theorem base_read_w (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X)
    (hB : BaseSources Q L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hget : X.get (g, k) = some ⟨pc, .rd a bs⟩) (hb : BaseReadAt Q L X g k)
    (hloc : a.loc = ⟨.shared, g / L.block, L.sharedBase⟩) (hsz : a.size = 4) :
    bs = (b32 0).toBytes.map some := by
  have hE := earlyTT_of_weak hX hS hW
  have hbk : L.block = 256 := hpre.block
  have hblk : 0 < L.block := by omega
  have hg : g < L.threads := Frame.lt_of_get hX hget
  have hlk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  have hrd : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨pc, hget⟩
  have hlen : bs.length = 4 := by
    have := Consistent.read_length hX hrd
    omega
  have hsh := hpre.sharedRange
  unfold sharedBytes at hsh
  have hg0 : g / L.block * L.block < L.threads :=
    lt_of_le_of_lt (Nat.div_mul_le_self g L.block) hg
  have hl0 : g / L.block * L.block % L.block < 32 := by rw [Nat.mul_mod_left]; omega
  have hlane : laneOf L (g / L.block * L.block) = 0 := by
    simp [laneOf, Nat.mul_mod_left]
  have hcta0 : g / L.block * L.block / L.block = g / L.block := Nat.mul_div_cancel _ hblk
  obtain ⟨hc1, hn1⟩ := baseRead_facts hX hS hlk hb
  obtain ⟨j, pcj, hj, hfj, hordj⟩ := arrival_before' hX hS hE (h := g) (k := k) (r := 0)
    (by omega) (by omega)
  have hp : j + 1 < (X.tr g).length := by omega
  obtain ⟨i0, pc0, hf00, hc00⟩ := bar0_member' hpre hX hS hE hfj hp (by omega)
    (g := g / L.block * L.block) hcta0
  have hc00' : ((X.tr (g / L.block * L.block)).take i0).countP (Execution.isBarId 0) = 0 := by
    rw [hc00]
    exact hordj
  have hprev : i0 = 0 ∨ ∃ k', i0 = k' + 1 ∧ TT Q L X (g / L.block * L.block, k') := by
    rcases Nat.eq_zero_or_pos i0 with h0 | h0
    · exact Or.inl h0
    · refine Or.inr ⟨i0 - 1, by omega, hE _ _ hg0 ?_⟩
      have hle : ((X.tr (g / L.block * L.block)).take (i0 - 1)).countP (Execution.isBarId 0) ≤
          ((X.tr (g / L.block * L.block)).take i0).countP (Execution.isBarId 0) :=
        (List.take_sublist_take_left (by omega)).countP_le
      omega
  obtain ⟨j1, hj1, tm, pc1, col, hσ1, he1⟩ :=
    allocWr_anchor hpre hX hS hT hg0 hl0 hlane hf00 hc00' hprev
  have hcol : (b32 col).toBytes = (b32 0).toBytes := hB.allocZero he1 hσ1
  have hli0 : i0 < (X.tr (g / L.block * L.block)).length := by
    have he00 : X.get (g / L.block * L.block, i0) = some ⟨pc0, .bar 0 none .sync⟩ := hf00
    exact (List.getElem?_eq_some_iff.mp he00).1
  have hj1' : j1 < (X.tr (g / L.block * L.block)).length := by omega
  have hbc : baseCausality L X (g / L.block * L.block, j1) (g, k) :=
    allocStore_baseCausality_read' hpre hX hS hE ⟨hg0, hg, hcta0⟩ hj1' ⟨tm, hσ1⟩ hlk hb
  have hwM : X.MemWrites (.thread (g / L.block * L.block, j1))
      { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 0).toBytes := by
    left
    refine ⟨pc1, ?_⟩
    rw [hcol] at he1
    rw [hcta0] at he1
    exact he1
  refine read_num_cases hlen fun m hm => ?_
  have hl : a.loc.at m = ⟨.shared, g / L.block, L.sharedBase + m⟩ := by
    rw [hloc]
    simp [Loc.at]
  have hwc : ({ loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } : Acc).Covers
      (a.loc.at m) := by
    rw [hl]
    exact ⟨rfl, rfl, by simp, by simp; omega⟩
  have hv : modelCausality L X (a.loc.at m) (.thread (g / L.block * L.block, j1))
      (.thread (g, k)) := .inl <| hbc
  refine read_byte_of_source hX hrd (by omega) hwM hwc hv ?_
  intro r' dst' bytes' hrf hw' hcov'
  have hsp' : dst'.loc.space = .shared := by
    have := hcov'.1
    rw [hl] at this
    exact this.symm
  rcases r' with ⟨g', k'⟩ | ⟨i, p⟩
  · obtain ⟨pc', hget'⟩ : ∃ pc', X.get (g', k') = some ⟨pc', .wr dst' bytes'⟩ := by
      rcases hw' with ⟨pc', hh⟩ | ⟨old, pc', hh⟩
      · exact ⟨pc', hh⟩
      · exact absurd hh (no_rmw hX)
    have hg' : g' < L.threads := Frame.lt_of_get hX hget'
    by_cases hTT : TT Q L X (g', k')
    · obtain ⟨s', hσ'⟩ := event_state_at hS hX hget' (by intro pc f h; cases h) hTT
      have hTW := thread_write_class hpre hX hS hg' hget' hσ' hsp'
      obtain ⟨-, hc', hlo, hhi⟩ := hcov'
      rw [hl] at hlo hhi
      simp only at hlo hhi
      cases hTW with
      | stq hi hs hl' hz' h1 h2 =>
        rw [hl'] at hlo hhi
        simp only [hz'] at hhi
        simp only at hlo hhi
        omega
      | st8 hs ha hb' =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
      | st9_0 hs ha hb' =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
      | st9_1 hs ha hb' =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
      | store10 hs ha =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
      | @allocWr d' _ _ hs ha hb' =>
        right; right
        obtain ⟨site, tm'⟩ := d'
        simp only at hs
        subst hs
        have hby : bytes' = (b32 0).toBytes := hB.allocZero hget' hσ'
        subst ha hby
        rw [hl]
        simp only [wbyte, toBytes_b32]
        have hs' : L.sharedBase + m - L.sharedBase = m := by omega
        rw [hs']
        rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> rfl
      | stTab hs ha hb' =>
        rw [ha] at hlo hhi
        simp only [EvD.wordAcc] at hlo hhi
        omega
    · -- a write at an event the machines no longer follow
      left
      have hk' : k' < (X.tr g').length := (List.getElem?_eq_some_iff.mp hget').1
      have hcta' : dst'.loc.cta = g' / L.block := thread_write_cta hX hS hw' hsp'
      have hc' : g' / L.block = g / L.block := by
        rw [← hcta']
        have := hcov'.2.1
        rw [hl] at this
        exact this.symm
      exact .inl <| late_after hpre hX hS hW ⟨hg, hg', hc'.symm⟩ hlk hb hk' hTT
  · left
    have hint := Execution.MemWrites.intent hw'
    cases p
    case writeLoad x y z =>
      have hcov2 := hcov'
      have hw2 := hw'
      obtain ⟨o, addr, b, -, ⟨pc', hget'⟩, -⟩ := hw'
      exact ⟨⟨dst', true, hint, hcov2⟩, Or.inl (hB.copy hlk hb hget' hg (l := a.loc.at m)
        (by rw [hl]) (by rw [hl]) ⟨x, y, z, dst', bytes', hw2, hcov2⟩)⟩
    case writeStore x y k =>
      obtain ⟨o, addr, b, -, ⟨pc, hget⟩, -⟩ := hw'
      exact absurd hget (no_tensorStore hX)
    case writeCta c =>
      obtain ⟨s, targets, ⟨pc, hget⟩, -⟩ := hw'
      exact absurd hget (no_clc hX)
    case writeCopy =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := hw'
      exact absurd hget (no_copy hX)
    case writeElem j =>
      obtain ⟨s, ⟨pc, hget⟩, -⟩ := hw'
      exact absurd hget (no_copy hX)
    all_goals exact (hw' : False).elim

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
