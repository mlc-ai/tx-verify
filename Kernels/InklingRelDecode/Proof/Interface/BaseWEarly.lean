-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BaseWord
public import Kernels.InklingRelDecode.Proof.Interface.PrefixWeak

@[expose] public section

/-!
# The early barrier-0 facts under the tracking up to the base-word stops

The synchronization of the common start (`Protocol/BaseWord.lean`) needs the machines to follow
each thread only up to its barrier-0 arrival of ordinal 1: the arrivals of ordinal 0 and 1 are the
common start's, and the read of the base word is between them. `EarlyTT` says exactly that: every
event whose prefix has at most one barrier-0 event is tracked. It follows from `WeakTracked`
(`earlyTT_of_weak`): a base-word stop is at a state after the common start, which has two
barrier-0 events before it.

This file restates the early lemmas of `BaseWord.lean` with `EarlyTT` in place of
`Frame.Tracked`: `bar0_count_none'`, `earlySources_bar0'`, `exit_arrivals'`, `arrival_before'`,
`bar0_member'`, `bar0_chain'`, `allocStore_baseCausality_read'`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every event before a thread's second barrier-0 arrival is tracked** (the arrival included:
its prefix has one barrier-0 event). -/
def EarlyTT (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ g k, g < L.threads → ((X.tr g).take k).countP (Execution.isBarId 0) ≤ 1 →
    TT Q L X (g, k)

/-- A base-word stop is after the common start. -/
theorem baseStop_tLb {s : TSt} (h : BaseStop s) : ¬ tLb s < 2 := by
  cases s with
  | d s =>
    cases s with
    | pro d => simp [tLb_pro]
    | _ => exact h.elim
  | w s =>
    cases s with
    | worker w =>
      obtain ⟨site, P⟩ := w
      obtain ⟨hs, -⟩ := h
      simp only at hs
      subst hs
      simp [tLb, wLb]
    | _ => exact h.elim

/-- A state of a thread has as many barrier-0 events before it as at the end of its trace, past
the trace. -/
theorem state_le_len {g j : Nat} {s : TSt} (hσ : St Q L X g j = some (some s)) :
    St Q L X g (min j (X.tr g).length) = some (some s) := by
  by_cases hj : j ≤ (X.tr g).length
  · rwa [Nat.min_eq_left hj]
  · rw [Nat.min_eq_right (by omega)]
    have : Frame.stateAt (code L Q) X g j = Frame.stateAt (code L Q) X g (X.tr g).length :=
      Frame.stateAt_of_le (by omega)
    show Frame.stateAt (code L Q) X g (X.tr g).length = _
    rw [← this]
    exact hσ

/-- **`EarlyTT` from the tracking up to the base-word stops.** -/
theorem earlyTT_of_weak (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hW : WeakTracked Q L X) :
    EarlyTT Q L X := by
  intro g k hg hk hn
  obtain ⟨j, hj, s, hσ, hb⟩ := hW g (k + 1) hg hn
  have hσ' := state_le_len hσ
  have h2 := bar0_ordinal_two hX hS (Nat.min_le_right _ _) hσ' (baseStop_tLb hb)
  have hle : ((X.tr g).take (min j (X.tr g).length)).countP (Execution.isBarId 0) ≤
      ((X.tr g).take k).countP (Execution.isBarId 0) :=
    (List.take_sublist_take_left (by omega)).countP_le
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (hE : EarlyTT Q L X)
include hX hS hE

theorem bar0_count_none' {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hn : ((X.tr g).take k).countP (Execution.isBarId 0) ≤ 1) : cnt = none := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨s, hσ⟩ := event_state_at hS hX he (fun pc' f h => by cases h) (hE g k hg hn)
  have hk : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  obtain ⟨h1, -⟩ := ordinal_inv hX hS k s hk hσ
  have hl : tLb s < 2 := by omega
  rcases start_event hX hS he hσ hl with ⟨-, pc', h⟩ | ⟨-, h⟩
  · simp only [Event.mk.injEq, Kind.bar.injEq, true_and] at h
    exact h.2.1
  · exact absurd rfl (h 0 cnt mode)

include hpre in
theorem earlySources_bar0' :
    NamedBar.EarlySources L X none (Finset.range (CtaBarrier.warps L.block)) 0 1 := by
  intro e pc cnt ⟨mode, he⟩ hg hn
  refine ⟨?_, bar0_count_none' hX hS hE he hn⟩
  have hb : L.block = 256 := hpre.block
  have : e.1 % L.block < 256 := by
    have := Nat.mod_lt e.1 (show L.block > 0 by omega)
    omega
  simp only [Finset.mem_range, CtaBarrier.warps, hb]
  omega

theorem arrival_before' {h k r : Nat}
    (hr : r < ((X.tr h).take k).countP (Execution.isBarId 0)) (hr1 : r ≤ 1) :
    ∃ j pc, j < k ∧ X.IsBarrier (h, j) 0 none pc ∧
      ((X.tr h).take j).countP (Execution.isBarId 0) = r := by
  obtain ⟨j, e, hj, hq, hcnt⟩ := NamedBar.exists_ordinal (Execution.isBarId 0) _ hr
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjk
    obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hq
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
    have hget : X.get (h, j) = some ⟨pc, .bar 0 cnt m⟩ := hj
    have hnone := bar0_count_none' hX hS hE hget (by omega)
    subst hnone
    exact ⟨j, pc, hjk, hX.isBarrier_of_arrival noBarArrive ⟨m, hget⟩, hcnt⟩
  · cases hj

omit hE in
/-- **An exit event's state is an exit state**, given the state. -/
theorem exit_state_of {g k pc : Nat} {s : TSt} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hσ : St Q L X g k = some (some s)) : ¬ tLb s < 2 := by
  obtain ⟨t, ins, o, hat, hinv, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hop : isExitOp ins.op = true := by
    rcases fires_exit_op hf (rfl : (⟨pc, .exit⟩ : Event).kind = .exit) with h | h <;>
      simp [isExitOp, h]
  have hpw : TSt.pc s ∈ exitPcs := OpPcsFast.mem kernel_exit_pcs hc hop
  cases s with
  | w s =>
    cases s with
    | worker w => exact absurd hpw (fun h => by simpa using worker_exit_pc w.site h)
    | idle d => simp [tLb, wLb]
    | loader d _ => simp [tLb, wLb]
    | mma d _ => simp [tLb, wLb]
    | exit x => simp [tLb, wLb]
  | d s =>
    cases s with
    | dstart d => exact absurd hpw (fun h => by simpa using dstart_exit_pc d.site h)
    | pro d => simp [tLb_pro]
    | sm d => simp [tLb, dLb]
    | epi d => simp [tLb_epi]

/-- **An exiting thread has made two barrier-0 arrivals.** -/
theorem exit_arrivals' {g j pc r : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) (hr : r ≤ 1) :
    ∃ i pc', X.IsBarrier (g, i) 0 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 0) = r := by
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hj : j ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  have h2 : 2 ≤ ((X.tr g).take j).countP (Execution.isBarId 0) := by
    by_contra hlt
    obtain ⟨s, hσ⟩ := event_state_at hS hX he (by intro pc f h; cases h) (hE g j hg (by omega))
    exact hlt (bar0_ordinal_two hX hS hj hσ (exit_state_of hX hS he hσ))
  obtain ⟨i, pc', -, hb, hc⟩ := arrival_before' hX hS hE (h := g) (k := j) (r := r)
    (by omega) hr
  exact ⟨i, pc', hb, hc⟩

include hpre in
theorem bar0_member' {h jf pcf g : Nat} (hf : X.IsBarrier (h, jf) 0 none pcf)
    (hpassed : jf + 1 < (X.tr h).length)
    (hn : ((X.tr h).take jf).countP (Execution.isBarId 0) ≤ 1)
    (hcta : g / L.block = h / L.block) :
    ∃ i pc, X.IsBarrier (g, i) 0 none pc ∧ ((X.tr g).take i).countP (Execution.isBarId 0) =
      ((X.tr h).take jf).countP (Execution.isBarId 0) := by
  obtain ⟨hpos, hcount, hcard, hbound⟩ := bar0_group hpre
  have hb : L.block = 256 := hpre.block
  refine NamedBar.early_member_arrival hX hpos hcount hcard hbound (by decide)
    (earlySources_bar0' hpre hX hS hE) hf hpassed hn hcta ?_ ?_
  · have := Nat.mod_lt g (show L.block > 0 by omega)
    simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
    omega
  · rintro ⟨j, pcx, hex⟩
    exact exit_arrivals' hX hS hE hex hn

include hpre in
theorem bar0_chain' {g h before after jf pcf : Nat} (hsame : SameCta L g h)
    (hf : X.IsBarrier (h, jf) 0 none pcf)
    (hφ : ((X.tr h).take jf).countP (Execution.isBarId 0) ≤ 1)
    (hbc : ((X.tr g).take before).countP (Execution.isBarId 0) ≤
      ((X.tr h).take jf).countP (Execution.isBarId 0))
    (hbl : before < (X.tr g).length)
    (hbn : ∀ ev, (X.tr g)[before]? = some ev → ¬ Execution.isBarId 0 ev = true)
    (hafter : jf < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) := by
  have hpassed : jf + 1 < (X.tr h).length := by omega
  obtain ⟨i, pc, hi, hord⟩ := bar0_member' hpre hX hS hE hf hpassed hφ hsame.2.2
  obtain ⟨ev, hev⟩ : ∃ ev, (X.tr g)[before]? = some ev :=
    ⟨_, List.getElem?_eq_getElem hbl⟩
  have hgi : (X.tr g)[i]? = some ⟨pc, .bar 0 none .sync⟩ := hi
  have hlt : before < i := before_lt (φ := ((X.tr h).take jf).countP (Execution.isBarId 0))
    hbc hev (hbn ev hev) hgi (by simp [Execution.isBarId]) hord
  obtain ⟨hpos, hcount, hcard, hbound⟩ := bar0_group hpre
  exact NamedBar.early_same_ordinal_baseCausality hX hpos hcount hcard hbound (by decide)
    (earlySources_bar0' hpre hX hS hE) hsame hi hf hpassed hord hφ hlt hafter hlen

include hpre in
/-- **The allocation's store is before every thread's read of the base word.** -/
theorem allocStore_baseCausality_read' {g k h kr : Nat} (hsame : SameCta L g h)
    (hk : k < (X.tr g).length) (ha : AllocStoreAt Q L X g k)
    (hr : kr < (X.tr h).length) (hb : BaseReadAt Q L X h kr) :
    baseCausality L X (g, k) (h, kr) := by
  obtain ⟨hc0, hn0⟩ := allocStore_facts hX hS hk ha
  obtain ⟨hc1, -⟩ := baseRead_facts hX hS hr hb
  obtain ⟨j0, pc0, hj0, hf, hord⟩ := arrival_before' hX hS hE (h := h) (k := kr) (r := 0)
    (by omega) (by omega)
  exact bar0_chain' hpre hX hS hE hsame hf (by omega) (by omega) hk hn0 hj0 hr

include hpre in
/-- **A read of the base word is before every event of a thread of its CTA with two barrier-0
events before it.** -/
theorem base_read_before_count {h kr u kc : Nat} (hsame : SameCta L h u)
    (hr : kr < (X.tr h).length) (hb : BaseReadAt Q L X h kr)
    (h2 : 2 ≤ ((X.tr u).take kc).countP (Execution.isBarId 0)) (hkc : kc < (X.tr u).length) :
    baseCausality L X (h, kr) (u, kc) := by
  obtain ⟨hc1, hn1⟩ := baseRead_facts hX hS hr hb
  obtain ⟨j1, pc1, hj1, hf, hord⟩ := arrival_before' hX hS hE (h := u) (k := kc) (r := 1)
    (by omega) le_rfl
  exact bar0_chain' hpre hX hS hE hsame hf (by omega) (by omega) hr hn1 hj1 hkc

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
