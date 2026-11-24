-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.LockBar0
public import Kernels.InklingRelDecode.Proof.Interface.LedgerFacts

@[expose] public section

/-!
# The phases of the barrier-0 events of the final generation

Facts about the number of barrier-1 events before an event on named barrier 0, from the phases of
the thread machines (`Interface.phase_inv`, conditional on `RoleReads`):

* `worker_final_b1`: a worker thread's barrier-0 event of source ordinal at least 2 (the exit
  role's `bar.sync 0`) follows at least three barrier-1 events of its thread (a state of the exit
  role has made a round of the dispatch loop, `t ≥ 1`, and its phase is `(1, 1)`);
* `loop_b1_le`: a default-partition thread's `bar.sync 0, 128` follows at most two barrier-1
  events of its thread (the prologue's and the softmax loop's are between the first two
  `barrier.sync 1`s and the third).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.BarOrd

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The instruction at the site of an event on barrier 0 is a `bar.sync 0` or `bar.sync 0, 128`. -/
theorem bar0_site_b0 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {g k pc : Nat} {cnt : Option Nat}
    {m : BarMode} {s : TSt} (he : X.get (g, k) = some ⟨pc, .bar 0 cnt m⟩)
    (hσ : St Q L X g k = some (some s)) : b0At (TSt.pc s) ≠ 0 := by
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar 0 cnt m⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar 0 cnt m⟩ : Event).kind = .bar 0 cnt m
    from rfl) with ⟨al, hop⟩ | ⟨-, al, hop⟩
  · simp [b0At, hc', hop]
  · simp [b0At, hc', hop]

/-- **A worker's barrier-0 event of source ordinal at least 2 follows three barrier-1 events.** -/
theorem worker_final_b1 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) {g k pc : Nat} {cnt : Option Nat} {m : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt m⟩) (hw : ¬ g % L.block < 128)
    (hord : 2 ≤ ((X.tr g).take k).countP (Execution.isBarId 0)) : 3 ≤ b1N X g k := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  have hk : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  have hb0 := bar0_site_b0 hpre hX hS he hσ
  obtain ⟨hTo, t', h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR k s hk hσ
  have hcls := cls_inv k s hk hσ
  cases s with
  | d d => exact absurd (hcls.mp trivial) hw
  | w ws =>
    have hlb : ¬ tLb (.w ws) < 2 := fun hlt => by
      have := (ordinal_inv hX hS k _ hk hσ).2 hlt
      omega
    cases ws with
    | worker w =>
      obtain ⟨site, P⟩ := w
      exfalso
      have := worker_b0 site
      simp only [TSt.pc, WComp.pc] at hb0
      cases site <;> simp_all [tLb, wLb, tTo, wTo]
    | idle d =>
      exfalso
      apply hb0
      simp only [TSt.pc, WComp.pc]
      exact idle_b0 d.site
    | loader d P =>
      exfalso
      apply hb0
      simp only [TSt.pc, WComp.pc]
      exact loader_b0 d.site
    | mma d P =>
      exfalso
      apply hb0
      simp only [TSt.pc, WComp.pc]
      exact mma_b0 d.site
    | exit x =>
      have h6 := h5 rfl
      have hp : wPh (.exit x) = (1, 1) := rfl
      simp only [tPh] at h2
      rw [hp] at h2
      omega

/-- A default-partition state whose instruction is `bar.sync 0, 128` has at most two barrier-1
events before it in its phase. -/
theorem d_b0_phase (d : DComp.St) (h : b0At (DComp.pc d) = 2) : (dPh d).2 ≤ 2 := by
  cases d with
  | dstart d =>
    have := dstart_b0 d.site
    simp only [DComp.pc] at h
    rw [this] at h
    split at h <;> omega
  | pro d => simp only [dPh]; split <;> omega
  | sm d => simp only [dPh]; split <;> omega
  | epi d =>
    have := epi_b0 d.site
    simp only [DComp.pc] at h
    rw [this] at h
    split at h <;> omega

/-- **A default-partition `bar.sync 0, 128` follows at most two barrier-1 events.** -/
theorem loop_b1_le (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
    (hR : RoleReads L X) {g k pc : Nat} {m : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 (some 128) m⟩) : b1N X g k ≤ 2 := by
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX ht he (fun pc' f h => by cases h)
  have hk : k ≤ (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1
    simp only at this
    omega
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := Frame.fired_site hS hX he hσ
  have hc' : kernel.code[TSt.pc s]? = some ins := hc
  have hf' : Fires (TSt.pc s) (eventTmpl asms L g t ins.op) ⟨pc, .bar 0 (some 128) m⟩ o := hf
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hmem := List.mem_of_getElem? hc'
  have hop : ∃ al, ins.op = .barSyncN (.imm 0) (.imm 128) al := by
    rcases bar_kind_op hb hmem hf' (show (⟨pc, .bar 0 (some 128) m⟩ : Event).kind =
      .bar 0 (some 128) m from rfl) with ⟨al, hop⟩ | ⟨-, al, hop⟩
    · rw [hop] at hf'
      have := EvD.fires_barSync_imm (by decide) hf'
      simp only [Event.mk.injEq, Kind.bar.injEq] at this
      exact absurd this.2.2.1 (by simp)
    · exact ⟨al, hop⟩
  obtain ⟨al, hop⟩ := hop
  have hpc2 : b0At (TSt.pc s) = 2 := by simp [b0At, hc', hop]
  obtain ⟨hTo, t', h1, h2, h3, h4, h5, h6⟩ := phase_inv hpre hX hS hR k s hk hσ
  cases s with
  | d d =>
    have ht0 := h3 rfl
    subst ht0
    simp only [tPh] at h2
    have := d_b0_phase d hpc2
    omega
  | w ws => exact absurd hpc2 (w_b0_ne ws)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
