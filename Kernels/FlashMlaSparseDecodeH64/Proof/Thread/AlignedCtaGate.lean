-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingSourceSites
import Lemmas.Flow.NthEv
import Lemmas.Tmem.PairProtocol

public section

/-! # Only the launch gate is an aligned barrier with full-CTA participation -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.AlignedCtaGate

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {g i : Nat}

private theorem only_gate {d : Machine.ThreadD} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0)
    (hf : (Machine.machine P L g).Fired (some d) e o)
    (hA : kernel.isAlignedCtaBar e = true) : d = .prologue .barrier := by
  have hb : ∃ id mode, e.kind = .bar id none mode ∧ kernel.alignedAt e.pc = true := by
    obtain ⟨tag, kind⟩ := e
    cases kind <;> simp only [Kernel.isAlignedCtaBar, Bool.false_eq_true] at hA
    case bar id c m =>
      cases c <;> simp only [Bool.false_eq_true] at hA
      exact ⟨id, m, rfl, hA⟩
  obtain ⟨id, mode, hk, ha⟩ := hb
  have hTag : e.pc = (Machine.code P L g).pc d := by
    obtain ⟨t, hat, hf⟩ := hf
    exact (fires_pc hf).trans hat.1.1
  rw [hTag] at ha
  have hSite := RingGateEvents.bar_site hf hk
  cases d with
  | prologue s => exact congrArg Machine.ThreadD.prologue hSite
  | wg0 d =>
    rcases hSite with h | h | h | h | h | h | ⟨j, h⟩
    case inr.inr.inr.inr.inr.inl =>
      change kernel.alignedAt d.site.pc = true at ha
      rw [h] at ha
      change kernel.alignedAt 1835 = true at ha
      unfold Kernel.alignedAt at ha
      rw [Flow.code_bar_10] at ha
      cases ha
    case inr.inl =>
      have hp := Wg0PeerTrace.pair_kind hpre hf h
      rw [hk] at hp
      cases hp
    all_goals
      have hw := Wg0BarrierTrace.bar9_kind hpre hf (by rw [h]; trivial)
      rw [hk] at hw
      cases hw
  | mma d =>
    change d.site = .outBar at hSite
    change kernel.alignedAt d.site.pc = true at ha
    rw [hSite] at ha
    change kernel.alignedAt 2160 = true at ha
    unfold Kernel.alignedAt at ha
    rw [Flow.code_bar_11] at ha
    cases ha
  | tma d =>
    change d.site = .barrier at hSite
    change kernel.alignedAt d.site.pc = true at ha
    rw [hSite] at ha
    change kernel.alignedAt 2330 = true at ha
    unfold Kernel.alignedAt at ha
    rw [Flow.code_bar_12] at ha
    cases ha
  | index d =>
    change d.site = .barrier at hSite
    change kernel.alignedAt d.site.pc = true at ha
    rw [hSite] at ha
    change kernel.alignedAt 2585 = true at ha
    unfold Kernel.alignedAt at ha
    rw [Flow.code_bar_13] at ha
    cases ha
  | idle s =>
    change s = .sync at hSite
    subst s
    change kernel.alignedAt 2604 = true at ha
    unfold Kernel.alignedAt at ha
    rw [Flow.code_bar_14] at ha
    cases ha
  | wg2 d =>
    change d.site = .barrier at hSite
    change kernel.alignedAt d.site.pc = true at ha
    rw [hSite] at ha
    change kernel.alignedAt 3610 = true at ha
    unfold Kernel.alignedAt at ha
    rw [Flow.code_bar_15] at ha
    cases ha
  | head | done => exact hSite.elim

private theorem gate_state {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hA : kernel.isAlignedCtaBar e = true) :
    Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .barrier)) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX (hs g hg).machine ht he (by
    intro fault h
    obtain ⟨tag, kind⟩ := e
    change kind = .ub fault at h
    subst kind
    cases hA)
  rwa [only_gate hpre hf hA] at hd

/-- An aligned full-CTA event is the lane's first such event. -/
theorem ordinal_zero {e : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.get (g, i) = some e) (hA : kernel.isAlignedCtaBar e = true) :
    ((X.tr g).take i).countP kernel.isAlignedCtaBar = 0 := by
  by_contra hn
  obtain ⟨j, hj, hjLt, hAlign, _⟩ := Tmem.Pair.countP_take_occ
    kernel.isAlignedCtaBar (X.tr g) i 0 (by omega)
  have hf : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hjLt
  have hEq := RingInitSources.gate_state_unique he hf
    (gate_state hpre hX hs ht he hA) (gate_state hpre hX hs ht hf hAlign)
  omega

/-- Every exiting thread has passed the aligned full-CTA launch gate. -/
theorem before_exit (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {tag : Nat} (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    0 < (X.tr g).countP kernel.isAlignedCtaBar := by
  have hg := Frame.lt_of_get hX he
  have hSound := (hs g hg).machine
  obtain ⟨d, _, hd, hf⟩ := RingSourceSites.fired_from_trace hX hSound ht he (by simp)
  obtain ⟨k, ev, hk, hev, hkind, hsGate⟩ :=
    RingInitSources.gate_before_role hX hSound ht he hd
      (RingGateEvents.exit_after_prologue hf rfl)
  have hAligned : kernel.isAlignedCtaBar ev = true := by
    obtain ⟨_, hfActual⟩ := (hSound.produces (hX.thr g hg)).fired_at hev hsGate
    obtain ⟨_, _, hFireActual⟩ := RingGateEvents.fired_at_code hfActual Flow.code_bar_0
    have hTag := fires_pc hFireActual
    obtain ⟨site, kind⟩ := ev
    change site = 97 at hTag
    change kind = .bar 0 none .sync at hkind
    subst site
    subst kind
    simp [Kernel.isAlignedCtaBar, Kernel.alignedAt, Flow.code_bar_0, Op.aligned]
  have hPos := PTX.Flow.countP_take_succ hev hAligned
  have hi : i < (X.tr g).length := PTX.len_of_get he
  have hLen : k + 1 ≤ (X.tr g).length := by omega
  have hMono := PTX.Flow.countP_take_mono kernel.isAlignedCtaBar (X.tr g) hLen
  rw [List.take_length] at hMono
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.AlignedCtaGate
