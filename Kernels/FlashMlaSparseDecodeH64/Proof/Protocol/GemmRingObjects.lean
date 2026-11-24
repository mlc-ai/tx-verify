-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingLogs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaGemmTrace
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2GemmTrace
public import Lemmas.Protocol.UnitNotify
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGemmPublishers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingDequantInputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Sound

@[expose] public section

/-! # Published dequantization and commit completion objects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing MachineTracking

/-- The single elected thread runs each MMA block of the CTA. -/
def MmaIssuer (P : Params) (L : Launch) (X : Execution) (cta issuer : Nat) : Prop :=
  ∀ g i (d : Wg1Mma.D), ctaOf L g = cta →
    Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) →
    d.site ≠ .elect → g = issuer

/-- The execution chooses the issuer for all GEMM objects of the CTA. -/
theorem exists_issuer {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) :
    ∃ issuer : Nat, MmaIssuer P L X cta issuer := by
  obtain ⟨lane, h⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX hs
  exact ⟨cta * L.block + 128 + lane.val, h⟩

private theorem dequant_thread {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) {g cta : Nat} (hc : ctaOf L g = cta) (hw : wgOf L g = 2) :
    ∃ lane : Fin 128, g = RawRing.consumer L cta lane := by
  simp only [ctaOf, hpre.block] at hc
  simp only [wgOf, tidOf_eq hpre] at hw
  refine ⟨⟨g % 384 - 256, by omega⟩, ?_⟩
  simp only [RawRing.consumer, hpre.block]
  omega

/-- The dequantized tile is published by exactly the 128 dequantizer threads. -/
theorem dequant_obj {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    :
    Unit.Obj X (Object.dequantReady.loc L cta slot) 128 (RawRing.consumer L cta) 0 where
  pos := by decide
  inj := RawRing.consumer_inj L cta
  src r hr := by
    let hCode := fun h hh => Machine.code_sound (g := h) hpre hh
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | arrive hid he ha =>
      obtain ⟨hc, rfl, rfl, rfl, rfl, hPub⟩ := actual_gemm_arrival hpre hX hCode he rfl
      rcases hPub with ⟨_, _, _, _, _, hState⟩ | ⟨hBad, _⟩
      · have hg := Frame.lt_of_get hX he
        have hWg := RingRoleGeometry.of_trace hX hg (hs _ hg) hState
        exact .arrive hid (dequant_thread hpre hc hWg) he ha
      · cases hBad
    | @commit id _ _ _ _ he hTarget _ =>
      obtain ⟨g, i⟩ := id
      obtain ⟨_, _, _, _, h, _⟩ := actual_notification hpre hX hCode he rfl hTarget
      rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    | inval _ _ ha => exact (objects_single_lifetime hX _ r hr ha).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
      exact (actual_gemm_no_completion hpre hX hCode hr ha).elim
  init := actual_gemm_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)
  noInval := objects_single_lifetime hX _
  parity := by
    intro g i _ p _ sc he
    have hg := Frame.lt_of_get hX he
    have hFollow : Frame.stateAt (Machine.code P L) X g i ≠ some none := by
      intro hDismiss
      have h := dismissed_softmax_wait_range hpre hX (fun _ hg => Machine.code_sound hpre hg)
        he rfl hDismiss
      change (_ ≤ L.sharedBase + (222792 + 8 * slot.val) ∧ _) ∨
        (_ ∧ _ ≤ L.sharedBase + (222792 + 8 * slot.val)) ∨
        _ ≤ L.sharedBase + (222792 + 8 * slot.val) at h
      have := slot.isLt
      omega
    obtain ⟨⟨hc, d, hb, hp, hd, hst⟩, _⟩ :=
      poll_at_followed hpre hX (hs _ hg) hFollow he rfl
    have hcount := Wg1MmaGemmTrace.composed_count_here hpre hg .dequant
      ((hs _ hg).produces (hX.thr g hg)) hst hb
    simp only [hd, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero] at hcount
    change okPolls (Object.dequantReady.loc L (ctaOf L g) slot) ((X.tr g).take i) = _ at hcount
    rw [hc] at hcount
    rw [hp, hcount]
    omega
  δ_le := by decide

/-- The PV object has one issuer. Its alternating reuse polls are the dequantizer's polls. -/
theorem reuse_obj {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer) :
    Notify.Obj X (Object.svDone.loc L cta slot) issuer (Object.svDone.loc L cta slot) 1
      (fun h => wgOf L h = 2) where
  src r hr := by
    let hCode := fun h hh => Machine.code_sound (g := h) hpre hh
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | arrive _ he _ =>
      obtain ⟨_, _, _, _, _, hPub⟩ := actual_gemm_arrival hpre hX hCode he rfl
      rcases hPub with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    | @commit id _ _ _ hid he hTarget ha =>
      obtain ⟨g, i⟩ := id
      obtain ⟨hm, hc, d, _, hSite, hState⟩ := actual_notification hpre hX hCode he rfl hTarget
      rcases hSite with ⟨h, _⟩ | ⟨_, hd⟩
      · cases h
      · have hId := hmma g i d hc hState (by rw [hd]; decide)
        subst g
        exact .commit hid he hm hTarget ha
    | inval _ _ ha => exact (objects_single_lifetime hX _ r hr ha).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
      exact (actual_gemm_no_completion hpre hX hCode hr ha).elim
  init := actual_gemm_init_first hpre hX (fun _ hg => Machine.code_sound hpre hg)
  noInval := objects_single_lifetime hX _
  parityOf := by
    intro g i _ p _ sc hw he
    have hg := Frame.lt_of_get hX he
    have hFollow := tracked_nonsoftmax_wg hpre hX (fun _ hg => Machine.code_sound hpre hg)
      (show wgOf L g ≠ 0 by omega) i
    obtain ⟨⟨hc, hrole⟩, _⟩ := poll_at_followed hpre hX (hs _ hg) hFollow he rfl
    rcases hrole with ⟨d, hb, hp, hd, hst⟩ | ⟨d, _, _, _, hst⟩
    · have hcount := Wg2GemmTrace.composed_reuse_count hpre
        ((hs _ hg).produces (hX.thr g hg)) hst hd
      rw [hc, hb] at hcount
      change okPolls (Object.svDone.loc L cta slot) ((X.tr g).take i) = _ at hcount
      rw [hp, hcount]
      omega
    · have hw0 := RingRoleGeometry.of_trace hX hg (hs _ hg) hst
      change wgOf L g = 0 at hw0
      omega
  δ_le := by decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
