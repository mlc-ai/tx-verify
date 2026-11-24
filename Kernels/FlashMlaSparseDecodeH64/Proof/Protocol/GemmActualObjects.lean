-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmScoreObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingGemmPublishers
public import Lemmas.Protocol.UnitItems

@[expose] public section

/-! # Actual QK and probability history sources -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX PTX.Flow PTX.MBarrier PTX.AsyncCopy PTX.MbarRing MachineTracking

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat} {slot : Fin 2}

/-- The checked probability history contains publications from the 128 softmax lanes. -/
theorem actual_score_history
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) :
    Unit.History X (Object.soReady.loc L cta slot) 128 (softmax L cta) where
  pos := by decide
  inj := by
    intro a b h
    exact Fin.ext (Nat.add_left_cancel h)
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | arrive hid he ha =>
      obtain ⟨hc, rfl, rfl, rfl, rfl, hPub⟩ := actual_gemm_arrival hpre hX hs he rfl
      rcases hPub with ⟨h, _⟩ | ⟨_, hWg, _⟩
      · cases h
      · exact .arrive hid (softmax_thread hpre hc hWg) he ha
    | @commit id _ _ _ _ he htarget _ =>
      obtain ⟨g, i⟩ := id
      obtain ⟨_, _, _, _, h, _⟩ := actual_notification hpre hX hs he rfl htarget
      rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    | inval _ _ ha => exact (objects_single_lifetime hX _ r hr ha).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
      exact (actual_gemm_no_completion hpre hX hs hr ha).elim
  init := actual_gemm_init_first hpre hX hs
  noInval := objects_single_lifetime hX _

/-- The elected MMA warp's successful score acquires alternate per slot. -/
theorem actual_score_alternates {issuer : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hw : warpOf L issuer = 4) :
    SelectedAlternates (objectThreadSelected issuer) (X.objects (Object.soReady.loc L cta slot))
      0 := by
  apply MbarRing.Poll.alternates hX ((actual_score_history hpre hX hs).pclean hX)
  intro i tag p acq sc he
  have hIssuer := Frame.lt_of_get hX he
  have hWg : wgOf L issuer ≠ 0 := by unfold wgOf warpOf at *; omega
  have hFollow := tracked_nonsoftmax_wg hpre hX hs hWg i
  obtain ⟨⟨hc, d, hb, hp, hd, hState⟩, _⟩ :=
    poll_at_followed (obj := .soReady) hpre hX (hs issuer hIssuer).machine hFollow he rfl
  have hCount := Wg1MmaGemmTrace.composed_count_here hpre hIssuer .score
    ((hs issuer hIssuer).machine.produces (hX.thr issuer hIssuer)) hState hb
  simp only [hd, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at hCount
  change Flow.okPolls (Object.soReady.loc L (ctaOf L issuer) slot) ((X.tr issuer).take i) =
    d.i / 2 at hCount
  rw [hc] at hCount
  simp [hCount, hp]

/-- All QK arrivals in the checked history come from the elected MMA issuer. -/
theorem actual_qk_obj_of_parity {issuer : Nat} {selected : Nat → Prop}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : MmaIssuer P L X cta issuer)
    (hpar : ∀ {g i tag p : Nat} {acq : Bool} {sc : MbarScope}, selected g →
      X.get (g, i) = some ⟨tag, .wait (Object.qkDone.loc L cta slot) p true acq sc⟩ →
      p % 2 = Flow.okPolls (Object.qkDone.loc L cta slot) ((X.tr g).take i) % 2) :
    Notify.Obj X (Object.qkDone.loc L cta slot) issuer (Object.qkDone.loc L cta slot)
      0 selected where
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | arrive _ he _ =>
      obtain ⟨_, _, _, _, _, hPub⟩ := actual_gemm_arrival hpre hX hs he rfl
      rcases hPub with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
    | @commit id _ _ _ hid he htarget ha =>
      obtain ⟨g, i⟩ := id
      obtain ⟨hm, hc, d, _, h, hState⟩ := actual_notification hpre hX hs he rfl htarget
      rcases h with ⟨_, hSite⟩ | ⟨h, _⟩
      · have hId := hmma g i d hc hState (by simp [hSite])
        subst g
        exact .commit hid he hm htarget ha
      · cases h
    | inval _ _ ha => exact (objects_single_lifetime hX _ r hr ha).elim
    | increment _ he _ | arriveOn _ he _ _ _ => exact (no_async_arrive hX he rfl).elim
    | tensor _ _ _ ha | bulk _ _ _ _ ha | clc _ _ _ _ ha =>
      exact (actual_gemm_no_completion hpre hX hs hr ha).elim
  init := actual_gemm_init_first hpre hX hs
  noInval := objects_single_lifetime hX _
  parityOf h hWait := by simpa only [Nat.add_zero] using hpar h hWait
  δ_le := Nat.zero_le _

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
