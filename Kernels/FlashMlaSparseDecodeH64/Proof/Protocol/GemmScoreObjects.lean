-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRingObjects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0GemmTrace

@[expose] public section

/-! # Published QK and softmax probability objects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX AsyncCopy MBarrier PTX.Flow PTX.MbarRing

/-- The 128 softmax lanes of a CTA. -/
def softmax (L : Launch) (cta : Nat) (lane : Fin 128) : Nat := cta * L.block + lane.val

private theorem softmax_inj (L : Launch) (cta : Nat) : Function.Injective (softmax L cta) := by
  intro a b h
  apply Fin.ext
  exact Nat.add_left_cancel h

/-- An actual warpgroup-zero thread has a CTA-local softmax lane. -/
theorem softmax_thread {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) {g cta : Nat} (hc : ctaOf L g = cta) (hw : wgOf L g = 0) :
    ∃ lane : Fin 128, g = softmax L cta lane := by
  simp only [ctaOf, hpre.block] at hc
  simp only [wgOf, tidOf_eq hpre] at hw
  refine ⟨⟨g % 384, by omega⟩, ?_⟩
  simp only [softmax, hpre.block]
  omega

/-- Every softmax lane belongs to warpgroup zero. -/
theorem softmax_wg0 {P : Params} {L : Launch} {mem0 : Mem0}
    (hpre : Pre P L mem0) (cta : Nat) (lane : Fin 128) : wgOf L (softmax L cta lane) = 0 := by
  have := lane.isLt
  simp only [wgOf, tidOf_eq hpre, softmax, hpre.block]
  omega

/-- The 128 softmax threads publish the probability tile once per generation. -/
theorem score_obj {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) :
    Unit.Obj X (Object.soReady.loc L cta slot) 128 (softmax L cta) 0 where
  pos := by decide
  inj := softmax_inj L cta
  src r hr := by
    cases sources hpre hX hs ht r hr with
    | init ha => exact .init ha
    | @poll g i parity ok e sc hid he hk ha _ =>
      obtain ⟨tag, kind⟩ := e
      change kind = _ at hk
      subst kind
      exact .poll hid he ha
    | @publish g i e hid he hk ha hrole =>
      obtain ⟨hc, d, _, _, hst⟩ := hrole
      have hg := Frame.lt_of_get hX he
      have hw := RingRoleGeometry.of_trace hX hg (hs _ hg) hst
      obtain ⟨tag, kind⟩ := e
      change kind = _ at hk
      subst kind
      exact .arrive hid (softmax_thread hpre hc hw) he ha
    | notify _ _ _ _ _ _ _ _ hd _ =>
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
  init := init_first hpre hX hs ht
  noInval := objects_single_lifetime hX _
  parity := by
    intro g i _ p _ sc he
    have hg := Frame.lt_of_get hX he
    obtain ⟨⟨hc, d, hb, hp, hd, hst⟩, _⟩ := poll hpre hX (hs _ hg) ht he rfl
    have hcount := Wg1MmaGemmTrace.composed_count_here hpre hg .score
      ((hs _ hg).produces (hX.thr g hg)) hst hb
    simp only [hd, Wg1MmaGemmTrace.completed, Bool.false_eq_true, ↓reduceIte,
      Nat.add_zero] at hcount
    change okPolls (Object.soReady.loc L (ctaOf L g) slot) ((X.tr g).take i) = _ at hcount
    rw [hc] at hcount
    rw [hp, hcount]
    omega
  δ_le := by decide

/-- The elected MMA thread issues QK completion to the waiting softmax lanes. -/
theorem qk_obj {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {cta issuer : Nat} {slot : Fin 2}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) (hmma : MmaIssuer P L X cta issuer) :
    Notify.Obj X (Object.qkDone.loc L cta slot) issuer (Object.qkDone.loc L cta slot) 0 where
  src r hr := by
    cases sources hpre hX hs ht r hr with
    | init ha => exact .init ha
    | @poll g i parity ok e sc hid he hk ha _ =>
      obtain ⟨tag, kind⟩ := e
      change kind = _ at hk
      subst kind
      exact .poll hid he ha
    | publish _ _ _ _ hrole => exact hrole.elim
    | @notify g i e sp rank d hid he hk hm hr ha hc _ hd hst =>
      have hd : d.site = .qkCommit := by
        rcases hd with ⟨_, hd⟩ | ⟨h, _⟩
        · exact hd
        · cases h
      have hg := hmma _ _ _ hc hst (by simp [hd])
      subst g
      obtain ⟨tag, kind⟩ := e
      change kind = _ at hk
      subst kind
      exact .commit hid he hm hr ha
  init := init_first hpre hX hs ht
  noInval := objects_single_lifetime hX _
  parityOf := by
    intro g i _ p _ sc _ he
    have hg := Frame.lt_of_get hX he
    obtain ⟨⟨hc, d, hb, hp, hd, hst⟩, _⟩ := poll hpre hX (hs _ hg) ht he rfl
    have hcount := Wg0GemmTrace.composed_qk_counts hpre
      ((hs _ hg).produces (hX.thr g hg)) hst hd
    rw [hc, hb] at hcount
    change okPolls (Object.qkDone.loc L cta slot) ((X.tr g).take i) = _ at hcount
    rw [hp, hcount]
    omega
  δ_le := by decide

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
