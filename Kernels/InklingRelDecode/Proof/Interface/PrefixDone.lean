-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.PrefixClose
public import Kernels.InklingRelDecode.Proof.Interface.BaseWCopy
public import Kernels.InklingRelDecode.Proof.Interface.BaseWAlloc
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords

@[expose] public section

/-!
# The machines follow every thread

The writer facts of the Tensor Memory base word on the tracking up to the base-word stops
(`BaseSources`: the allocation's store writes the zero word, `allocWordZero_w`; every tensor copy
is after every read of the base word through a proxy fence, `copy_w`) give the tracking of the
machines in every consistent execution (`tracked_of_close`): every state that is not
`Discharged` is a base-word stop, and no thread reaches one.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The writer facts of the base word**, on the tracking up to the base-word stops. -/
theorem baseSources_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X) :
    BaseSources Q L X :=
  ⟨allocWordZero_w hpre hX hS hT hW, copy_w hpre hX hS hT hW⟩

/-- **The machines follow every thread in every consistent execution.** -/
theorem tracked_holds (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    Frame.Tracked (code L Q) X :=
  tracked_of_close hpre hX (baseSources_of hpre hX (sound_all hpre smOb) (tmplOk hpre))

/-- **`BaseWordRead`**: a read of the Tensor Memory base word is at a base-read state
(`thread_read_class`), where it returns the zero word (`base_read_w`). -/
theorem baseWordRead_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    BaseWordRead L X := by
  intro g k pc a bs hget hloc hsz
  have hS := sound_all hpre smOb
  have hT := tmplOk hpre
  have hW : WeakTracked Q L X := weakTracked_of hpre hX hS hT
    (fun g k s e hg he hσ hd hb _ _ => absurd ((discharged_or_stop hS hX he hσ).resolve_left hd) hb)
  have hg : g < L.threads := Frame.lt_of_get hX hget
  have hsh := hpre.sharedRange
  unfold sharedBytes at hsh
  obtain ⟨s, hσ⟩ := Frame.event_state hS hX (tracked_holds hpre hX) hget
    (by intro pc' f h; cases h)
  have hσ' : St Q L X g k = some (some s) := hσ
  have hb : Bar.BaseReadAt Q L X g k := by
    cases thread_read_class hpre hX hS hT hg hget hσ' (by rw [hloc]) with
    | @dstart d0 _ hs hl hz' =>
      obtain ⟨site, tm⟩ := d0
      simp only at hs
      subst hs
      exact Or.inl ⟨tm, hσ'⟩
    | @base w0 _ hs hl hz' =>
      obtain ⟨site, P⟩ := w0
      simp only at hs
      subst hs
      exact Or.inr ⟨P, hσ'⟩
    | role hs hl hz' | ld0 hs hl hz' | ld1 hs hl hz' | ldNum hs hl hz' =>
      have := congrArg Loc.addr (hl.symm.trans hloc)
      simp only at this
      omega
    | scratch hs hl hz' =>
      have := congrArg Loc.addr (hl.symm.trans hloc)
      simp only at this
      have : g % L.block % 4 < 4 := Nat.mod_lt _ (by have := hpre.block; omega)
      omega
  exact base_read_w hpre hX hS hT hW (baseSources_of hpre hX hS hT hW) hget hb hloc hsz

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
