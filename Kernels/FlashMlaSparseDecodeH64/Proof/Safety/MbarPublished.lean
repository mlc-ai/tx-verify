-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.Mbar
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingInit
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # Every mbarrier history entry is inside its published object lifetime -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem record_use (hX : Consistent L kernel Assumptions.all mem0 X)
    {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m)
    (hn : ∀ n, r.action ≠ .init n) :
    X.UsesMbar r.id.issuer m ∧ ∀ n, ¬ X.MbInit r.id.issuer m n := by
  have use {i : EvId} {tag : Nat} {k : Kind} (hEq : r.id.issuer = i)
      (he : X.get i = some ⟨tag, k⟩) (hu : X.UsesMbar i m)
      (hOther : ∀ n, k ≠ .mbInit m n) :
      X.UsesMbar r.id.issuer m ∧ ∀ n, ¬ X.MbInit r.id.issuer m n := by
    rw [hEq]
    refine ⟨hu, ?_⟩
    rintro count ⟨_, hInit⟩
    exact hOther count (congrArg Event.kind (Option.some.inj (he.symm.trans hInit)))
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact (hn _ ha).elim
  | inval hid he _ => exact use (by rw [hid]; rfl) he (.of_inval ⟨_, he⟩) (by simp)
  | arrive hid he _ =>
    exact use (by rw [hid]; rfl) he (.inl ⟨_, _, _, _, _, he⟩) (by simp)
  | wait hid he _ =>
    exact use (by rw [hid]; rfl) he (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, he⟩)))))
      (by simp)
  | increment hid he _ =>
    exact use (by rw [hid]; rfl) he (.inr (.inr (.inl ⟨_, _, he⟩))) (by simp)
  | tensor hid he hm _ =>
    exact use (by rw [hid]; rfl) he
      (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, hm⟩))))))) (by simp)
  | arriveOn hid he hm _ _ =>
    subst m
    exact use (by rw [hid]; rfl) he (.inr (.inr (.inl ⟨_, _, he⟩))) (by simp)
  | bulk hid he hc _ _ =>
    exact use (by rw [hid]; rfl) he (.inr (.inl ⟨_, ⟨_, he⟩, hc⟩)) (by simp)
  | commit hid he ht _ =>
    exact use (by rw [hid]; rfl) he (.inr (.inr (.inr (.inl ⟨_, _, ⟨_, he⟩, ht⟩)))) (by simp)
  | clc hid he hm ht _ =>
    exact use (by rw [hid]; rfl) he
      (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, ⟨_, he⟩, ht, hm⟩))))))))
      (by simp)

/-- The frozen kernel never invalidates a barrier object. -/
theorem mbar_record_not_inval (hX : Consistent L kernel Assumptions.all mem0 X)
    {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) : r.action ≠ .inval := by
  intro hn
  cases record_source hX.tma.2.2.1 hr with
  | inval hid he _ => exact Protocol.no_inval hX ⟨_, he⟩
  | init _ _ ha | arrive _ _ ha | wait _ _ ha | increment _ _ ha
  | tensor _ _ _ ha | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha | commit _ _ _ ha
  | clc _ _ _ _ ha =>
    rw [hn] at ha
    cases ha

/-- Every actual initialization is the successful first record of its barrier object. -/
theorem mbar_init_record_first
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {init : EvId} {m : Loc} {count : Nat} (hi : X.MbInit init m count) :
    ∃ r, (X.objects m)[0]? = some r ∧ r.id = .thread init ∧
      r.action = .init count ∧ r.fault = none := by
  obtain ⟨g, k⟩ := init
  have hEvent := hi.choose_spec
  have hg := Frame.lt_of_get hX hEvent
  obtain ⟨entry, _, rfl, rfl⟩ :=
    RingInitSources.init_from_trace hpre hX (hs g hg).machine ht hEvent rfl
  let m := initTable.loc L (ctaOf L g) entry
  have hCount := initTable.count_valid (b := entry) trivial
  have unique {i : EvId} {n : Nat} (ha : X.MbInit i m n) : i = (g, k) :=
    init_event_unique hpre hX (fun g hg => (hs g hg).machine) ht
      ha.choose_spec hi.choose_spec rfl rfl
  obtain ⟨r, h0, hId, hAct, hClean, _⟩ := init_record_success_of_unique_init hX hi hCount
    (fun _ s count hGet hAct => by
      have hMem := List.mem_of_getElem? hGet
      cases record_source hX.tma.2.2.1 hMem with
      | init hId hInit _ => rw [hId, unique ⟨_, hInit⟩]
      | inval _ _ hs' | arrive _ _ hs' | wait _ _ hs' | increment _ _ hs'
      | tensor _ _ _ hs' | arriveOn _ _ _ _ hs' | bulk _ _ _ _ hs'
      | commit _ _ _ hs' | clc _ _ _ _ hs' =>
        rw [hAct] at hs'
        cases hs')
    (fun _ s hGet hAct => by
      obtain ⟨hu, hn⟩ := record_use hX (List.mem_of_getElem? hGet) hAct
      obtain ⟨_, hm, i, hI, hP⟩ := published_init_of_use hpre hX hs ht hu hn
      have hSame := unique hI
      rw [hSame] at hP
      exact object_not_before_of_published hX ⟨_, hi⟩ hP)
  exact ⟨r, h0, hId, hAct, hClean⟩

/-- Actual object records all refer to their unique published prologue initialization. -/
theorem mbar_record_published
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    {m : Loc} {r : Record Ref} (hr : r ∈ X.objects m) :
    ObjectPublished L X m r := by
  classical
  by_cases hInit : ∃ n, r.action = .init n
  · exact .inl ⟨hInit, fun _ hv _ => (Protocol.no_inval hX hv).elim⟩
  obtain ⟨hu, hn⟩ := record_use hX hr (fun n hn => hInit ⟨n, hn⟩)
  obtain ⟨entry, rfl, init, hi, hp⟩ := published_init_of_use hpre hX hs ht hu hn
  obtain ⟨r0, h0, hid, ha, hf⟩ := mbar_init_record_first hpre hX hs ht hi
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hjPos : 0 < j := by
    cases j
    · rw [h0] at hj
      obtain rfl := Option.some.inj hj
      exact (hInit ⟨_, ha⟩).elim
    · omega
  exact .inr ⟨init, _, hi, ⟨0, j, r0, r, _, h0, hid, ha, hf, hj, rfl, hjPos,
    fun _ s _ _ hs' => mbar_record_not_inval hX (List.mem_of_getElem? hs')⟩, hp,
    fun _ hv _ _ => (Protocol.no_inval hX hv).elim⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
