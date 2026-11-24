-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.ProloguePublication
public import Kernels.TmlFa4Fwd.Proof.PrologueInitUnique
public import Kernels.TmlFa4Fwd.Proof.StaticSafety
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.Fire
public import Lemmas.MBarrier.MBarrierInitOrder
public import Lemmas.Protocol.FirstPublished
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Prologue
open PTX PTX.Flow PTX.Proof AsyncCopy MBarrier

noncomputable section

private def postStartupObjectOp : Op → Bool
  | .mbarInit .. => false
  | op => objectOp op

private theorem beforeStartupObjectCode :
    (kernel.code.take 174).all (fun i => !postStartupObjectOp i.op) = true := by
  decide +kernel

/-- A non-initializing object use falls after the startup rendezvous. -/
theorem mbarUseIsLate {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) (hObj : ObjectKind e.kind)
    (hNotInit : ∀ loc count, e.kind ≠ .mbInit loc count) : 173 < e.pc := by
  by_contra hLow
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, o, _, hc, hf⟩
  · rw [hBad] at hObj
    cases hObj
  have hTake : (kernel.code.take 174)[e.pc]? = some ins := by
    rwa [List.getElem?_take_of_lt (by omega)]
  have hAudit := List.all_eq_true.mp beforeStartupObjectCode ins (List.mem_of_getElem? hTake)
  have hNon : postStartupObjectOp ins.op = false := by simpa using hAudit
  have hClass :
      (∃ base off counts, ins.op = .mbarInit base off counts) ∨ objectOp ins.op = false := by
    generalize hi : ins.op = op at hNon ⊢
    cases op <;> simp_all [postStartupObjectOp]
  rcases hClass with ⟨ba, off, n, hI⟩ | hOther
  · rw [hI] at hf
    rcases eventTmpl_opTmpl (A := Assumptions.all) (L := l) (g := i.1) (t := t)
      (.mbarInit ba off n) with ⟨f, hF⟩ | ⟨loc, count, u, hInit⟩
    · rw [hF] at hf
      rw [congrArg Event.kind hf.1] at hObj
      cases hObj
    · rw [hInit] at hf
      exact hNotInit loc count (congrArg Event.kind hf.1)
  · exact notObject_of_op hOther hf hObj

/-- An object's non-initialization record has an actual issuer beyond the startup rendezvous. -/
theorem mbarRecordIssuerAfterStartup {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {r : Record Ref}
    (hr : r ∈ X.objects loc) (hNotInit : ∀ n, r.action ≠ .init n) :
    ∃ event, X.get r.id.issuer = some event ∧ 173 < event.pc := by
  have hLate {i : EvId} {e : Event} (he : X.get i = some e) (hObj : ObjectKind e.kind)
      (hNot : ∀ loc count, e.kind ≠ .mbInit loc count) : ∃ event,
        X.get i = some event ∧ 173 < event.pc :=
    ⟨e, he, mbarUseIsLate hX he hObj hNot⟩
  cases record_source hX.tma.2.2.1 hr with
  | init _ _ ha => exact (hNotInit _ ha).elim
  | inval hi he _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | arrive hi he _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | wait hi he _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | increment hi he _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | tensor hi he _ _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | arriveOn hi he _ _ _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | bulk hi he _ _ _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | commit hi he _ _ =>
    rw [hi]
    exact hLate he trivial (by simp)
  | clc hi he _ _ _ =>
    rw [hi]
    exact hLate he trivial (by simp)

private theorem initRecordSource {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {loc : Loc} {r : Record Ref}
    (hr : r ∈ X.objects loc) {n : Nat} (ha : r.action = .init n) :
    ∃ i, r.id = .thread i ∧ X.MbInit i loc n := by
  cases record_source hX.tma.2.2.1 hr <;> rename_i h
  all_goals try (rw [h] at ha; cases ha; done)
  rename_i hi he
  rw [h] at ha
  obtain rfl := Action.init.inj ha
  exact ⟨_, hi, ⟨_, he⟩⟩

/-- Once the issuer of each record is known to be in the owning CTA, the unique actual
initialization precedes all the records of that object and is successfully performed. -/
theorem initFirstOfOwnedRecords {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {cta : Nat}
    (site : Fin 34) {i : EvId} (hInit : X.MbInit i (initObject l cta site) (initSite site).count)
    (hOwn : ∀ r ∈ X.objects (initObject l cta site), (∀ n, r.action ≠ .init n) →
      r.id.issuer.1 / l.block = cta) :
    PairTmaRing.InitFirst X (initObject l cta site) (initSite site).count ∧
      ∀ r ∈ X.objects (initObject l cta site), ObjectPublished l X (initObject l cta site) r := by
  let loc := initObject l cta site
  let count := (initSite site).count
  have hUnique (r : Record Ref) (hr : r ∈ X.objects loc) (n : Nat)
      (ha : r.action = .init n) : r.id = .thread i := by
    obtain ⟨j, hj, hJ⟩ := initRecordSource hX hr ha
    rw [hj, (actualInitializerUnique hp hX hJ hInit).1]
  have hPub (r : Record Ref) (hr : r ∈ X.objects loc) (hNo : ∀ n, r.action ≠ .init n) :
      InitPublished l X i r.id.issuer loc := by
    obtain ⟨ev, hGet, hLate⟩ := mbarRecordIssuerAfterStartup hX hr hNo
    have hCta := hOwn r hr hNo
    obtain ⟨j, hFound, hp'⟩ := initPublishedAfterCommon hp hX (event_thread_lt hX hGet)
      hGet hLate site
    rw [hCta] at hFound hp'
    rw [(actualInitializerUnique hp hX hFound hInit).1] at hp'
    exact hp'
  have hCount : validCount count := by fin_cases site <;> decide
  obtain ⟨r0, hZero, hId, hAct, hOk, _⟩ := init_record_success_of_unique_init hX hInit hCount
    (fun _ r n hr ha => hUnique r (List.mem_of_getElem? hr) n ha)
    (fun _ r hr hNon => object_not_before_of_published hX ⟨count, hInit⟩
      (hPub r (List.mem_of_getElem? hr) hNon))
  constructor
  · intro _ _
    refine ⟨r0, hZero, hAct, hOk, ?_⟩
    intro r hr hInitAction
    obtain ⟨n, hn⟩ := hInitAction
    have hSame := (hUnique r hr n hn).trans hId.symm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
    have hj0 := object_record_index_unique hX.tma.2.2.1 hj hZero hSame
    rw [hj0, hZero] at hj
    exact (Option.some.inj hj).symm
  · intro r hr
    exact objectPublished_of_first hX hZero hId hAct hOk hInit
      (fun _ _ h => noMbarInval hX h) hPub hr


/-- Any record of an audited object gives its actual initializer, including in prefixes
that stop before the common rendezvous or before the initializer's peers. -/
theorem initializerOfOwnedRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {cta : Nat}
    (site : Fin 34) {r : Record Ref} (hr : r ∈ X.objects (initObject l cta site))
    (hOwn : r.id.issuer.1 / l.block = cta) :
    ∃ i, X.MbInit i (initObject l cta site) (initSite site).count := by
  by_cases hInit : ∃ n, r.action = .init n
  · obtain ⟨n, hn⟩ := hInit
    obtain ⟨i, hi, pc, he⟩ := initRecordSource hX hr hn
    rw [hi] at hOwn
    change i.1 / l.block = cta at hOwn
    obtain ⟨j, _, _, _, hLoc, hCount, _⟩ := actualInitializer hp hX (event_thread_lt hX he) he
    rw [hOwn] at hLoc
    have hEq : site = j := by
      by_contra hn
      exact initObject_ne hn hLoc
    subst j
    exact ⟨i, pc, by simpa only [hCount] using he⟩
  · obtain ⟨e, he, hPc⟩ := mbarRecordIssuerAfterStartup hX hr
      (fun n hn => hInit ⟨n, hn⟩)
    obtain ⟨i, hi, _⟩ := initPublishedAfterCommon hp hX (event_thread_lt hX he) he hPc site
    rw [hOwn] at hi
    exact ⟨i, hi⟩

end
end PTX.Kernels.TmlFa4Fwd.Prologue
