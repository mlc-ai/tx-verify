-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.TensorStore.TensorStoreCompleteConsistentWriteFrame
public import Lemmas.Execution.EffectFrame

@[expose] public section

/-! # A pending tensor reduction element completes

A proof tool for DEP-REDUCTION-VALUES. An element of an issued reduction whose shared bytes are read
and whose global bytes are not yet written can be performed in one step: its old destination
bytes are read from caller-chosen sources and all its bytes are written together. The caller
supplies, byte by byte, what any new read needs (a covering source write with the read value or
W0, and no visible later write hiding it) and the two reduction-specific facts: no performed
reduction of the same element footprint already read that source (`hunique`), and the written
bytes are the reduced value when the value rule gives one (`hvalue`). The new element has no
reader, so reads-from among reductions stays acyclic; the new effects have no completion, so no
order edge leaves them. -/

namespace PTX
open AsyncCopy TensorStore
noncomputable section

/-- Element `(x, y)` performed: old bytes `old`, written bytes `new`. -/
def TensorStore.Observation.reduceElement (o : TensorStore.Observation) (x y : Nat)
    (old new : Nat → Byte) : TensorStore.Observation :=
  ⟨o.spec, {o.effects with
    old := fun s => if s.1.val = x ∧ s.2.1.val = y then some (old s.2.2.val) else o.effects.old s,
    write := fun s => if s.1.val = x ∧ s.2.1.val = y then some (new s.2.2.val)
      else o.effects.write s}⟩

/-- The reads-from sources of the element's old bytes are `src`; all others are kept. -/
def reduceRf (X : Execution) (i : EvId) (x y : Nat) (src : Nat → Option Ref) :
    Ref → Nat → Option Ref
  | .async j (.old (.store x' y' k')), k => if j = i ∧ x' = x ∧ y' = y then src k' else
      X.rf (.async j (.old (.store x' y' k'))) k
  | e, k => X.rf e k

def Execution.recordStoreReduce (X : Execution) (i : EvId) (o : TensorStore.Observation)
    (x y : Nat) (old new : Nat → Byte) (src : Nat → Option Ref) : Execution :=
  X.recordStoreEffects i (o.reduceElement x y old new) (reduceRf X i x y src)

/-- The new references: the element's old-byte reads and writes. -/
def ReduceNew (i : EvId) (x y : Nat) (e : Ref) : Prop :=
  ∃ k, e = .async i (.old (.store x y k)) ∨ e = .async i (.write (.store x y k))

namespace TensorStore

variable {o : Observation} {x y : Nat} {old new : Nat → Byte}

theorem reduceElement_spec : (o.reduceElement x y old new).spec = o.spec := rfl

theorem reduceElement_writeByte_other {x' y' k : Nat} (h : ¬(x' = x ∧ y' = y)) :
    writeByte (o.reduceElement x y old new) x' y' k = writeByte o x' y' k := by
  unfold writeByte
  cases hs : TensorTransfer.slotAt o.spec.descriptor x' y' k with
  | none => simp [Observation.reduceElement, hs]
  | some s =>
    have hc := TensorCopy.slotAt_coordinates hs
    simp only [Observation.reduceElement, hs, Option.bind_some]
    rw [ite_eq_right (by rw [hc.1, hc.2.1]; exact h)]

theorem reduceElement_oldByte_other {x' y' k : Nat} (h : ¬(x' = x ∧ y' = y)) :
    oldByte (o.reduceElement x y old new) x' y' k = oldByte o x' y' k := by
  unfold oldByte
  cases hs : TensorTransfer.slotAt o.spec.descriptor x' y' k with
  | none => simp [Observation.reduceElement, hs]
  | some s =>
    have hc := TensorCopy.slotAt_coordinates hs
    simp only [Observation.reduceElement, hs, Option.bind_some]
    rw [ite_eq_right (by rw [hc.1, hc.2.1]; exact h)]

theorem reduceElement_writeByte_self (k : Nat) :
    writeByte (o.reduceElement x y old new) x y k =
      (TensorTransfer.slotAt o.spec.descriptor x y k).map fun _ => new k := by
  unfold writeByte
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [Observation.reduceElement, hs]
  | some s =>
    have hc := TensorCopy.slotAt_coordinates hs
    simp [Observation.reduceElement, hs, hc.1, hc.2.1, hc.2.2]

theorem reduceElement_oldByte_self (k : Nat) :
    oldByte (o.reduceElement x y old new) x y k =
      (TensorTransfer.slotAt o.spec.descriptor x y k).map fun _ => old k := by
  unfold oldByte
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [Observation.reduceElement, hs]
  | some s =>
    have hc := TensorCopy.slotAt_coordinates hs
    simp [Observation.reduceElement, hs, hc.1, hc.2.1, hc.2.2]

/-- The element's slots: in bounds, read, not yet written. -/
def ElementPending (o : Observation) (x y : Nat) : Prop :=
  ∀ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x → s.2.1.val = y →
    (∃ loc, destination o.spec s = some loc) ∧ (∃ b, o.effects.read s = some b) ∧
      o.effects.write s = none

theorem ElementPending.old_none {o : Observation} {x y : Nat} (hc : CopyOk o.spec o.effects)
    (hp : ElementPending o x y) (s : TensorTransfer.Slot o.spec.descriptor) (h1 : s.1.val = x)
    (h2 : s.2.1.val = y) : o.effects.old s = none := by
  cases ho : o.effects.old s with
  | none => rfl
  | some b =>
    obtain ⟨-, w, hw⟩ := hc.old s b ho
    rw [(hp s h1 h2).2.2] at hw
    cases hw

theorem reduceElement_copyOk {red : AtomOp} (hc : CopyOk o.spec o.effects)
    (hred : o.spec.reduce = some red) (hp : ElementPending o x y)
    (hfull : o.effects.fullDone = false) :
    CopyOk (o.reduceElement x y old new).spec (o.reduceElement x y old new).effects := by
  constructor
  · intro (s : TensorTransfer.Slot o.spec.descriptor) byte hw
    by_cases hs : s.1.val = x ∧ s.2.1.val = y
    · obtain ⟨hd, ⟨b, hb⟩, -⟩ := hp s hs.1 hs.2
      refine ⟨hd, b, hb, fun h => ?_⟩
      rw [reduceElement_spec, hred] at h
      cases h
    · simp only [Observation.reduceElement, ite_eq_right hs] at hw
      exact hc.writes s byte hw
  · exact hc.readsComplete
  · intro hf
    change o.effects.fullDone = true at hf
    rw [hfull] at hf
    cases hf
  · intro (s : TensorTransfer.Slot o.spec.descriptor) byte hw hr other h1 h2
    by_cases hs : s.1.val = x ∧ s.2.1.val = y
    · have ho : other.1.val = x ∧ other.2.1.val = y := by rw [h1, h2]; exact hs
      simp [Observation.reduceElement, ho]
    · have ho : ¬(other.1.val = x ∧ other.2.1.val = y) := by rw [h1, h2]; exact hs
      simp only [Observation.reduceElement, ite_eq_right hs] at hw
      simp only [Observation.reduceElement, ite_eq_right ho]
      exact hc.element s byte hw hr other h1 h2
  · intro (s : TensorTransfer.Slot o.spec.descriptor) byte hb
    by_cases hs : s.1.val = x ∧ s.2.1.val = y
    · exact ⟨by rw [reduceElement_spec, hred]; rfl, new s.2.2.val,
        by simp [Observation.reduceElement, hs]⟩
    · simp only [Observation.reduceElement, ite_eq_right hs] at hb ⊢
      exact hc.old s byte hb

theorem reduceElement_effects_extends (hc : CopyOk o.spec o.effects) (hp : ElementPending o x y) :
    TensorStore.Extends o.effects (o.reduceElement x y old new).effects := by
  refine ⟨fun _ _ h => h, ?_, fun h => h, fun h => h, fun _ => rfl, ?_⟩
  · intro (s : TensorTransfer.Slot o.spec.descriptor) b hw
    by_cases hs : s.1.val = x ∧ s.2.1.val = y
    · rw [(hp s hs.1 hs.2).2.2] at hw
      cases hw
    · simpa only [Observation.reduceElement, ite_eq_right hs] using hw
  · intro (s : TensorTransfer.Slot o.spec.descriptor) b hb
    by_cases hs : s.1.val = x ∧ s.2.1.val = y
    · rw [hp.old_none hc s hs.1 hs.2] at hb
      cases hb
    · simpa only [Observation.reduceElement, ite_eq_right hs] using hb

theorem reduceElement_extends (hc : CopyOk o.spec o.effects) (hp : ElementPending o x y) :
    o.Extends (o.reduceElement x y old new) :=
  ⟨rfl, reduceElement_effects_extends hc hp⟩

end TensorStore

variable {L : Launch} {X : Execution} {i : EvId} {o : TensorStore.Observation} {x y : Nat}
  {old new : Nat → Byte} {src : Nat → Option Ref}
local notation "Y" => X.recordStoreReduce i o x y old new src

theorem reduceFrame_rf : (Y).rf = reduceRf X i x y src := rfl

theorem reduceFrame_rf_other {e : Ref} (he : ¬ ∃ k', e = .async i (.old (.store x y k')))
    (k : Nat) :
    (Y).rf e k = X.rf e k := by
  rw [reduceFrame_rf]
  cases e with
  | thread j => simp only [reduceRf]
  | async j p =>
    cases p
    case oldStore x' y' k' =>
      simp only [reduceRf]
      rw [ite_eq_right]
      rintro ⟨rfl, rfl, rfl⟩
      exact he ⟨k', rfl⟩
    all_goals simp only [reduceRf]

theorem reduceFrame_rf_new (k k' : Nat) :
    (Y).rf (.async i (.old (.store x y k'))) k = src k' := by
  rw [reduceFrame_rf]
  simp [reduceRf]

theorem reduceFrame_present_other (ho : X.tensorStores i = some o) {j : EvId} {p : Part}
    (hne : ¬ ReduceNew i x y (.async j p)) : (Y).AsyncPresent j p ↔ X.AsyncPresent j p := by
  by_cases hj : j = i
  · subst j
    cases p <;> try rfl
    all_goals simp only [Execution.AsyncPresent, Execution.recordStoreReduce,
      Execution.recordStoreEffects, ↓reduceIte, ho, Option.some.injEq, exists_eq_left']
    case readStore x' y' k' => rfl
    case writeStore x' y' k' =>
      rw [TensorStore.reduceElement_writeByte_other]
      rintro ⟨rfl, rfl⟩
      exact hne ⟨k', .inr rfl⟩
    case oldStore x' y' k' =>
      rw [TensorStore.reduceElement_oldByte_other]
      rintro ⟨rfl, rfl⟩
      exact hne ⟨k', .inl rfl⟩
    all_goals rfl
  · cases p <;> try rfl
    all_goals simp only [Execution.AsyncPresent, Execution.recordStoreReduce,
      Execution.recordStoreEffects, ite_eq_right hj]

theorem reduceFrame_refPresent_other (ho : X.tensorStores i = some o) {e : Ref}
    (hne : ¬ ReduceNew i x y e) : (Y).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p => exact reduceFrame_present_other ho hne

theorem reduceFrame_fullDone (ho : X.tensorStores i = some o) (j : EvId) :
    (Y).AsyncPresent j .fullDone ↔ X.AsyncPresent j .fullDone :=
  reduceFrame_present_other ho (by rintro ⟨k, h | h⟩ <;> cases h)

theorem reduceFrame_readsDone (ho : X.tensorStores i = some o) (j : EvId) :
    (Y).AsyncPresent j .readsDone ↔ X.AsyncPresent j .readsDone :=
  reduceFrame_present_other ho (by rintro ⟨k, h | h⟩ <;> cases h)

theorem reduceFrame_groupPresent (ho : X.tensorStores i = some o) (j : EvId) (k : GroupWait) :
    (∀ q ∈ GroupWaitStages Y j k, (Y).AsyncPresent j q) ↔
      ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q :=
  forall₂_congr fun q hq => by
    rcases groupWaitStages_cases X j k hq with rfl | rfl | rfl | rfl
    · exact reduceFrame_readsDone ho j
    · exact reduceFrame_fullDone ho j
    · exact Iff.rfl
    · exact Iff.rfl

theorem reduceFrame_finished (ho : X.tensorStores i = some o) (j : EvId) (p : Part) (w : EvId) :
    AsyncFinished L Y j p w ↔ AsyncFinished L X j p w :=
  or_congr (exists_congr fun k => and_congr_right fun _ => and_congr_right fun _ =>
    reduceFrame_groupPresent ho j k) Iff.rfl

theorem reduceFrame_onlyFinished (ho : X.tensorStores i = some o) (j : EvId) (p : Part)
    (w : EvId) : AsyncOnlyFinished Y j p w ↔ AsyncOnlyFinished X j p w :=
  and_congr_right fun _ => and_congr_right fun _ => reduceFrame_groupPresent ho j _

theorem reduceFrame_no_fullDone (hn : o.effects.fullDone = false) :
    ¬ (Y).AsyncPresent i .fullDone :=
  store_unfinished_no_fullDone (by
    simp [Execution.recordStoreReduce, Execution.recordStoreEffects,
      TensorStore.Observation.reduceElement, hn])

/-- Before the full completion of the store, no wait observes the completion of a new stage of
the element: a group wait that sees it waits for the full completion, and it notifies no
mbarrier. -/
theorem reduceFrame_new_not_finished (hn : o.effects.fullDone = false) {p : Part} {l : Loc}
    {w : EvId} (hp : ReduceNew i x y (.async i p)) (hc : AsyncCovers Y i p l) :
    ¬ AsyncFinished L Y i p w ∧ ¬ AsyncOnlyFinished Y i p w := by
  have hissue : ∃ pc addr s, (Y).get i = some ⟨pc, .tensorStore addr s⟩ := by
    obtain ⟨k, h | h⟩ := hp <;> obtain ⟨-, rfl⟩ := Ref.async.inj h
    · obtain ⟨a, w', ⟨-, s, addr, ⟨pc, hg⟩, -⟩, -⟩ := hc
      exact ⟨pc, addr, s, hg⟩
    · obtain ⟨a, w', ⟨-, s, addr, ⟨pc, hg⟩, -⟩, -⟩ := hc
      exact ⟨pc, addr, s, hg⟩
  obtain ⟨pc, addr, s, hg⟩ := hissue
  have hvis : ∀ k, GroupWaitVisible k p = true → Part.fullDone ∈ GroupWaitStages Y i k := by
    intro k hv
    unfold GroupWaitStages
    rw [hg]
    obtain ⟨k', h | h⟩ := hp <;> obtain ⟨-, rfl⟩ := Ref.async.inj h <;>
      rcases k with ⟨_ | _ | _⟩ | _ <;> simp_all [GroupWaitVisible]
  have htarget : p.target = none := by
    obtain ⟨k', h | h⟩ := hp <;> obtain ⟨-, rfl⟩ := Ref.async.inj h <;> rfl
  refine ⟨?_, ?_⟩
  · rintro (⟨k, hv, -, hall⟩ | ⟨ws, ⟨n, m, hN, -⟩, -⟩)
    · exact reduceFrame_no_fullDone hn (hall _ (hvis k hv))
    · obtain ⟨k', h | h⟩ := hp <;> obtain ⟨-, rfl⟩ := Ref.async.inj h <;> exact hN
  · rintro ⟨-, -, hall⟩
    refine reduceFrame_no_fullDone hn (hall _ ?_)
    unfold GroupWaitStages
    rw [hg]
    simp

theorem reduceFrame_new_no_before (hn : o.effects.fullDone = false) {l : Loc}
    {a b : EvId × Part} (ha : ReduceNew i x y (.async a.1 a.2)) : ¬ AsyncBefore L Y l a b := by
  obtain ⟨a1, a2⟩ := a
  have hi : a1 = i := by obtain ⟨k, h | h⟩ := ha <;> exact (Ref.async.inj h).1
  subst hi
  rintro ⟨hc, _, ⟨w, hf, _⟩ | ⟨w, hf, _⟩⟩
  · exact (reduceFrame_new_not_finished hn ha hc).1 hf
  · exact (reduceFrame_new_not_finished (L := L) hn ha hc).2 hf

theorem reduceFrame_new_no_vis (hn : o.effects.fullDone = false) {l : Loc} {e f : Ref}
    (he : ReduceNew i x y e) : ¬ modelCausality L Y l e f := by
  obtain ⟨k, rfl | rfl⟩ := he <;> cases f with
  | thread j =>
    rintro ⟨hc, w, hf, _⟩
    exact (reduceFrame_new_not_finished hn ⟨k, by simp⟩ hc).1 hf
  | async j p =>
    intro h
    obtain ⟨b, hb⟩ := h.2.first
    exact reduceFrame_new_no_before hn ⟨k, by simp⟩ hb

theorem reduceFrame_modelCausality (ho : X.tensorStores i = some o)
    (hn : o.effects.fullDone = false)
    (l : Loc) (e f : Ref) : modelCausality L Y l e f ↔ modelCausality L X l e f := by
  cases e <;> cases f
  · exact Iff.rfl
  · exact Iff.rfl
  · simp only [modelCausality, reduceFrame_finished ho]
    rfl
  · refine and_congr_right fun _ => ?_
    apply AsyncChain.congr_on_edges
      (fun a b => by simp only [AsyncBefore, reduceFrame_finished ho,
        reduceFrame_onlyFinished ho]; rfl)
    intro a b hedge
    apply reduceFrame_present_other ho
    intro hnew
    exact reduceFrame_new_no_before hn hnew hedge

private theorem reduceFrame_byteCausality (ho : X.tensorStores i = some o)
    (hn : o.effects.fullDone = false)
    {l : Loc} {e f : Ref} : ByteCausality L Y l e f → ByteCausality L X l e f :=
  ByteCausality.of_same_context (L := L) (X := X) («Y» := Y) rfl rfl
    (fun {l e f} => (reduceFrame_modelCausality ho hn l e f).mp) (fun h => h)

theorem reduceFrame_reads_other (ho : X.tensorStores i = some o) {e : Ref}
    (hne : ¬ ∃ k, e = .async i (.old (.store x y k))) (a : Acc) (bs : List (Option Byte)) :
    (Y).MemReads e a bs ↔ X.MemReads e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case readStore x' y' k' =>
      by_cases hj : j = i
      · subst j
        simp only [Execution.MemReads, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ↓reduceIte, ho, Option.some.injEq, exists_and_left, exists_eq_left']
        rfl
      · simp only [Execution.MemReads, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl
    case oldStore x' y' k' =>
      by_cases hj : j = i
      · subst j
        have hxy : ¬(x' = x ∧ y' = y) := by
          rintro ⟨rfl, rfl⟩
          exact hne ⟨k', rfl⟩
        simp only [Execution.MemReads, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ↓reduceIte, ho, Option.some.injEq, exists_and_left, exists_eq_left']
        rw [TensorStore.reduceElement_oldByte_other hxy]
        rfl
      · simp only [Execution.MemReads, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem reduceFrame_reads_new {k : Nat} {a : Acc}
    {bs : List (Option Byte)} (h : (Y).MemReads (.async i (.old (.store x y k))) a bs) :
    TensorStore.writeLoc o.spec x y k = some a.loc ∧ a.size = 1 ∧ bs = [some (old k)] := by
  obtain ⟨o', addr, b, ho', -, -, hl, hb, hs, rfl⟩ := h
  simp only [Execution.recordStoreReduce, Execution.recordStoreEffects, ↓reduceIte,
    Option.some.injEq] at ho'
  subst o'
  rw [TensorStore.reduceElement_oldByte_self] at hb
  obtain ⟨-, -, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨hl, hs, rfl⟩

theorem reduceFrame_writes_other (ho : X.tensorStores i = some o) {e : Ref}
    (hne : ¬ ∃ k, e = .async i (.write (.store x y k))) (a : Acc) (bs : List Byte) :
    (Y).MemWrites e a bs ↔ X.MemWrites e a bs := by
  cases e with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case writeStore x' y' k' =>
      by_cases hj : j = i
      · subst j
        have hxy : ¬(x' = x ∧ y' = y) := by
          rintro ⟨rfl, rfl⟩
          exact hne ⟨k', rfl⟩
        simp only [Execution.MemWrites, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ↓reduceIte, ho, Option.some.injEq, exists_and_left, exists_eq_left']
        rw [TensorStore.reduceElement_writeByte_other hxy]
        rfl
      · simp only [Execution.MemWrites, Execution.recordStoreReduce, Execution.recordStoreEffects,
          ite_eq_right hj]
        rfl

theorem reduceFrame_no_old_read (ho : X.tensorStores i = some o)
    (hc : TensorStore.CopyOk o.spec o.effects) (hp : TensorStore.ElementPending o x y) (k : Nat)
    (a : Acc) (bs : List (Option Byte)) : ¬ X.MemReads (.async i (.old (.store x y k))) a bs := by
  rintro ⟨o', addr, b, ho', -, -, -, hb, -⟩
  rw [ho] at ho'
  cases ho'
  unfold TensorStore.oldByte at hb
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [hs] at hb
  | some s =>
    have hcs := TensorCopy.slotAt_coordinates hs
    rw [hs, Option.bind_some, hp.old_none hc s hcs.1 hcs.2.1] at hb
    cases hb

theorem reduceFrame_le (ho : X.tensorStores i = some o) (hc : TensorStore.CopyOk o.spec o.effects)
    (hp : TensorStore.ElementPending o x y) : X.le Y := by
  refine Execution.le_recordStoreEffects ?_ ?_
  · intro prior hprior
    rw [ho] at hprior
    cases hprior
    exact TensorStore.reduceElement_extends hc hp
  · rintro e k ⟨a, bs, he⟩
    refine reduceFrame_rf_other (o := o) (old := old) (new := new) ?_ k
    rintro ⟨k', rfl⟩
    exact reduceFrame_no_old_read ho hc hp k' a bs he

theorem reduceFrame_writes_lift (ho : X.tensorStores i = some o)
    (hc : TensorStore.CopyOk o.spec o.effects) (hp : TensorStore.ElementPending o x y)
    {w : Ref} {a : Acc} {bs : List Byte} (h : X.MemWrites w a bs) : (Y).MemWrites w a bs :=
  Execution.le_memWrites (reduceFrame_le ho hc hp) h

theorem reduceFrame_new_write_absent (ho : X.tensorStores i = some o)
    (hp : TensorStore.ElementPending o x y) {k : Nat} {a : Acc} {bs : List Byte} :
    ¬ X.MemWrites (.async i (.write (.store x y k))) a bs := by
  rintro ⟨o', addr, b, ho', -, -, hb, -⟩
  rw [ho] at ho'
  cases ho'
  unfold TensorStore.writeByte at hb
  cases hs : TensorTransfer.slotAt o.spec.descriptor x y k with
  | none => simp [hs] at hb
  | some s =>
    have hcs := TensorCopy.slotAt_coordinates hs
    rw [hs, Option.bind_some, (hp s hcs.1 hcs.2.1).2.2] at hb
    cases hb

/-- A new stage of the element starts no stage edge: the full completion is absent. -/
theorem reduceFrame_new_no_edge (hn : o.effects.fullDone = false) {e : Ref}
    (he : ReduceNew i x y e) (f : Ref) : ¬ StageEdge Y e f := by
  intro h
  obtain ⟨k, rfl | rfl⟩ := he <;> cases f with
  | thread j => exact h
  | async j p =>
    cases p <;> try exact h
    all_goals first
      | (obtain ⟨rfl, -, hd⟩ := h
         exact reduceFrame_no_fullDone (src := src) (old := old) (new := new) (x := x) (y := y)
           hn hd)
      | (obtain ⟨rfl, hm, -⟩ := h
         simp [AsyncCopy.Part.target] at hm)

/-- The new stages of the element, when absent before, and the returns of the waits they witness
form a sink; outside them every order relation is old. -/
theorem reduceFrame_order {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i = some o)
    (hn : o.effects.fullDone = false) : OrderOk L K A Y :=
  (sinkFrame_effect (R := reduceRf X i x y src)
    (S := fun j => if j = i then some (o.reduceElement x y old new) else X.tensorStores j) hX
    (fun e => ReduceNew i x y e ∧ ¬ X.RefPresent e)
    (by rintro j ⟨⟨k, h | h⟩, -⟩ <;> cases h) (fun _ _ he => he.2)
    (fun e he h => by
      by_cases hr : ReduceNew i x y e
      · by_contra hx
        exact he ⟨hr, hx⟩
      · exact (reduceFrame_refPresent_other ho hr).mp h)
    (recordStoreEffects_needs hX.tma.2.2.1) (fun _ _ => rfl) (fun _ _ _ _ h => h)
    (fun _ f he => reduceFrame_new_no_edge hn he.1 f)
    (fun m r hr he => by
      have hm := ((hX.tma.2.2.1 m).2.1 r hr).1
      obtain ⟨⟨k, h | h⟩, -⟩ := he <;> rw [h] at hm <;> simp [objectAction] at hm)).orderOk
    hX.orderOk

/-- The value of byte `k` of element `(x, y)` lies in a slot when the element exists. -/
theorem slotAt_of_element {o : TensorStore.Observation} {x y k : Nat}
    (hex : ∃ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x ∧ s.2.1.val = y)
    (hk : k < o.spec.descriptor.format.bytes) :
    ∃ s, TensorTransfer.slotAt o.spec.descriptor x y k = some s := by
  obtain ⟨⟨⟨x', hx⟩, ⟨y', hy⟩, _⟩, rfl, rfl⟩ := hex
  refine ⟨(⟨x', hx⟩, ⟨y', hy⟩, ⟨k, hk⟩), ?_⟩
  simp [TensorTransfer.slotAt, hx, hy, hk]

theorem reduceFrame_rfWf {mem0 : Mem0} (hX : RfWf mem0 X) (ho : X.tensorStores i = some o)
    (hc : TensorStore.CopyOk o.spec o.effects) (hp : TensorStore.ElementPending o x y)
    (hsrc : ∀ k loc, TensorStore.writeLoc o.spec x y k = some loc →
      match src k with
      | none => ∀ c, mem0 loc = some c → some (old k) = X.initialByte c loc
      | some w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers loc ∧
          some (old k) = wbyte a' bs' loc) :
    RfWf mem0 Y := by
  intro e a bs he
  by_cases hnew : ∃ k, e = .async i (.old (.store x y k))
  · obtain ⟨k, rfl⟩ := hnew
    obtain ⟨hl, hs, rfl⟩ := reduceFrame_reads_new he
    refine ⟨by simp [hs], fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    have hat : a.loc.at 0 = a.loc := by simp [Loc.at]
    rw [reduceFrame_rf_new, hat]
    have h := hsrc k a.loc hl
    cases hsk : src k with
    | none =>
      rw [hsk] at h
      intro c hc'
      simp [h c hc']
      rfl
    | some w =>
      rw [hsk] at h
      obtain ⟨a', bs', hw, hcov, hv⟩ := h
      exact ⟨a', bs', reduceFrame_writes_lift ho hc hp hw, hcov, by simp [hv]⟩
  · obtain ⟨hlen, hv⟩ := hX e a bs ((reduceFrame_reads_other ho hnew a bs).mp he)
    refine ⟨hlen, fun k hk => ?_⟩
    have h := hv k hk
    rw [reduceFrame_rf_other hnew]
    cases hs : X.rf e k with
    | none => rw [hs] at h; exact h
    | some w =>
      rw [hs] at h
      obtain ⟨a', bs', hw, hcov, hval⟩ := h
      exact ⟨a', bs', reduceFrame_writes_lift ho hc hp hw, hcov, hval⟩

theorem reduceFrame_noFuture (hX : NoFuture L X) (ho : X.tensorStores i = some o)
    (hn : o.effects.fullDone = false) : NoFuture L Y := by
  intro e a bs k w he hk hs hv
  by_cases hnew : ∃ k', e = .async i (.old (.store x y k'))
  · obtain ⟨k', rfl⟩ := hnew
    obtain ⟨first, hfirst⟩ := hv.starts
    exact reduceFrame_new_no_vis hn ⟨k', .inl rfl⟩ (f := first) hfirst
  · rw [reduceFrame_rf_other hnew] at hs
    exact hX e a bs k w ((reduceFrame_reads_other ho hnew a bs).mp he) hk hs
      (reduceFrame_byteCausality ho hn hv)

theorem reduceFrame_hidden (hX : Hidden L X) (ho : X.tensorStores i = some o)
    (hn : o.effects.fullDone = false)
    (hhid : ∀ k loc, TensorStore.writeLoc o.spec x y k = some loc → ∀ w a' bs',
      X.MemWrites w a' bs' → a'.Covers loc → modelCausality L X loc w
          (.async i (.old (.store x y k))) →
      match src k with
      | none => False
      | some w' => ¬ modelCausality L X loc w' w) : Hidden L Y := by
  intro e a bs k w a' bs' he hk hw hc hv
  by_cases hwn : ∃ k', w = .async i (.write (.store x y k'))
  · obtain ⟨k', rfl⟩ := hwn
    obtain ⟨first, hfirst⟩ := hv.starts
    exact (reduceFrame_new_no_vis hn ⟨k', .inr rfl⟩ (f := first) hfirst).elim
  have hwX := (reduceFrame_writes_other ho hwn a' bs').mp hw
  have hvX := reduceFrame_byteCausality ho hn hv
  by_cases hnew : ∃ k', e = .async i (.old (.store x y k'))
  · obtain ⟨k', rfl⟩ := hnew
    obtain ⟨hl, hs, rfl⟩ := reduceFrame_reads_new he
    have hk0 : k = 0 := by omega
    subst hk0
    have hat : a.loc.at 0 = a.loc := by simp [Loc.at]
    rw [hat] at hc hvX
    have hglobal : a.loc.space = .global := by
      obtain ⟨slot, -, hd⟩ := Option.bind_eq_some_iff.mp hl
      obtain ⟨address, -, heq⟩ := Option.map_eq_some_iff.mp hd
      rw [← heq]
    have h := hhid k' a.loc hl w a' bs' hwX hc
      ((ByteCausality.direct_iff_of_global hglobal).mp hvX)
    change match (Y).rf _ 0 with
      | none => False
      | some w' => ¬ ByteCausality L Y (a.loc.at 0) w' w
    rw [reduceFrame_rf_new, hat]
    cases hsk : src k' with
    | none => rw [hsk] at h; exact h
    | some w' =>
      rw [hsk] at h
      exact fun hh => h ((ByteCausality.direct_iff_of_global hglobal).mp
        (reduceFrame_byteCausality ho hn hh))
  · have h := hX e a bs k w a' bs' ((reduceFrame_reads_other ho hnew a bs).mp he) hk hwX hc hvX
    change match (Y).rf e k with
      | none => False
      | some w' => ¬ ByteCausality L Y (a.loc.at k) w' w
    rw [reduceFrame_rf_other hnew]
    cases hs : X.rf e k with
    | none => rw [hs] at h; exact h
    | some w' =>
      rw [hs] at h
      exact fun hh => h (reduceFrame_byteCausality ho hn hh)

/-- A performed reduction element's old byte `k` of its element is an actual read. -/
theorem reduced_old_read {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {j : EvId} {x' y' k : Nat} {fp : Acc}
    (h : TensorStore.Reduced X j x' y' fp) (hk : k < fp.size) :
    ∃ a bs, X.MemReads (.async j (.old (.store x' y' k))) a bs := by
  obtain ⟨oX, red, loc, hoX, hr, hl, rfl, hw⟩ := h
  obtain ⟨hi, -, hc⟩ := hX.store j oX hoX
  obtain ⟨addr, hiss⟩ := hi
  unfold TensorStore.writeByte at hw
  cases hs0 : TensorTransfer.slotAt oX.spec.descriptor x' y' 0 with
  | none => simp [hs0] at hw
  | some s0 =>
    rw [hs0, Option.bind_some] at hw
    cases hb0 : oX.effects.write s0 with
    | none => rw [hb0] at hw; cases hw
    | some b0 =>
      have hc0 := TensorCopy.slotAt_coordinates hs0
      obtain ⟨sk, hsk⟩ := slotAt_of_element (o := oX) ⟨s0, hc0.1, hc0.2.1⟩ hk
      have hck := TensorCopy.slotAt_coordinates hsk
      obtain ⟨⟨bw, hbw⟩, ⟨bo, hbo⟩⟩ := hc.element s0 b0 hb0 (by rw [hr]; rfl) sk
        (Fin.ext (hck.1.trans hc0.1.symm)) (Fin.ext (hck.2.1.trans hc0.2.1.symm))
      obtain ⟨⟨lk, hlk⟩, -⟩ := hc.writes sk bw hbw
      refine ⟨{ loc := lk, size := 1 }, [some bo], oX, addr, bo, hoX, hiss, by rw [hr]; rfl,
        ?_, ?_, rfl, rfl⟩
      · simp [TensorStore.writeLoc, hsk, hlk]
      · simp [TensorStore.oldByte, hsk, hbo]

theorem reduceFrame_elem_other (ho : X.tensorStores i = some o) {j : EvId} {x' y' : Nat}
    {o' : TensorStore.Observation} (ho' : (Y).tensorStores j = some o')
    (hne : (j, x', y') ≠ (i, x, y)) :
    ∃ oX, X.tensorStores j = some oX ∧ oX.spec = o'.spec ∧ ∀ k,
      TensorStore.writeByte o' x' y' k = TensorStore.writeByte oX x' y' k ∧
      TensorStore.oldByte o' x' y' k = TensorStore.oldByte oX x' y' k ∧
      TensorStore.readByte o' x' y' k = TensorStore.readByte oX x' y' k := by
  by_cases hj : j = i
  · subst j
    simp only [Execution.recordStoreReduce, Execution.recordStoreEffects, ↓reduceIte,
      Option.some.injEq] at ho'
    subst o'
    have hxy : ¬(x' = x ∧ y' = y) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
    exact ⟨o, ho, rfl, fun k => ⟨TensorStore.reduceElement_writeByte_other hxy,
      TensorStore.reduceElement_oldByte_other hxy, rfl⟩⟩
  · simp only [Execution.recordStoreReduce, Execution.recordStoreEffects, ite_eq_right hj] at ho'
    exact ⟨o', ho', rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩

theorem reduceFrame_reduced (ho : X.tensorStores i = some o) {j : EvId} {x' y' : Nat} {fp : Acc}
    (h : TensorStore.Reduced Y j x' y' fp) :
    (j, x', y') = (i, x, y) ∨ ((j, x', y') ≠ (i, x, y) ∧ TensorStore.Reduced X j x' y' fp) := by
  by_cases hn : (j, x', y') = (i, x, y)
  · exact .inl hn
  · refine .inr ⟨hn, ?_⟩
    obtain ⟨o', red, loc, ho', hr, hl, rfl, hw⟩ := h
    obtain ⟨oX, hoX, hsp, hb⟩ := reduceFrame_elem_other ho ho' hn
    refine ⟨oX, red, loc, hoX, hsp ▸ hr, hsp ▸ hl, by rw [hsp], ?_⟩
    rw [← (hb 0).1]
    exact hw

theorem reduceFrame_rf_elem (q : EvId × Nat × Nat) (hq : q ≠ (i, x, y)) (k n : Nat) :
    (Y).rf (.async q.1 (.old (.store q.2.1 q.2.2 k))) n =
      X.rf (.async q.1 (.old (.store q.2.1 q.2.2 k))) n := by
  apply reduceFrame_rf_other
  rintro ⟨k', h⟩
  obtain ⟨h1, h2⟩ := Ref.async.inj h
  cases h2
  exact hq (by rw [← h1])

theorem reduceFrame_new_value {A : List Assumption} {red red' : AtomOp}
    (hred : o.spec.reduce = some red)
    (hex : ∃ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x ∧ s.2.1.val = y)
    (hvalue : ∀ v, TensorStore.reduceValue A red o.spec.descriptor.format
      ((List.range o.spec.descriptor.format.bytes).map fun k => some (old k))
      (TensorStore.elementBytes TensorStore.readByte o x y) = .ok v →
      ∀ k < o.spec.descriptor.format.bytes, new k = v.byteAt k)
    {o' : TensorStore.Observation} (ho' : (Y).tensorStores i = some o')
    (hr : o'.spec.reduce = some red') {v : Value}
    (hv : TensorStore.reduceValue A red' o'.spec.descriptor.format
      (TensorStore.elementBytes TensorStore.oldByte o' x y)
      (TensorStore.elementBytes TensorStore.readByte o' x y) = .ok v)
    {k : Nat} (hk : k < o'.spec.descriptor.format.bytes) :
    TensorStore.writeByte o' x y k = some (v.byteAt k) := by
  simp only [Execution.recordStoreReduce, Execution.recordStoreEffects, ↓reduceIte,
    Option.some.injEq] at ho'
  subst o'
  rw [TensorStore.reduceElement_spec, hred] at hr
  cases hr
  rw [TensorStore.reduceElement_spec] at hk hv
  have hold : TensorStore.elementBytes TensorStore.oldByte (o.reduceElement x y old new) x y =
      (List.range o.spec.descriptor.format.bytes).map fun k => some (old k) := by
    unfold TensorStore.elementBytes
    rw [TensorStore.reduceElement_spec]
    refine List.map_congr_left fun j hj => ?_
    rw [TensorStore.reduceElement_oldByte_self]
    obtain ⟨sj, hsj⟩ := slotAt_of_element hex (List.mem_range.mp hj)
    rw [hsj]
    rfl
  rw [hold] at hv
  have hnew := hvalue v hv k hk
  rw [TensorStore.reduceElement_writeByte_self]
  obtain ⟨sk, hsk⟩ := slotAt_of_element hex hk
  rw [hsk, hnew]
  rfl

theorem reduceFrame_reduceOk {K : Kernel} {A : List Assumption} {mem0 : Mem0} {red : AtomOp}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i = some o)
    (hred : o.spec.reduce = some red)
    (hex : ∃ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x ∧ s.2.1.val = y)
    (hvalue : ∀ v, TensorStore.reduceValue A red o.spec.descriptor.format
      ((List.range o.spec.descriptor.format.bytes).map fun k => some (old k))
      (TensorStore.elementBytes TensorStore.readByte o x y) = .ok v →
      ∀ k < o.spec.descriptor.format.bytes, new k = v.byteAt k) :
    TensorStore.ReduceOk A Y := by
  refine ⟨?_, hX.reduce.copies⟩
  intro j o' red' x' y' v ho' hr hw hv k hk
  by_cases hn : (j, x', y') = (i, x, y)
  · simp only [Prod.mk.injEq] at hn
    obtain ⟨rfl, rfl, rfl⟩ := hn
    exact reduceFrame_new_value hred hex hvalue ho' hr hv hk
  · obtain ⟨oX, hoX, hsp, hb⟩ := reduceFrame_elem_other ho ho' hn
    have hold : TensorStore.elementBytes TensorStore.oldByte o' x' y' =
        TensorStore.elementBytes TensorStore.oldByte oX x' y' := by
      unfold TensorStore.elementBytes; rw [hsp]; exact List.map_congr_left fun k _ => (hb k).2.1
    have hsrc' : TensorStore.elementBytes TensorStore.readByte o' x' y' =
        TensorStore.elementBytes TensorStore.readByte oX x' y' := by
      unfold TensorStore.elementBytes; rw [hsp]; exact List.map_congr_left fun k _ => (hb k).2.2
    rw [hold, hsrc', ← hsp] at hv
    rw [(hb k).1]
    exact hX.reduce.values j oX red' x' y' v hoX (hsp ▸ hr) ((hb 0).1 ▸ hw) hv k (hsp ▸ hk)

/-- The source of a byte of the old value of a performed atomic operation is a write (MEM-READS-FROM
of its old-value read). -/
theorem rmwAt_oldRf_write {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {q : RmwId} {l : Loc} {n k : Nat} {w : Ref}
    (hq : X.RmwAt q l n) (hk : k < n) (h : X.oldRf q k = some w) :
    ∃ a bs, X.MemWrites w a bs := by
  have hsrc : ∀ e a bs, X.MemReads e a bs → ∀ k' < a.size, X.rf e k' = some w →
      ∃ a bs, X.MemWrites w a bs := by
    intro e a bs hr k' hk' hrf
    have hv := (hX.rf e a bs hr).2 k' hk'
    rw [hrf] at hv
    obtain ⟨a', bs', hw, -⟩ := hv
    exact ⟨a', bs', hw⟩
  cases q with
  | thread e =>
    obtain ⟨a, old', new', hr, rfl, rfl⟩ := hq
    exact hsrc (.thread e) a old' (Or.inr ⟨new', hr⟩) k hk h
  | tensor j x' y' =>
    obtain ⟨fp, hfp, -, rfl⟩ := hq
    obtain ⟨a, bs, hr⟩ := reduced_old_read hX hfp hk
    have ha : a.size = 1 := by
      obtain ⟨_, _, _, _, _, _, _, _, hs1, _⟩ := hr
      exact hs1
    exact hsrc _ a bs hr 0 (by omega) h
  | copy j e =>
    obtain ⟨s, r, a, ⟨pc, hc⟩, hw, hel, hws, -, rfl⟩ := hq
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hws
    have hne : AsyncCopy.nonempty (X.async.copies j) := ⟨.write (.elem e), by
      simp [AsyncCopy.present, hbs]⟩
    obtain ⟨s', hs', hok⟩ := hX.tma.1 j hne
    have hss : s' = s := by
      simp only [AsyncCopy.issuedBy, hc] at hs'
      exact (Option.some.inj hs').symm
    subst hss
    obtain ⟨raw, hraw⟩ := (hok.2.2.2.2.1 e bs hbs).2.2.2 r hw
    exact hsrc (.async j (.old (.elem e))) a (raw.map some)
      ⟨s', r, raw, ⟨pc, hc⟩, hw, hel, hraw, rfl⟩ k hk h

theorem reduceFrame_rmwAt_old (ho : X.tensorStores i = some o) {q : RmwId}
    (hq : q ≠ .tensor i x y) {l : Loc} {n : Nat} : (Y).RmwAt q l n ↔ X.RmwAt q l n := by
  cases q with
  | thread e => exact Iff.rfl
  | copy j e => exact Iff.rfl
  | tensor j x' y' =>
    have hne : (j, x', y') ≠ (i, x, y) := fun h => hq (by simp_all)
    constructor
    · rintro ⟨fp, hfp, hl, hn⟩
      rcases reduceFrame_reduced ho hfp with h | ⟨-, h⟩
      · exact (hne h).elim
      · exact ⟨fp, h, hl, hn⟩
    · rintro ⟨fp, ⟨oX, red, loc, hoX, hr, hw0, rfl, hw⟩, hl, hn⟩
      refine ⟨_, ?_, hl, hn⟩
      by_cases hj : j = i
      · subst j
        rw [ho] at hoX
        cases hoX
        have hxy : ¬(x' = x ∧ y' = y) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
        refine ⟨o.reduceElement x y old new, red, loc, ?_, hr, hw0, rfl, ?_⟩
        · simp [Execution.recordStoreReduce, Execution.recordStoreEffects]
        · rw [TensorStore.reduceElement_writeByte_other hxy]
          exact hw
      · refine ⟨oX, red, loc, ?_, hr, hw0, rfl, hw⟩
        simp [Execution.recordStoreReduce, Execution.recordStoreEffects, hj, hoX]

theorem reduceFrame_oldRf_old {q : RmwId} (hq : q ≠ .tensor i x y) (k : Nat) :
    (Y).oldRf q k = X.oldRf q k := by
  cases q with
  | thread e => rfl
  | tensor j x' y' =>
    exact reduceFrame_rf_elem (j, x', y') (fun h => hq (by simp_all)) k 0
  | copy j e =>
    exact reduceFrame_rf_other (by rintro ⟨k', h⟩; cases h) k

/-- MEM-ATOMICITY of the extension: the new element reads its old value from sources that no other
morally strong atomic operation at its footprint read (`hunique`), and it is read by none, because
its write was absent and every old-value source is a write. -/
theorem reduceFrame_atomicOk {K : Kernel} {A : List Assumption} {mem0 : Mem0} {loc0 : Loc}
    (hX : Consistent L K A mem0 X) (ho : X.tensorStores i = some o)
    (hp : TensorStore.ElementPending o x y)
    (hex : ∃ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x ∧ s.2.1.val = y)
    (hl0 : TensorStore.writeLoc o.spec x y 0 = some loc0)
    (hsrc : ∀ k loc, TensorStore.writeLoc o.spec x y k = some loc →
      match src k with
      | none => ∀ c, mem0 loc = some c → some (old k) = X.initialByte c loc
      | some w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers loc ∧ some (old k) = wbyte a' bs' loc)
    (hunique : ∀ q, q ≠ .tensor i x y → X.RmwAt q loc0 o.spec.descriptor.format.bytes →
      ∀ k < o.spec.descriptor.format.bytes, X.oldRf q k ≠ src k) :
    AtomicOk L Y := by
  have hloc : ∀ k < o.spec.descriptor.format.bytes, ∃ loc,
      TensorStore.writeLoc o.spec x y k = some loc := by
    intro k hk
    obtain ⟨sk, hsk⟩ := slotAt_of_element hex hk
    have hck := TensorCopy.slotAt_coordinates hsk
    obtain ⟨⟨loc, hl⟩, -⟩ := hp sk hck.1 hck.2.1
    exact ⟨loc, by simp [TensorStore.writeLoc, hsk, hl]⟩
  have hnewAt : ∀ {l n}, (Y).RmwAt (.tensor i x y) l n →
      l = loc0 ∧ n = o.spec.descriptor.format.bytes := by
    rintro l n ⟨fp, ⟨o', red', loc, ho', -, hl, rfl, -⟩, rfl, rfl⟩
    simp only [Execution.recordStoreReduce, Execution.recordStoreEffects, ↓reduceIte,
      Option.some.injEq] at ho'
    subst o'
    change TensorStore.writeLoc o.spec x y 0 = some loc at hl
    rw [hl0] at hl
    cases hl
    exact ⟨rfl, rfl⟩
  have hnewRf : ∀ k, (Y).oldRf (.tensor i x y) k = src k := fun k => reduceFrame_rf_new 0 k
  refine ⟨fun p q l n k hpq hqq hne hs hk => ?_, fun e hcyc => ?_⟩
  · by_cases hp0 : p = .tensor i x y
    · subst hp0
      have hq0 : q ≠ .tensor i x y := fun h => hne h.symm
      obtain ⟨rfl, rfl⟩ := hnewAt hpq
      rw [hnewRf, reduceFrame_oldRf_old hq0]
      exact fun h => hunique q hq0 ((reduceFrame_rmwAt_old ho hq0).mp hqq) k hk h.symm
    · by_cases hq0 : q = .tensor i x y
      · subst hq0
        obtain ⟨rfl, rfl⟩ := hnewAt hqq
        rw [hnewRf, reduceFrame_oldRf_old hp0]
        exact hunique p hp0 ((reduceFrame_rmwAt_old ho hp0).mp hpq) k hk
      · rw [reduceFrame_oldRf_old hp0, reduceFrame_oldRf_old hq0]
        exact hX.atomic.unique p q l n k ((reduceFrame_rmwAt_old ho hp0).mp hpq)
          ((reduceFrame_rmwAt_old ho hq0).mp hqq) hne ((rmwStrong_congr rfl rfl).mp hs) hk
  · -- No atomic operation reads the new element: its write was absent from `X`.
    have hnoOut : ∀ b, ¬ AtomicReads L Y (.tensor i x y) b := by
      rintro b ⟨l, n, ha, hb, -, k, k', hk, hrf⟩
      obtain ⟨rfl, rfl⟩ := hnewAt ha
      have hwX : ∃ a bs, X.MemWrites (.async i (.write (.store x y k'))) a bs := by
        by_cases hb0 : b = .tensor i x y
        · subst hb0
          rw [hnewRf] at hrf
          obtain ⟨loc, hl⟩ := hloc k hk
          have h := hsrc k loc hl
          rw [hrf] at h
          obtain ⟨a', bs', hw, -⟩ := h
          exact ⟨a', bs', hw⟩
        · rw [reduceFrame_oldRf_old hb0] at hrf
          exact rmwAt_oldRf_write hX ((reduceFrame_rmwAt_old ho hb0).mp hb) hk hrf
      obtain ⟨a, bs, hw⟩ := hwX
      exact reduceFrame_new_write_absent ho hp hw
    have hstep : ∀ a b, AtomicReads L Y a b → b ≠ .tensor i x y →
        a ≠ .tensor i x y ∧ AtomicReads L X a b := by
      intro a b hab hb
      have ha : a ≠ .tensor i x y := by rintro rfl; exact hnoOut b hab
      obtain ⟨l, n, hra, hrb, hs, k, k', hk, hrf⟩ := hab
      refine ⟨ha, l, n, (reduceFrame_rmwAt_old ho ha).mp hra, (reduceFrame_rmwAt_old ho hb).mp hrb,
        (rmwStrong_congr rfl rfl).mp hs, k, k', hk, ?_⟩
      rw [← reduceFrame_oldRf_old hb]
      exact hrf
    have hpath : ∀ a b, Relation.TransGen (AtomicReads L Y) a b → b ≠ .tensor i x y →
        Relation.TransGen (AtomicReads L X) a b := by
      intro a b h
      induction h with
      | single h => exact fun hb => .single (hstep _ _ h hb).2
      | tail _ h ih =>
        intro hb
        have hs := hstep _ _ h hb
        exact (ih hs.1).tail hs.2
    by_cases he : e = .tensor i x y
    · subst he
      obtain ⟨c, hc', -⟩ := Relation.TransGen.head'_iff.mp hcyc
      exact hnoOut c hc'
    · exact hX.atomic.acyclic e (hpath e e hcyc he)

/-- **A pending reduction element completes.** Its old bytes read from the chosen sources and
its bytes are written in one consistent extension step. -/
theorem consistent_storeReduce {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {red : AtomOp} {loc0 : Loc} (hX : Consistent L K A mem0 X)
    (ho : X.tensorStores i = some o) (hred : o.spec.reduce = some red)
    (hp : TensorStore.ElementPending o x y)
    (hex : ∃ s : TensorTransfer.Slot o.spec.descriptor, s.1.val = x ∧ s.2.1.val = y)
    (hl0 : TensorStore.writeLoc o.spec x y 0 = some loc0)
    (hsrc : ∀ k loc, TensorStore.writeLoc o.spec x y k = some loc →
      match src k with
      | none => ∀ c, mem0 loc = some c → some (old k) = X.initialByte c loc
      | some w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers loc ∧ some (old k) = wbyte a' bs' loc)
    (hhid : ∀ k loc, TensorStore.writeLoc o.spec x y k = some loc → ∀ w a' bs',
      X.MemWrites w a' bs' → a'.Covers loc → modelCausality L X loc w
          (.async i (.old (.store x y k))) →
      match src k with
      | none => False
      | some w' => ¬ modelCausality L X loc w' w)
    (hunique : ∀ q, q ≠ .tensor i x y → X.RmwAt q loc0 o.spec.descriptor.format.bytes →
      ∀ k < o.spec.descriptor.format.bytes, X.oldRf q k ≠ src k)
    (hvalue : ∀ v, TensorStore.reduceValue A red o.spec.descriptor.format
      ((List.range o.spec.descriptor.format.bytes).map fun k => some (old k))
      (TensorStore.elementBytes TensorStore.readByte o x y) = .ok v →
      ∀ k < o.spec.descriptor.format.bytes, new k = v.byteAt k)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) : Consistent L K A mem0 Y := by
  obtain ⟨hi, hvalid, hc⟩ := hX.store i o ho
  have hn : o.effects.fullDone = false := by
    obtain ⟨s, h1, h2⟩ := hex
    obtain ⟨⟨loc, hd⟩, -, hw⟩ := hp s h1 h2
    exact TensorStore.missing_required_before_fullDone hc hd hw
  exact consistent_recordStoreEffects hX hi hvalid
    (TensorStore.reduceElement_copyOk hc hred hp hn)
    (fun prior hprior => by
      rw [ho] at hprior
      cases hprior
      exact TensorStore.reduceElement_extends hc hp)
    (reduceFrame_rfWf hX.rf ho hc hp hsrc) (reduceFrame_order hX ho hn)
    (reduceFrame_noFuture hX.noFuture ho hn) (reduceFrame_hidden hX.hidden ho hn hhid)
    (fun _ _ => rfl)
    (reduceFrame_reduceOk hX ho hred hex hvalue) hasm
    (reduceFrame_atomicOk hX ho hp hex hl0 hsrc hunique)

end
end PTX
