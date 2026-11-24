-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Read
public import Lemmas.Snoc.PlainExtend
public import Lemmas.Order.ByteCausalityAcyclic

@[expose] public section

/-! # A source for every byte of a new read

A proof tool. The writes of an execution are finitely many (`writers_finite`): the thread writes
and bulk copy writes of its events, the response writes to the targets of its cancellation
requests, and the slot writes of its observed tensor copies and stores. Each byte of a new read
can therefore take its value from a write covering it that no other covering write follows in
byte visibility (`ByteCausality.acyclic`, under guarded synchronization), or from the launch
content when no write covers it (`newRead_exists`). Such a source is never hidden behind a write the
read sees, so a released thread can perform any read (`read_source_counted_extension`), given the
assumptions' constraints for the extension whose bytes have such sources. -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {X : Execution} {mem0 : Mem0} {g : Nat}

/-- The element slots of a tensor transfer. -/
def slotTriples {outer : Nat} (d : TensorDescriptor.Descriptor outer) : List (Nat × Nat × Nat) :=
  (List.range (TensorTile.count d.box 0)).flatMap fun x =>
    (List.range (TensorTile.rows d.box)).flatMap fun y =>
      (List.range d.format.bytes).map fun k => (x, y, k)

theorem mem_slotTriples {outer : Nat} {d : TensorDescriptor.Descriptor outer} {x y k : Nat}
    (h : (TensorTransfer.slotAt d x y k).isSome) : (x, y, k) ∈ slotTriples d := by
  unfold TensorTransfer.slotAt at h
  split_ifs at h with hx hy hk
  · simp [slotTriples, hx, hy, hk]
  all_goals simp at h

/-- The references of the writes issued by event `i`. -/
def writeRefs (X : Execution) (i : EvId) : List Ref :=
  [.thread i, .async i (.write .copy)] ++
  (match X.get i with
    | some ⟨_, .clcIssue _ ts⟩ => ts.map fun c => .async i (.write (.cta c))
    | some ⟨_, .copy s⟩ => (List.range s.elems.length).map fun j => .async i (.write (.elem j))
    | _ => []) ++
  (match X.tensor i with
    | some o => (slotTriples o.spec.descriptor).map fun p =>
      .async i (.write (.load p.1 p.2.1 p.2.2))
    | none => []) ++
  (match X.tensorStores i with
    | some o => (slotTriples o.spec.descriptor).map fun p =>
      .async i (.write (.store p.1 p.2.1 p.2.2))
    | none => [])

/-- **The writes of an execution are finitely many.** -/
theorem writers_finite (hX : Consistent L K A mem0 X) :
    ∃ ws : List Ref, ∀ w a bs, X.MemWrites w a bs → w ∈ ws := by
  refine ⟨(X.events L).flatMap (writeRefs X), fun w a bs hw => ?_⟩
  have hev : ∀ {i : EvId} {ev : Event}, X.get i = some ev → i ∈ X.events L := by
    intro i ev he
    have hl := len_of_get he
    refine mem_events ?_ hl
    by_contra hn
    rw [hX.outside i.1 (by omega)] at hl
    simp at hl
  simp only [List.mem_flatMap]
  cases w with
  | thread i =>
    rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩ <;> exact ⟨i, hev he, by simp [writeRefs]⟩
  | async i p =>
    cases p
    case writeCopy =>
      obtain ⟨s, ⟨pc, he⟩, -⟩ := hw
      exact ⟨i, hev he, by simp [writeRefs]⟩
    case writeElem j =>
      obtain ⟨s, ⟨pc, he⟩, hj, -⟩ := hw
      have hl : j < s.elems.length := (List.getElem?_eq_some_iff.mp hj).1
      exact ⟨i, hev he, by simp [writeRefs, he, hl]⟩
    case writeCta c =>
      obtain ⟨s, ts, ⟨pc, he⟩, hc, -⟩ := hw
      exact ⟨i, hev he, by simp [writeRefs, he, hc]⟩
    case writeLoad x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, he⟩, hl, -⟩ := hw
      have hs : (TensorTransfer.slotAt o.spec.descriptor x y k).isSome := by
        unfold TensorCopy.writeLoc at hl
        cases h : TensorTransfer.slotAt o.spec.descriptor x y k <;> simp_all
      refine ⟨i, hev he, ?_⟩
      simp only [writeRefs, ho, List.mem_append, List.mem_map]
      exact .inl (.inr ⟨(x, y, k), mem_slotTriples hs, rfl⟩)
    case writeStore x y k =>
      obtain ⟨o, addr, b, ho, ⟨pc, he⟩, hl, -⟩ := hw
      have hs : (TensorTransfer.slotAt o.spec.descriptor x y k).isSome := by
        unfold TensorStore.writeLoc at hl
        cases h : TensorTransfer.slotAt o.spec.descriptor x y k <;> simp_all
      refine ⟨i, hev he, ?_⟩
      simp only [writeRefs, ho, List.mem_append, List.mem_map]
      exact .inr ⟨(x, y, k), mem_slotTriples hs, rfl⟩
    all_goals exact hw.elim

/-- **Every byte of a new read has a source**: a covering write that no other covering write
follows in byte visibility, or the launch content. -/
theorem newRead_exists (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X) (a : Acc) :
    ∃ bs r, ∀ e : Event, NewRead L mem0 X g e r a bs := by
  classical
  obtain ⟨ws, hws⟩ := writers_finite hX
  let P : Nat → Ref → Prop := fun k w => ∃ a' bs', X.MemWrites w a' bs' ∧ a'.Covers (a.loc.at k)
  let R : Nat → Ref → Ref → Prop := fun k => Relation.TransGen (ByteCausality L X (a.loc.at k))
  have hmax : ∀ k, (∃ w ∈ ws, P k w) → ∃ w ∈ ws, P k w ∧ ∀ y ∈ ws, P k y → ¬ R k w y :=
    fun k h => exists_maximal (R := R k) (fun _ _ _ h1 h2 => h1.trans h2)
      (ByteCausality.acyclic hX.effectValidity hX.object
        (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk (a.loc.at k)) (P k) ws h
  let rr : Nat → Option Ref := fun k =>
    if h : ∃ w ∈ ws, P k w then some (Classical.choose (hmax k h)) else none
  let byte : Nat → Option Byte := fun k =>
    if h : ∃ w ∈ ws, P k w then
      wbyte (Classical.choose (Classical.choose_spec (hmax k h)).2.1)
        (Classical.choose (Classical.choose_spec (Classical.choose_spec (hmax k h)).2.1))
        (a.loc.at k)
    else (mem0 (a.loc.at k)).bind fun c => X.initialByte c (a.loc.at k)
  have hall : ∀ k w a' bs', k < a.size → X.MemWrites w a' bs' → a'.Covers (a.loc.at k) →
      match rr k with
      | none => False
      | some w' => ¬ ByteCausality L X (a.loc.at k) w' w := by
    intro k w a' bs' hk hw hc
    have hP : P k w := ⟨a', bs', hw, hc⟩
    have h : ∃ w ∈ ws, P k w := ⟨w, hws w a' bs' hw, hP⟩
    have hrr : rr k = some (Classical.choose (hmax k h)) := dite_eq_left h
    simp only [hrr]
    intro hv
    have hspec := Classical.choose_spec (hmax k h)
    exact hspec.2.2 w (hws w a' bs' hw) hP (.single hv)
  refine ⟨(List.range a.size).map byte, rr, fun e => ⟨by simp, fun k hk => ?_,
    fun k w a' bs' hk hw hc _ => hall k w a' bs' hk hw hc⟩⟩
  · have hb : ((List.range a.size).map byte)[k]? = some (byte k) := by
      simp [List.getElem?_range hk]
    by_cases h : ∃ w ∈ ws, P k w
    · have hrr : rr k = some (Classical.choose (hmax k h)) := dite_eq_left h
      simp only [hrr]
      have hs := (Classical.choose_spec (hmax k h)).2.1
      have hs' := Classical.choose_spec (Classical.choose_spec hs)
      refine ⟨_, _, hs'.1, hs'.2, ?_⟩
      rw [hb]
      simp only [byte, dite_eq_left h]
    · have hrr : rr k = none := dite_eq_right h
      simp only [hrr]
      intro c hc
      rw [hb]
      simp [byte, dite_eq_right h, hc, Execution.initialByte]

/-- **A released thread performs a read**, each byte taking a source that no other write the
read sees hides: a counted extension. The assumptions' constraints are asked of the extension
only for bytes taken from such sources (`hasm`). -/
theorem read_source_counted_extension (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ []) (hrel : Released L X g) {t t1 : TState} {o : List (Option Byte) → TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    {a : Acc} (hout : out K A L g t1 = .ev (.read a o))
    (hasm : ∀ bs r, (∀ e, NewRead L mem0 X g e r a bs) →
      ∀ a' ∈ A, a'.wf L mem0 (X.snoc g ⟨t1.pc, .rd a bs⟩ r))
    (hsg : SyncGuarded L K X) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  obtain ⟨bs, r, hread⟩ := newRead_exists (g := g) hX hsg a
  exact read_counted_extension hX hg hne hrel hrun hl (o := some (o bs))
    ⟨_, hout, bs, (hread ⟨t1.pc, .rd a bs⟩).len, rfl, rfl⟩ (hread _) (hasm bs r hread)

end
end PTX.Step
