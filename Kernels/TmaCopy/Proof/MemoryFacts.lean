-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Values

@[expose] public section

/-! # `tma_copy`: the memory accesses

The accesses of an execution are thread 0's read of `buf` and write of `B`, and the bulk copy's
read of `A` and write of `buf` (`intent_cases`). Two of them that overlap are ordered: thread 0's
accesses by program order, the copy's write before the read of `buf` through the observing poll
(`ordinary_after_copy`), and no other pair overlaps (`conflicts_ordered`). Every accessed byte is
allocated (`no_unalloc`), no access touches the mbarrier (`intent_mbar_disjoint`), and every
shared access and mbarrier operation is in its issuer's CTA (`intent_local`, `object_local`). -/

namespace PTX.Kernels.TmaCopy.Proof
open PTX PTX.Proof AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0} {X : Execution}
variable (hpre : Pre L A B x mem0) (ht : ThreadFacts L A B X) (hX : Consistent L kernel [] mem0 X)
include hpre ht hX



omit hpre in
theorem ordinary_access_thread {i : EvId} {a : Acc} {w : Bool} (hi : X.Access i a w) :
    i.1 = 0 ∧ ∃ ev, X.get i = some ev := by
  rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩
  · exact ⟨(reads_cases ht hX hr).1, _, hr.choose_spec⟩
  · exact ⟨(writes_cases ht hX hw).1, _, hw.choose_spec⟩

omit hpre in
theorem intent_cases {e : Ref} {a : Acc} {w : Bool} (he : X.Intent e a w) :
    (∃ i, e = .thread i ∧ X.Access i a w) ∨
    (e = .async (0, 3) (.read .copy) ∧ w = false ∧ a = { loc := gA A, size := 16 }) ∨
    (e = .async (0, 3) (.write .copy) ∧ w = true ∧
      a = { loc := buf L.sharedBase, size := 16 }) := by
  cases e with
  | thread i => exact .inl ⟨i, rfl, he⟩
  | async i p =>
    cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
      and_false] at he
    case readCopy =>
      obtain ⟨rfl, ⟨s, hb, rfl⟩ | hp⟩ := he
      · obtain ⟨rfl, rfl⟩ := bulk_cases ht hX hb
        exact .inr (.inl ⟨rfl, rfl, rfl⟩)
      · exact (no_bulkPrefetch ht hX hp).elim
    case writeCopy =>
      obtain ⟨rfl, s, hb, -, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := bulk_cases ht hX hb
      exact .inr (.inr ⟨rfl, rfl, rfl⟩)
    case writeElem j =>
      obtain ⟨-, s, hb, hj⟩ := he
      obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
      simp [copySpec, bulkSpec, Spec.elems, Spec.elemOffsets] at hj
    case oldElem j =>
      obtain ⟨-, s, r, hb, hw, -⟩ := he
      obtain ⟨-, rfl⟩ := bulk_cases ht hX hb
      simp [copySpec, bulkSpec] at hw
    case readLoad x y k | writeLoad x y k | readStore x y k | writeStore x y k | oldStore x y k
        | readPrefetch x y k =>
      obtain ⟨_,spec,addr,⟨pc,hp⟩,_⟩ := he
      exact (not_class ht hX hp rfl).elim
    case writeCta c =>
      obtain ⟨_,spec,targets,⟨pc,hp⟩,_⟩ := he
      exact (not_class ht hX hp rfl).elim
    case mmaRead isB k =>
      rcases he with ⟨_,_,⟨d,s,accum,mask,⟨pc,hp⟩,_⟩ | ⟨a,src,cta,⟨pc,hp⟩,_⟩⟩
      · exact (noTc ht hX _ _ _ hp).elim
      · exact (noTc ht hX _ _ _ hp).elim

theorem ordinary_input_disjoint {i : EvId} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access i a w) (hc : a.Covers l) : ¬ ({ loc := gA A, size := 16 } : Acc).Covers l := by
  intro ha
  rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩
  · have hloc := (reads_cases ht hX hr).2.1
    rw [hloc] at hc
    simp only [Acc.Covers, Loc.InRange, buf, gA] at hc ha
    exact (by simpa [ha.1] using hc.1 : False)
  · have hloc := (writes_cases ht hX hw).2.1
    rw [hloc] at hc
    have hd := hpre.disjoint
    simp only [Acc.Covers, Loc.InRange, gB, gA] at hc ha
    omega

omit hpre in
theorem ordinary_after_copy {i : EvId} {a : Acc} {w : Bool} {l : Loc}
    (hi : X.Access i a w) (hc : a.Covers l)
    (hs : ({ loc := buf L.sharedBase, size := 16 } : Acc).Covers l)
    (hw : X.Intent (.async (0, 3) (.write .copy)) { loc := buf L.sharedBase, size := 16 } true) :
    modelCausality L X l (.async (0, 3) (.write .copy)) (.thread i) := by
  rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hwr, _⟩
  · obtain ⟨waiter, ws, ho, hsc, hb⟩ := read_copy_visible ht hX hr
    obtain ⟨n, m, hn, hwo⟩ := ho
    exact ⟨⟨_, true, hw, hs⟩, waiter, .inr ⟨ws, ⟨n, m, .inl hn, hwo⟩, hsc⟩, .inl hb⟩
  · have hloc := (writes_cases ht hX hwr).2.1
    rw [hloc] at hc
    simp only [Acc.Covers, Loc.InRange, gB, buf] at hc hs
    exact (by simpa [hs.1] using hc.1 : False).elim

/-- Every overlapping pair of different access intents has the required byte order.
This includes the copy's write before it has happened. -/
theorem intents_ordered {e f : Ref} {a b : Acc} {we wf : Bool} {l : Loc}
    (he : X.Intent e a we) (hf : X.Intent f b wf) (hne : e ≠ f)
    (ha : a.Covers l) (hb : b.Covers l) : modelCausality L X l e f ∨ modelCausality L X l f e := by
  rcases intent_cases ht hX he with ⟨i, rfl, hi⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · rcases intent_cases ht hX hf with ⟨j, rfl, hj⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨hi0, ei, hei⟩ := ordinary_access_thread ht hX hi
      obtain ⟨hj0, ej, hej⟩ := ordinary_access_thread ht hX hj
      have hij : i.2 ≠ j.2 := by
        intro heq; exact hne (congrArg Ref.thread (Prod.ext (hi0.trans hj0.symm) heq))
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact .inl (.inl (.single (.inl
          (po_of_overlap hi hj (hi0.trans hj0.symm) hlt ⟨l, ha, hb⟩))))
      · exact .inr (.inl (.single (.inl
          (po_of_overlap hj hi (hj0.trans hi0.symm) hgt ⟨l, hb, ha⟩))))
    · exact (ordinary_input_disjoint hpre ht hX hi ha hb).elim
    · exact .inr (ordinary_after_copy ht hX hi ha hb hf)
  · rcases intent_cases ht hX hf with ⟨j, rfl, hj⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, rfl⟩
    · exact (ordinary_input_disjoint hpre ht hX hj hb ha).elim
    · exact (hne rfl).elim
    · simp only [Acc.Covers, Loc.InRange, gA, buf] at ha hb
      exact (by simpa [ha.1] using hb.1 : False).elim
  · rcases intent_cases ht hX hf with ⟨j, rfl, hj⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, _⟩
    · exact .inl (ordinary_after_copy ht hX hj hb ha he)
    · simp only [Acc.Covers, Loc.InRange, gA, buf] at ha hb
      exact (by simpa [hb.1] using ha.1 : False).elim
    · exact (hne rfl).elim

/-- **Conflicting accesses are ordered** at every byte. -/
theorem conflicts_ordered : ConflictsOrdered L X fun _ => True :=
  fun _ _ _ _ _ ⟨hne, _, _, he, hf, _⟩ ha hb _ => intents_ordered hpre ht hX he hf hne ha hb

omit ht hX in
theorem input_alloc {l : Loc} (hc : ({ loc := gA A, size := 16 } : Acc).Covers l) :
    mem0 l ≠ none := by
  obtain ⟨sp, cta, addr⟩ := l
  simp only [Acc.Covers, Loc.InRange, gA] at hc
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hh := hpre.inputAlloc (addr - A) (by omega)
  simpa [Nat.add_sub_of_le hlo] using hh

omit ht hX in
theorem output_alloc {l : Loc} (hc : ({ loc := gB B, size := 4 } : Acc).Covers l) :
    mem0 l ≠ none := by
  obtain ⟨sp, cta, addr⟩ := l
  simp only [Acc.Covers, Loc.InRange, gB] at hc
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hh := hpre.output (addr - B) (by omega)
  simpa [Nat.add_sub_of_le hlo] using hh

omit ht hX in
theorem shared_alloc {n : Nat} {l : Loc} (hn : n ≤ 24)
    (hc : ({ loc := buf L.sharedBase, size := n } : Acc).Covers l) : mem0 l ≠ none := by
  obtain ⟨sp, cta, addr⟩ := l
  simp only [Acc.Covers, Loc.InRange, buf] at hc
  obtain ⟨rfl, rfl, hlo, hhi⟩ := hc
  have hh := hpre.shared (addr - L.sharedBase) (by omega)
  simpa [Nat.add_sub_of_le hlo] using hh

theorem intent_alloc {e : Ref} {a : Acc} {w : Bool} {l : Loc}
    (he : X.Intent e a w) (hc : a.Covers l) : mem0 l ≠ none := by
  rcases intent_cases ht hX he with ⟨i, _, hi⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩
    · rw [(reads_cases ht hX hr).2.1] at hc
      exact shared_alloc hpre (by decide) hc
    · rw [(writes_cases ht hX hw).2.1] at hc
      exact output_alloc hpre hc
  · exact input_alloc hpre hc
  · exact shared_alloc hpre (by decide) hc

omit ht hX in
/-- The mbarrier's storage is allocated. -/
theorem mbar_alloc {l : Loc} (hc : ({ loc := mbar L.sharedBase, size := 8 } : Acc).Covers l) :
    mem0 l ≠ none := by
  have hs : ({ loc := buf L.sharedBase, size := 24 } : Acc).Covers l := by
    simp only [Acc.Covers, Loc.InRange, mbar, buf] at hc ⊢
    exact ⟨hc.1, hc.2.1, by omega, by omega⟩
  exact shared_alloc hpre (by decide) hs

theorem no_unalloc : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, ht', hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  · rcases ht' with ⟨w, he⟩ | ⟨i, bs, _, hnc⟩
    · exact intent_alloc hpre ht hX he hc hn
    · exact no_nc ht hX hnc
  · rw [uses_cases ht hX hu] at hc
    exact mbar_alloc hpre hc hn

omit hpre in
/-- No data access overlaps the mbarrier object's storage. -/
theorem intent_mbar_disjoint {e : Ref} {a : Acc} {w : Bool} {l : Loc}
    (he : X.Intent e a w) (hc : a.Covers l) :
    ¬ ({ loc := mbar L.sharedBase, size := 8 } : Acc).Covers l := by
  intro hm
  rcases intent_cases ht hX he with ⟨i, _, hi⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
  · rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩
    · rw [(reads_cases ht hX hr).2.1] at hc
      simp only [Acc.Covers, Loc.InRange, buf, mbar] at hc hm
      omega
    · rw [(writes_cases ht hX hw).2.1] at hc
      simp only [Acc.Covers, Loc.InRange, gB, mbar] at hc hm
      exact (by simpa [hm.1] using hc.1 : False)
  · simp only [Acc.Covers, Loc.InRange, gA, mbar] at hc hm
    exact (by simpa [hm.1] using hc.1 : False)
  · simp only [Acc.Covers, Loc.InRange, buf, mbar] at hc hm
    omega


omit hpre in
/-- Every shared access is in its issuer's CTA. -/
theorem intent_local {e : Ref} {a : Acc} {w : Bool} (he : X.Intent e a w)
    (hs : a.loc.space = .shared) : a.loc.cta = e.issuer.1 / L.block := by
  rcases intent_cases ht hX he with ⟨i, rfl, hi⟩ | ⟨rfl, _, rfl⟩ | ⟨rfl, _, rfl⟩
  · obtain ⟨hi0, -⟩ := ordinary_access_thread ht hX hi
    rcases access_cases ht hX hi with ⟨bs, hr, _⟩ | ⟨bs, hw, _⟩
    · rw [(reads_cases ht hX hr).2.1]
      simp [buf, Ref.issuer, hi0]
    · rw [(writes_cases ht hX hw).2.1] at hs
      cases hs
  · cases hs
  · simp [buf, Ref.issuer]

omit hpre in
/-- Every mbarrier operation is on the object of its issuer's CTA. -/
theorem object_local {m : Loc} {e : Ref} {act : Action}
    (ha : objectAction X X.async m e = some act) : m.cta = e.issuer.1 / L.block := by
  obtain ⟨rfl, h⟩ := object_action_cases ht hX ha
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨j, ok, -, rfl, -⟩ <;> simp [mbar, Ref.issuer]

end

end PTX.Kernels.TmaCopy.Proof
