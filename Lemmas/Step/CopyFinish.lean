-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncExecution
public import Lemmas.Snoc.Snoc
public import Lemmas.Async.ReadSources

@[expose] public section

/-! Construct an extension that completes one copy. The copy reads its source memory and writes
its destination as one whole (`Spec.data = none`, `Spec.writes = .whole`), and its completion is
the notification of an mbarrier (`Spec.completion = .mbarrier m`). These helpers do not assert
execution consistency: callers must establish source values, object transitions and
ordering. No kernel, address, phase or number of writers is fixed here. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- Record the read, the write and the completion notification of copy `i` with bytes `bs`, and
the read sources `src`; the element stages of the copy are kept. -/
def Execution.finishCopy (X : Execution) (i : EvId) (bs : List Byte)
    (src : Nat → Option Ref) : Execution :=
  { X with
    rf := fun e k => if e = .async i (.read .copy) ∧ k < bs.length then src k else X.rf e k
    async := { X.async with copies := fun j => (if j = i then
      { (X.async.copies j) with readBytes := some bs, writeBytes := some bs, notified := true }
      else X.async.copies j) } }

/-- Completing a copy keeps its element stages, so its counted element stages are unchanged. -/
theorem Execution.finishCopy_elemSize (X : Execution) (i : EvId) (bs : List Byte)
    (src : Nat → Option Ref) (j : EvId) : (X.finishCopy i bs src).elemSize j = X.elemSize j := by
  have hc : ∀ k, ((X.finishCopy i bs src).async.copies j).elemWrites k =
      (X.async.copies j).elemWrites k ∧ ((X.finishCopy i bs src).async.copies j).elemOld k =
      (X.async.copies j).elemOld k := by
    intro k
    by_cases h : j = i <;> simp [finishCopy, h]
  have hg : (X.finishCopy i bs src).get j = X.get j := rfl
  unfold Execution.elemSize
  rw [hg]
  split <;> simp [hc]

theorem Execution.le_finishCopy {X : Execution} {i : EvId} {bs : List Byte}
    {src : Nat → Option Ref}
    (hr : ∀ old, (X.async.copies i).readBytes = some old → old = bs)
    (hw : ∀ old, (X.async.copies i).writeBytes = some old → old = bs)
    (hf : ∀ a old, X.MemReads (.async i (.read .copy)) a old →
      ∀ k < bs.length, src k = X.rf (.async i (.read .copy)) k) :
    X.le (X.finishCopy i bs src) := by
  refine ⟨fun _ => List.prefix_refl _, ?_, ?_, (Execution.le_refl X).2.2.2⟩
  · rintro e k ⟨a, old, he⟩
    simp only [finishCopy]
    split_ifs with hc
    · obtain ⟨rfl, hk⟩ := hc
      exact hf a old he k hk
    · rfl
  · refine ⟨?_, ?_, ?_, fun _ _ h => h, fun _ h => h, fun _ h => h, ?_, ?_⟩
    · intro j old hj
      by_cases hi : j = i
      · subst j; simp [finishCopy, hr old hj]
      · simpa [finishCopy, hi] using hj
    · intro j old hj
      by_cases hi : j = i
      · subst j; simp [finishCopy, hw old hj]
      · simpa [finishCopy, hi] using hj
    · intro j hj
      by_cases hi : j = i
      · simp [finishCopy, hi]
      · simpa [finishCopy, hi] using hj
    · intro j k old hj
      by_cases hi : j = i
      · subst j; simpa [finishCopy] using hj
      · simpa [finishCopy, hi] using hj
    · intro j k old hj
      by_cases hi : j = i
      · subst j; simpa [finishCopy] using hj
      · simpa [finishCopy, hi] using hj

/-- A copy that writes its destination as one whole has recorded no element stage. -/
theorem elems_none_of_whole {X : Execution} {i : EvId} {spec : Spec}
    (ht : WellFormed (issuedBy X) X.async) (hi : issuedBy X i = some spec)
    (hw : spec.writes = .whole) (j : Nat) :
    (X.async.copies i).elemWrites j = none ∧ (X.async.copies i).elemOld j = none := by
  have hok : nonempty (X.async.copies i) → CopyOk spec (X.async.copies i) := by
    intro hn
    obtain ⟨s, hs, hc⟩ := ht i hn
    rw [hi] at hs
    cases hs
    exact hc
  constructor
  · cases hj : (X.async.copies i).elemWrites j with
    | none => rfl
    | some bs =>
      have hc := hok ⟨.write (.elem j), by simp [present, hj]⟩
      have := (hc.2.2.2.2.1 j bs hj).1
      simp [Spec.elems, Spec.elemOffsets, hw] at this
  · cases hj : (X.async.copies i).elemOld j with
    | none => rfl
    | some bs =>
      have hc := hok ⟨.old (.elem j), by simp [present, hj]⟩
      obtain ⟨r, hr⟩ := (hc.2.2.2.2.2 j bs hj).1
      rw [hw] at hr
      cases hr

theorem finishCopy_wellFormed {X : Execution} {i : EvId} {bs : List Byte}
    {src : Nat → Option Ref} {spec : Spec}
    {m : Loc} (ht : WellFormed (issuedBy X) X.async) (hi : issuedBy X i = some spec)
    (hw : spec.writes = .whole) (hd : spec.data = none) (hm : spec.completion = .mbarrier m)
    (hsize : spec.src.size = spec.dst.size) (hbytes : bs.length = spec.src.size) :
    WellFormed (issuedBy (X.finishCopy i bs src)) (X.finishCopy i bs src).async := by
  intro j hj
  by_cases he : j = i
  · subst j
    refine ⟨spec, hi, ?_⟩
    have hn := elems_none_of_whole ht hi hw
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simp [Execution.finishCopy, hd, hbytes]
    · simp [Execution.finishCopy, hw, sourceBytes, hd, hsize]
    · simp [Execution.finishCopy, hm]
    · constructor
      · intro k b hk
        simp [Execution.finishCopy, (hn k).1] at hk
      · intro k b hk
        simp [Execution.finishCopy, (hn k).2] at hk
  · have hs : ((X.finishCopy i bs src).async.copies j) = X.async.copies j := by
      simp [Execution.finishCopy, he]
    rw [hs] at hj
    obtain ⟨s, hs', hc⟩ := ht j hj
    exact ⟨s, hs', by rw [hs]; exact hc⟩

/-- Completing a copy from an allocated footprint with no program writer preserves
any source or destination bytes already recorded for that copy. -/
theorem finishCopy_initial_extends {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {i : EvId} {s : Spec} (hb : X.Copy i s) (hw : s.writes = .whole) (hd : s.data = none)
    (hsize : s.src.size = s.dst.size)
    (ha : ∀ k < s.src.size, mem0 (s.src.loc.at k) ≠ none)
    (hn : ∀ k < s.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (s.src.loc.at k)) :
    X.le (X.finishCopy i (initialBytes mem0 X s.src) (fun _ => none)) := by
  have hread : ∀ old, (X.async.copies i).readBytes = some old →
      old = initialBytes mem0 X s.src := fun old hr =>
    read_bytes_of_no_writer hX (e := .async i (.read .copy)) ⟨s, old, hb, rfl, hr, rfl⟩ ha hn
  apply Execution.le_finishCopy
  · exact hread
  · intro old hwb
    obtain ⟨spec, hi, hc⟩ := hX.tma.1 i ⟨.write .copy, by simp [present, hwb]⟩
    have hs : spec = s := (issuedBy_some.mp hi).unique hb
    subst spec
    have hsrc := hc.2.2.1 old hwb
    simp only [hw, sourceBytes, hd, hsize, Nat.sub_self, List.replicate_zero, List.append_nil,
      Option.map_id'] at hsrc
    exact hread old hsrc
  · intro acc old hr k hk
    have hk' : k < s.src.size := by simpa [initialBytes] using hk
    have hacc : acc = s.src := by
      obtain ⟨s', raw, hb', hs', _, _⟩ := hr
      rw [← hs', hb'.unique hb]
    subst acc
    exact (read_rf_of_no_writer hX hr hk' (hn k hk')).symm

private theorem sum_map_mono {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ i ∈ xs, f i ≤ g i) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj => h j (by simp [hj]))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- A new notification strictly increases the counted execution size, including when
its read and write stages were already present. -/
theorem finishCopy_size {L : Launch} {X : Execution} {i : EvId} {bs : List Byte}
    {src : Nat → Option Ref} (hg : i.1 < L.threads) (hi : i.2 < (X.tr i.1).length)
    (hn : (X.async.copies i).notified = false) :
    X.size L < (X.finishCopy i bs src).size L := by
  have hs : ∀ j, (if j = i then X.asyncSize j + 1 else X.asyncSize j) ≤
      (X.finishCopy i bs src).asyncSize j := by
    intro j
    have hc : (X.finishCopy i bs src).async.copies j =
        (if j = i then
          { (X.async.copies j) with readBytes := some bs, writeBytes := some bs, notified := true }
          else X.async.copies j) := rfl
    unfold Execution.asyncSize
    rw [hc, show (X.finishCopy i bs src).async.mmaStarted = X.async.mmaStarted from rfl,
      show (X.finishCopy i bs src).async.mmaDone = X.async.mmaDone from rfl,
      show (X.finishCopy i bs src).async.arrived = X.async.arrived from rfl,
      show (X.finishCopy i bs src).clc = X.clc from rfl,
      show (X.finishCopy i bs src).tensor = X.tensor from rfl,
      show (X.finishCopy i bs src).tensorStores = X.tensorStores from rfl,
      show (X.finishCopy i bs src).tcNotified = X.tcNotified from rfl,
      Execution.finishCopy_elemSize]
    by_cases he : j = i
    · subst j
      simp only [↓reduceIte, Option.isSome_some, hn, Bool.false_eq_true]
      split_ifs <;> omega
    · simp only [he, ↓reduceIte, le_refl]
  let f := fun g => (X.tr g).countP Event.counts +
    ((List.range (X.tr g).length).map fun k => X.asyncSize (g, k)).sum
  have hb : ∀ g, (if g = i.1 then f g + 1 else f g) ≤
      ((X.finishCopy i bs src).tr g).countP Event.counts +
      ((List.range ((X.finishCopy i bs src).tr g).length).map
        fun k => (X.finishCopy i bs src).asyncSize (g, k)).sum := by
    intro g
    have hm := sum_map_mono (List.range (X.tr g).length)
      (fun k => if (g, k) = i then X.asyncSize (g, k) + 1 else X.asyncSize (g, k))
      (fun k => (X.finishCopy i bs src).asyncSize (g, k)) (fun k _ => hs (g, k))
    by_cases he : g = i.1
    · subst g
      have heq : ∀ k, (i.1, k) = i ↔ k = i.2 := by intro k; exact Prod.ext_iff.trans (by simp)
      simp only [heq] at hm
      rw [sum_range_bump, ite_eq_left hi] at hm
      simpa [f, Execution.finishCopy, Nat.add_assoc] using
        Nat.add_le_add_left hm ((X.tr i.1).countP Event.counts)
    · have heq : ∀ k, (g, k) ≠ i := fun k h => he (congrArg Prod.fst h)
      simpa [f, Execution.finishCopy, he, heq] using
        Nat.add_le_add_left hm ((X.tr g).countP Event.counts)
  have hm := sum_map_mono (List.range L.threads)
    (fun g => if g = i.1 then f g + 1 else f g) _ (fun g _ => hb g)
  rw [sum_range_bump, ite_eq_left hg] at hm
  change X.threadSize L + 1 ≤ (X.finishCopy i bs src).threadSize L at hm
  have hp : (X.finishCopy i bs src).pairSize L = X.pairSize L := rfl
  unfold Execution.size
  rw [hp]
  omega

end
end PTX
