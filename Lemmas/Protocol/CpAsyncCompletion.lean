-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CpAsync
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

namespace PTX

open AsyncCopy

noncomputable section

/-- Complete the read and write stages of an ordinary whole copy. The source byte count can
be smaller than the destination byte count. The copy has no mbarrier notification of its own. -/
def Execution.finishCpAsync (X : Execution) (i : EvId) (read written : List Byte) : Execution :=
  { X with
    rf := fun ref k => if ref = .async i (.read .copy) ∧ k < read.length then none else X.rf ref k
    async := { X.async with copies := fun j =>
      (if j = i then
        { (X.async.copies j) with readBytes := some read, writeBytes := some written }
        else X.async.copies j) } }

variable {X : Execution} {i : EvId} {rs written : List Byte}

theorem Execution.le_finishCpAsync
    (hr : ∀ old, (X.async.copies i).readBytes = some old → old = rs)
    (hw : ∀ old, (X.async.copies i).writeBytes = some old → old = written)
    (hf : ∀ a old, X.MemReads (.async i (.read .copy)) a old →
      ∀ k < rs.length, X.rf (.async i (.read .copy)) k = none) :
    X.le (X.finishCpAsync i rs written) := by
  refine ⟨fun _ => List.prefix_refl _, ?_, ?_, (X.le_refl).2.2.2⟩
  · rintro ref k ⟨a, old, he⟩
    simp only [finishCpAsync]
    split_ifs with hc
    · obtain ⟨rfl, hk⟩ := hc
      exact (hf a old he k hk).symm
    · rfl
  · refine ⟨?_, ?_, ?_, fun _ _ h => h, fun _ h => h, fun _ h => h, ?_, ?_⟩
    · intro j old hj
      by_cases he : j = i
      · subst j
        simp [finishCpAsync, hr old hj]
      · simpa [finishCpAsync, he] using hj
    · intro j old hj
      by_cases he : j = i
      · subst j
        simp [finishCpAsync, hw old hj]
      · simpa [finishCpAsync, he] using hj
    · intro j hj
      by_cases he : j = i <;> simpa [finishCpAsync, he] using hj
    · intro j k old hj
      by_cases he : j = i <;> simpa [finishCpAsync, he] using hj
    · intro j k old hj
      by_cases he : j = i <;> simpa [finishCpAsync, he] using hj

theorem finishCpAsync_initial_extends {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} (hX : Consistent L K A mem0 X) {s : Spec}
    (hi : X.Copy i s) (hw : s.writes = .whole) (hd : s.data = none)
    (ha : ∀ k < s.src.size, mem0 (s.src.loc.at k) ≠ none)
    (hn : ∀ k < s.src.size, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers (s.src.loc.at k)) :
    X.le (X.finishCpAsync i (initialBytes mem0 X s.src)
      (initialBytes mem0 X s.src ++ List.replicate (s.dst.size - s.src.size) zeroByte)) := by
  apply Execution.le_finishCpAsync
  · intro old hr
    have hmem : X.MemReads (.async i (.read .copy)) s.src (old.map some) :=
      ⟨s, old, hi, rfl, hr, rfl⟩
    exact read_bytes_of_no_writer hX hmem ha hn
  · intro old hr
    exact whole_copy_write_initial hX hi hw hd hr ha hn
  · intro src old hr k hk
    have hmem := hr
    obtain ⟨s', _, hi', he, _, _⟩ := hr
    have hs : s' = s := hi'.unique hi
    subst s'
    subst src
    have hk' : k < s.src.size := by simpa [initialBytes] using hk
    exact read_rf_of_no_writer hX hmem hk' (hn k hk')

theorem finishCpAsync_wellFormed {s : Spec} (h : WellFormed (issuedBy X) X.async)
    (hi : issuedBy X i = some s) (hw : s.writes = .whole) (hd : s.data = none)
    (hc : s.completion = .asyncGroup) (hsize : s.src.size ≤ s.dst.size)
    (hrs : rs.length = s.src.size)
    (hbs : written = rs ++ List.replicate (s.dst.size - s.src.size) zeroByte) :
    WellFormed (issuedBy (X.finishCpAsync i rs written)) (X.finishCpAsync i rs written).async := by
  intro j hj
  by_cases he : j = i
  · subst j
    have hold : nonempty (X.async.copies i) → CopyOk s (X.async.copies i) := by
      intro hnon
      obtain ⟨s', hs, hok⟩ := h i hnon
      rw [hi] at hs
      cases hs
      exact hok
    refine ⟨s, hi, hsize, ?_, ?_, ?_, ?_⟩
    · simp [Execution.finishCpAsync, hd, hrs]
    · simp [Execution.finishCpAsync, hw, sourceBytes, hd, hbs]
    · intro hn
      have hn' : (X.async.copies i).notified = true := by simpa [Execution.finishCpAsync] using hn
      have hok := hold ⟨.notify .copy, by simp [present, hn']⟩
      simpa [hc] using (hok.2.2.2.1 hn').1
    · constructor
      · intro j bs hb
        have hb' : (X.async.copies i).elemWrites j = some bs := by
          simpa [Execution.finishCpAsync] using hb
        have hne := hold ⟨.write (.elem j), by simp [present, hb']⟩
        have ht := (hne.2.2.2.2.1 j bs hb').1
        simp [Spec.elems, Spec.elemOffsets, hw] at ht
      · intro j bs hb
        have hb' : (X.async.copies i).elemOld j = some bs := by
          simpa [Execution.finishCpAsync] using hb
        have hne := hold ⟨.old (.elem j), by simp [present, hb']⟩
        have ht := (hne.2.2.2.2.2 j bs hb').1
        simp [hw] at ht
  · have hsame : (X.finishCpAsync i rs written).async.copies j = X.async.copies j := by
      simp [Execution.finishCpAsync, he]
    rw [hsame] at hj ⊢
    exact h j hj

/-- An already performed arrive-on cannot track a copy whose write is still pending. -/
theorem no_arriveOn_tracks_pending_copy (h : ArriveOk X)
    (hn : (X.async.copies i).writeBytes = none) {j : EvId} (hj : TracksCpAsync X i j) :
    X.async.arrived j = false := by
  cases ha : X.async.arrived j
  · rfl
  · have hwrite := (h j ha).2 i hj
    simp [hn] at hwrite


theorem finishCpAsync_tmaOk {s : Spec} (h : TmaOk X) (hle : X.le (X.finishCpAsync i rs written))
    (hi : issuedBy X i = some s) (hw : s.writes = .whole) (hd : s.data = none)
    (hc : s.completion = .asyncGroup) (hsize : s.src.size ≤ s.dst.size)
    (hrs : rs.length = s.src.size)
    (hbs : written = rs ++ List.replicate (s.dst.size - s.src.size) zeroByte) :
    TmaOk (X.finishCpAsync i rs written) := by
  refine ⟨finishCpAsync_wellFormed h.1 hi hw hd hc hsize hrs hbs, h.2.1, ?_, ?_⟩
  · have hact : ∀ l ref,
        objectAction (X.finishCpAsync i rs written) (X.finishCpAsync i rs written).async l ref =
          objectAction X X.async l ref := by
      intro l ref
      cases ref with
      | thread j => rfl
      | async j p =>
        cases p <;> try rfl
        case notifyCopy =>
          by_cases hj : j = i <;> simp only [objectAction, Execution.finishCpAsync, hj,
            ↓reduceIte] <;> rfl
    intro l
    have hobjects : (X.finishCpAsync i rs written).objects l = X.objects l := rfl
    simpa only [MatchesObject, CoversObject, hact, hobjects] using h.2.2.1 l
  · intro j hj
    obtain ⟨harr, htrack⟩ := h.2.2.2 j hj
    refine ⟨harr, fun copy ht => ?_⟩
    obtain ⟨bs, hbytes⟩ := Option.isSome_iff_exists.mp (htrack copy ht)
    exact Option.isSome_iff_exists.mpr ⟨bs, hle.2.2.1.2.1 copy bs hbytes⟩

theorem finishCpAsync_size {L : Launch} (hle : X.le (X.finishCpAsync i rs written))
    (hg : i.1 < L.threads) (hidx : i.2 < (X.tr i.1).length)
    (hn : (X.async.copies i).writeBytes = none) :
    X.size L < (X.finishCpAsync i rs written).size L := by
  apply Execution.size_lt_of_asyncSize_lt hle rfl hg hidx
  have h : (X.finishCpAsync i rs written).elemSize i = X.elemSize i := by
    have he : ∀ k, ((X.finishCpAsync i rs written).async.copies i).elemWrites k =
        (X.async.copies i).elemWrites k ∧
        ((X.finishCpAsync i rs written).async.copies i).elemOld k =
        (X.async.copies i).elemOld k := by
      intro k
      simp [Execution.finishCpAsync]
    have hget : (X.finishCpAsync i rs written).get i = X.get i := rfl
    unfold Execution.elemSize
    rw [hget]
    split <;> simp [he]
  unfold Execution.asyncSize
  rw [h]
  cases (X.async.copies i).readBytes <;> cases hm : X.async.mmaOperands i <;>
    cases hb : (X.async.copies i).notified <;>
    simp [Execution.finishCpAsync, Snapshot.mmaStarted, hn, hm, hb]

end

end PTX
