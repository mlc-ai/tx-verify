-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Memory.Order
public import Core.Async.CpAsync
public import Lemmas.Async.AsyncMBarrier
public import Lemmas.Async.ReadSources
public import Lemmas.Execution.ExecutionCountedPrefixSize
public import Lemmas.Snoc.Snoc

@[expose] public section

namespace PTX

noncomputable section

/-- The explicit source-size operand is checked as an unsigned 32-bit value. -/
theorem cpAsyncSourceSize_size {L : Launch} {g capacity : Nat} {t : TState} {n : Opnd}
    {v : BitVec 64} (hv : readBits L g t 32 n = .ok v) (hn : v.toNat ≤ capacity) :
    cpAsyncSourceSize L g t capacity (.size n) = .ok v.toNat := by
  simp [cpAsyncSourceSize, hv, hn, bind, Except.bind, pure, Except.pure]

/-- A valid ordinary asynchronous copy issues exactly one whole-copy event. -/
theorem cpAsyncTmpl_copy {L : Launch} {g size n : Nat} {t : TState} {db sb : Nat}
    {doff soff : Int} {source : CpAsyncSource} {policy : Option Opnd} {d s : Loc}
    (hd : effAddr L g t .shared db doff = .ok d)
    (hs : effAddr L g t .global sb soff = .ok s)
    (ha : 0 < size ∧ d.addr % size = 0 ∧ s.addr % size = 0)
    (hn : cpAsyncSourceSize L g t size source = .ok n)
    (hp : bulkPolicy L g t policy = .ok ()) :
    cpAsyncTmpl L g t (.cpAsync db doff sb soff size source policy) =
      .copy ⟨{ loc := s, size := n }, { loc := d, size := size },
        .asyncGroup, .whole, none, true, none⟩ (next t) := by
  simp [cpAsyncTmpl, hd, hs, ha, hn, hp, ofExec, bind, Except.bind, pure, Except.pure]

/-- The state-space form of `cp.async.mbarrier.arrive.noinc` issues an asynchronous arrival. -/
theorem cpAsyncTmpl_arrive_noinc {L : Launch} {g : Nat} {t : TState} {b : Nat} {off : Int}
    {m : Loc} (hm : mbarLoc L g t b off = .ok m) :
    cpAsyncTmpl L g t (.cpAsyncArrive true b off false) = .asyncArrive m true (next t) := by
  simp [cpAsyncTmpl, hm, ofExec, bind, Except.bind, pure, Except.pure]

namespace AsyncCopy

/-- A completed whole copy without a register source writes exactly its source bytes with the
specified zero padding. -/
theorem CopyOk.whole_write {s : Spec} {e : Effects} {bs : List Byte}
    (h : CopyOk s e) (hw : s.writes = .whole) (hd : s.data = none)
    (hb : e.writeBytes = some bs) :
    ∃ rs, e.readBytes = some rs ∧ rs.length = s.src.size ∧
      bs = rs ++ List.replicate (s.dst.size - s.src.size) zeroByte := by
  have hsource := h.2.2.1 bs hb
  simp only [hw, sourceBytes, hd, Option.map_eq_some_iff] at hsource
  obtain ⟨rs, hrs, rfl⟩ := hsource
  exact ⟨rs, hrs, (h.2.1 rs hrs).2, rfl⟩

/-- Source-size zero fills the entire destination, with an empty recorded source read. -/
theorem CopyOk.whole_write_zero {s : Spec} {e : Effects} {bs : List Byte}
    (h : CopyOk s e) (hw : s.writes = .whole) (hd : s.data = none)
    (hz : s.src.size = 0) (hb : e.writeBytes = some bs) :
    e.readBytes = some [] ∧ bs = List.replicate s.dst.size zeroByte := by
  obtain ⟨rs, hr, hlen, rfl⟩ := h.whole_write hw hd hb
  rw [hz, List.length_eq_zero_iff] at hlen
  subst rs
  simp [hr, hz]

/-- A whole asynchronous copy from an allocated read-only source writes its launch bytes,
followed by any zero padding mandated by its source-size operand. -/
theorem whole_copy_write_initial {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) {i : EvId} {s : Spec} {bs : List Byte}
    (hi : X.Copy i s) (hw : s.writes = .whole) (hd : s.data = none)
    (hb : (X.async.copies i).writeBytes = some bs)
    (ha : ∀ k < s.src.size, mem0 (s.src.loc.at k) ≠ none)
    (hn : ∀ k < s.src.size, ∀ w dst bytes, X.MemWrites w dst bytes →
      ¬ dst.Covers (s.src.loc.at k)) :
    bs = initialBytes mem0 X s.src ++ List.replicate (s.dst.size - s.src.size) zeroByte := by
  obtain ⟨s', hi', hcopy⟩ := hX.tma.1 i ⟨.write .copy, by simp [present, hb]⟩
  have hs := (issuedBy_some.mp hi').unique hi
  subst s'
  obtain ⟨rs, hrs, _, rfl⟩ := hcopy.whole_write hw hd hb
  have hr : X.MemReads (.async i (.read .copy)) s.src (rs.map some) :=
    ⟨s, rs, hi, rfl, hrs, rfl⟩
  rw [read_bytes_of_no_writer hX hr ha hn]

/-- Distinct aligned starts of fixed-width copies determine disjoint destinations. -/
theorem not_overlap_of_aligned_starts {a b : Acc} {width : Nat}
    (ha : a.loc.addr % width = 0) (hb : b.loc.addr % width = 0)
    (hsa : a.size ≤ width) (hsb : b.size ≤ width) (hne : a.loc.addr ≠ b.loc.addr) :
    ¬ a.Overlap b := by
  rintro ⟨l, hla, hlb⟩
  have hwidth : 0 < width := by
    by_contra! h
    have hz : width = 0 := by omega
    simp [hz] at ha hb
    exact hne (ha.trans hb.symm)
  obtain ⟨_, _, h1, h2⟩ := hla
  obtain ⟨_, _, h3, h4⟩ := hlb
  have hada : a.loc.addr = width * (a.loc.addr / width) := by
    have h := Nat.mod_add_div a.loc.addr width
    omega
  have hadb : b.loc.addr = width * (b.loc.addr / width) := by
    have h := Nat.mod_add_div b.loc.addr width
    omega
  have hh : a.loc.addr / width ≠ b.loc.addr / width := by
    intro heq
    exact hne (hada.trans ((congrArg (width * ·) heq).trans hadb.symm))
  rcases Nat.lt_or_gt_of_ne hh with h | h
  · have ht := Nat.mul_le_mul_left width (Nat.succ_le_of_lt h)
    simp only [Nat.mul_succ] at ht
    omega
  · have ht := Nat.mul_le_mul_left width (Nat.succ_le_of_lt h)
    simp only [Nat.mul_succ] at ht
    omega

/-- Destination separation between distinct issues discharges Core's overlap check. -/
theorem not_cpAsyncOverlap_of_apart {X : Execution}
    (h : ∀ i j s s', SameAsyncGroup X i j → X.Copy i s → X.Copy j s' →
      ¬ s.dst.Overlap s'.dst) :
    ¬ CpAsyncOverlap X := fun ⟨i, j, s, s', hg, hi, hj, hover⟩ => h i j s s' hg hi hj hover

/-- Ordinary copy issues in an execution without ordinary group waits are observed through
arrive-on only. Bulk group waits cover a different completion mode. -/
theorem not_groupWaitsFor_of_no_cpAsyncWait {X : Execution} {i : EvId} {s : Spec}
    (hi : X.Copy i s) (hc : s.completion = .asyncGroup)
    (hno : ∀ w pc remaining, X.get w ≠ some ⟨pc, .asyncWait remaining⟩) (k : GroupWait) (w : EvId) :
    ¬ GroupWaitsFor X k i w := by
  cases k with
  | bulk mode => exact not_bulkWaitsFor_of_copy hi (by simp [hc])
  | cpAsync =>
    rintro ⟨pc, rem, hget, _⟩
    exact hno w pc rem hget

/-- The issue of a no-increment arrival has no barrier action of its own. -/
theorem objectAction_noinc_issue {X : Execution} {S : Snapshot} {i : EvId} {m : Loc}
    (h : X.AsyncArrive i m true) (target : Loc) :
    objectAction X S target (.thread i) = none := by
  obtain ⟨pc, hp⟩ := h
  simp [objectAction, hp]

/-- The asynchronous stage of a recorded no-increment arrival decrements the pending count once. -/
theorem objectAction_noinc_arriveOn {X : Execution} {i : EvId} {m : Loc}
    (hi : X.AsyncArrive i m true) (ha : X.async.arrived i = true) :
    objectAction X X.async m (.async i .arriveOn) = some (.arrive 1 0) := by
  obtain ⟨pc, hp⟩ := hi
  simp [objectAction, hp, ha]

/-- A recorded arrive-on requires every earlier ordinary copy of its issuing thread to write. -/
theorem ArriveOk.write_of_prior_copy {X : Execution} {i j : EvId} {s : Spec}
    {m : Loc} {noinc : Bool} (h : ArriveOk X) (ha : X.async.arrived j = true)
    (hi : X.Copy i s) (hc : s.completion = .asyncGroup)
    (hj : X.AsyncArrive j m noinc) (ht : i.1 = j.1) (hb : i.2 < j.2) :
    ∃ bs, (X.async.copies i).writeBytes = some bs := by
  have hwrite := (h j ha).2 i ⟨ht, hb, ⟨s, hi, hc⟩, ⟨m, noinc, hj⟩⟩
  exact Option.isSome_iff_exists.mp hwrite

/-- An acquire poll that observes a tracking arrive-on also observes the corresponding copy write
when the scopes meet. -/
theorem asyncFinished_of_arriveOn {L : Launch} {X : Execution} {i j w : EvId}
    {m : Loc} {ws : MbarScope} {noinc : Bool} (ht : TracksCpAsync X i j)
    (hj : X.AsyncArrive j m noinc) (ha : X.async.arrived j = true)
    (hw : WaitObserves X (.async j .arriveOn) w m true ws)
    (hs : ScopesMeet L .cluster i.1 ws w.1) :
    AsyncFinished L X i (.write .copy) w :=
  Or.inr ⟨ws, ⟨.async j .arriveOn, m, Or.inr ⟨j, noinc, rfl, ht, hj, ha⟩, hw⟩, hs⟩

end AsyncCopy


/-- Adding a counted stage at a real issue strictly increases the execution measure when
the thread traces stay fixed. -/
theorem Execution.size_lt_of_asyncSize_lt {L : Launch} {X Y : Execution} {i : EvId}
    (hle : X.le Y) (htr : Y.tr = X.tr) (hg : i.1 < L.threads)
    (hi : i.2 < (X.tr i.1).length) (hs : X.asyncSize i < Y.asyncSize i) :
    X.size L < Y.size L := by
  open Proof.ExecutionCountedPrefix in
  have hlocal : threadMeasure X i.1 + 1 ≤ threadMeasure Y i.1 := by
    have hpoint (k : Nat) :
        (if k = i.2 then X.asyncSize (i.1, k) + 1 else X.asyncSize (i.1, k))
          ≤ Y.asyncSize (i.1, k) := by
      by_cases hk : k = i.2
      · subst k; exact (ite_eq_left rfl).symm ▸ hs
      · rw [ite_eq_right hk]
        exact asyncSize_mono hle _
    have hsum := List.sum_le_sum (fun k (_ : k ∈ List.range (X.tr i.1).length) => hpoint k)
    rw [sum_range_bump, ite_eq_left hi] at hsum
    simpa [threadMeasure, htr, Nat.add_assoc] using
      Nat.add_le_add_left hsum ((X.tr i.1).countP Event.counts)
  open Proof.ExecutionCountedPrefix in
  have hpoint (g : Nat) : (if g = i.1 then threadMeasure X g + 1 else threadMeasure X g)
      ≤ threadMeasure Y g := by
    by_cases hg' : g = i.1
    · subst g; simpa using hlocal
    · rw [ite_eq_right hg']
      exact threadMeasure_mono hle g
  open Proof.ExecutionCountedPrefix in
  have hsum := List.sum_le_sum (fun g (_ : g ∈ List.range L.threads) => hpoint g)
  rw [sum_range_bump, ite_eq_left hg] at hsum
  change X.threadSize L + 1 ≤ Y.threadSize L at hsum
  have hp := Proof.ExecutionCountedPrefix.pairSize_mono hle L
  unfold Execution.size
  omega

end

end PTX
