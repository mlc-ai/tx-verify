-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.IndexRingAccessOrder
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.GlobalWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.IndexCoordinateTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.StageWriteClasses
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1TmaLeader
import Lemmas.Order.Order

@[expose] public section

/-! # Byte causality for coordinates and validity masks -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.IndexSharedConflicts

open PTX PTX.Flow PTX.Proof AsyncCopy Protocol IndexRingThreads

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The four validity and coordinate slots occupy adjacent shared windows. -/
def Window (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 221696 ≤ l.addr ∧ l.addr < L.sharedBase + 222752

private def InSlot (L : Launch) (l : Loc) (block base size : Nat) : Prop :=
  L.sharedBase + base + size * (block % 4) ≤ l.addr ∧
    l.addr < L.sharedBase + base + size * (block % 4) + size

private def ByteUse (L : Launch) (l : Loc) (block : Nat) : Prop :=
  InSlot L l block 221696 8 ∨ InSlot L l block 221728 256

private theorem slot_eq {l : Loc} {a b : Nat} (ha : ByteUse L l a) (hb : ByteUse L l b) :
    indexSlot a = indexSlot b := by
  apply Fin.ext
  change a % 4 = b % 4
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases ha with ⟨ha, ha'⟩ <;>
    rcases hb with ⟨hb, hb'⟩ <;> omega

private def byteLane (L : Launch) (l : Loc) : Nat :=
  if l.addr < L.sharedBase + 221728 then
    4 * ((l.addr - (L.sharedBase + 221696)) % 8)
  else ((l.addr - (L.sharedBase + 221728)) % 256) / 8

private theorem writer_geometry {i : EvId} {a : Acc} {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hw : X.Writes i a bytes) (ha : a.Covers l) (hWin : Window L l) :
    ∃ block, IndexRing.ProducerWrite P L X i.1 i.2 block ∧
      ctaOf L i.1 = l.cta ∧ warpOf L i.1 = 7 ∧ laneOf L i.1 = byteLane L l ∧
      ByteUse L l block := by
  obtain ⟨g, j⟩ := i
  obtain ⟨hSh, hLo, hHi⟩ := hWin
  have hg := Frame.lt_of_get hX hw.choose_spec
  by_cases hMask : l.addr < L.sharedBase + 221728
  · obtain ⟨d, extra, q, hd, hSite, hInv, hLane, _, hLoc, _, _⟩ :=
      StageWriteClasses.validity_from_covered_write hpre hX hs ht hw ha hSh hLo hMask
    have hWarp : warpOf L g = 7 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
    have hPhase := hInv.phase_block (by rw [hSite]; intro h; cases h)
    have hCta := congrArg Loc.cta hLoc
    have hAddr := congrArg Loc.addr hLoc
    change l.addr = L.sharedBase + 221696 + 8 * d.phase + q.val at hAddr
    have hQ := q.isLt
    refine ⟨d.block, ⟨d, rfl, .inr ⟨extra, hSite⟩, hd⟩, hCta.symm, hWarp, ?_, .inl ?_⟩
    · rw [byteLane, ite_eq_left hMask, hLane]
      omega
    · unfold InSlot
      omega
  · obtain ⟨d, extra, high, hd, hSite, hInv, hLoc, hSize, _⟩ :=
      StageWriteClasses.coordinate_from_covered_write hpre hX hs ht hw ha hSh (by omega) hHi
    have hWarp : warpOf L g = 7 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
    have hPhase := hInv.phase_block (by rw [hSite]; intro h; cases h)
    have hIndex : d.site.sub < 2 := by rw [hSite]; cases extra <;> cases high <;> decide
    have hLane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
    obtain ⟨_, hc, haLo, haHi⟩ := ha
    rw [hLoc] at hc haLo haHi
    rw [hSize] at haHi
    change L.sharedBase + Wg1Index.coordOff L g d.phase + 4 * d.site.sub ≤ l.addr at haLo
    change l.addr < L.sharedBase + Wg1Index.coordOff L g d.phase + 4 * d.site.sub + 4 at haHi
    simp only [Wg1Index.coordOff, hPhase] at haLo haHi
    refine ⟨d.block, ⟨d, rfl, .inl ⟨extra, high, hSite⟩, hd⟩, hc.symm, hWarp, ?_, .inr ?_⟩
    · change laneOf L g = byteLane L l
      rw [byteLane, ite_eq_right hMask]
      omega
    · unfold InSlot
      omega

private theorem reader_geometry {g i block : Nat} {a : Acc} {values : List (Option Byte)} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hr : X.Reads (g, i) a values)
    (hd : IndexRing.ConsumerRead P L X g i block) (ha : a.Covers l) :
    l.space = .shared ∧ ctaOf L g = l.cta ∧ ByteUse L l block := by
  obtain ⟨tag, he⟩ := hr
  have hg := Frame.lt_of_get hX he
  rcases hd with ⟨d, rfl, ⟨k, j, hSite⟩, hd⟩ | ⟨d, rfl, hSite, hd⟩
  · obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
    obtain ⟨_, _, hKind, hSize, hLoc⟩ := IndexCoordinateTrace.read_word hpre hSite hf
    obtain rfl := (Kind.rd.inj hKind).1
    obtain ⟨hSh, hCta, hLo, hHi⟩ := ha
    rw [hLoc] at hSh hCta hLo hHi
    rw [hSize] at hHi
    have hK := k.isLt
    have hJ := j.isLt
    refine ⟨hSh, hCta.symm, .inr ?_⟩
    change L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 4 * _ ≤ l.addr at hLo
    change l.addr < L.sharedBase + Wg1Tma.coordBase (d.block % 4) + 4 * _ + 4 at hHi
    simp only [Wg1Tma.coordBase, Wg1Tma.coordPos] at hLo hHi
    unfold InSlot
    omega
  · obtain ⟨_, hf⟩ := RingEvents.fired_of_trace hX (hs g hg).machine he hd
    obtain ⟨_, _, hKind, hSize, hHalf, hLoc⟩ :=
      Wg0.composed_mask_footprint hpre hSite hf ⟨a, values, rfl⟩
    obtain rfl := (Kind.rd.inj hKind).1
    obtain ⟨hSh, hCta, hLo, hHi⟩ := ha
    rw [hLoc] at hSh hCta hLo hHi
    rw [hSize] at hHi
    refine ⟨hSh, hCta.symm, .inl ?_⟩
    simp only [Wg0.shLoc, Wg0.maskBase, Wg0.maskStride] at hLo hHi
    unfold InSlot
    omega

private theorem threading {g i block cta : Nat} {e : Event} {lane : Fin 32}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hLeader : ∀ g i (d : Wg1Tma.D), ctaOf L g = cta →
      Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)) →
      d.site ≠ .elect → g = cta * L.block + 160 + lane.val)
    (hc : ctaOf L g = cta) (he : X.get (g, i) = some e)
    (hr : IndexRing.ConsumerRead P L X g i block) :
    ∃ c, g = consumerThread L cta lane c := by
  rcases hr with ⟨d, _, ⟨k, j, hSite⟩, hd⟩ | ⟨d, _, hSite, hd⟩
  · refine ⟨⟨128, by decide⟩, ?_⟩
    simpa only [consumerThread, Nat.lt_irrefl, ↓reduceIte, Nat.add_assoc] using
      hLeader g i d hc hd (by simp [hSite])
  · have hg := Frame.lt_of_get hX he
    have hw := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
    obtain ⟨q, _, hEq⟩ := consumer_of_wg0 hpre hc hw lane
    exact ⟨q, hEq⟩

/-- Every covering ordinary producer write is ordered against the actual coordinate/mask read,
including writes from another use of the same physical slot. -/
theorem read_write_ordered {g i w j block : Nat} {a fp : Acc} {values : List (Option Byte)}
    {bytes : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads (g, i) a values) (hd : IndexRing.ConsumerRead P L X g i block)
    (hw : X.Writes (w, j) fp bytes) (ha : a.Covers l) (hf : fp.Covers l) (hWin : Window L l) :
    ByteCausality L X l (.thread (w, j)) (.thread (g, i)) ∨
      ByteCausality L X l (.thread (g, i)) (.thread (w, j)) := by
  let cta := l.cta
  obtain ⟨_, hCta, hReadUse⟩ := reader_geometry hpre hX hs hr hd ha
  obtain ⟨generation, hWriter, hCtaW, hWarpW, _, hWriteUse⟩ :=
    writer_geometry hpre hX hs ht hw hf hWin
  have hSlot := slot_eq hReadUse hWriteUse
  have hMachine (s : Nat) (hh : s < L.threads) := (hs s hh).machine
  have hg := Frame.lt_of_get hX hr.choose_spec
  have hGrid : cta < L.grid := by
    change l.cta < L.grid
    rw [← hCta]
    exact NamedBar.cta_lt hg
  obtain ⟨lane, hLeader⟩ := Wg1TmaLeader.cta_issuer (cta := cta) hpre hX hMachine
  have hTma : IndexRing.TmaConsumer P L X cta lane := by
    intro s t e d he hc hSite hd
    rw [hLeader s t d hc hd (by simp [hSite])]
    have hLane := lane.isLt
    simp only [laneOf, tidOf_eq hpre, hpre.block]
    omega
  let H := IndexRing.unit_ring_of_lane (slot := indexSlot block) hpre hX hGrid hMachine ht hTma
  change ctaOf L w = cta at hCtaW
  change warpOf L w = 7 at hWarpW
  change IndexRing.ProducerWrite P L X w j generation at hWriter
  obtain ⟨p, hp⟩ := producer_of_warp hpre hCtaW hWarpW
  obtain ⟨rtag, he⟩ := hr
  obtain ⟨wtag, hf⟩ := hw
  obtain ⟨c, hc⟩ := threading hpre hX hs hLeader hCta he hd
  rw [hp] at hWriter hCtaW hf ⊢
  rw [hc] at hd he hCta ⊢
  by_cases hLater : block / 4 < generation / 4
  · exact .inr (.direct (.inl (IndexRing.read_before_overwrite hpre hX H hMachine
      hCtaW hCta hSlot hLater hd hWriter hf)))
  · exact .inl (.direct (.inl (IndexRing.write_before_read_of_generation hpre hX H hMachine
      hCtaW hCta hSlot.symm (by omega) hWriter hd he)))

/-- A shared coordinate or mask byte has one issuing lane, so distinct writes are ordered. -/
theorem writes_ordered {e f : EvId} {a b : Acc} {bytes raw : List Byte} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (he : X.Writes e a bytes) (hf : X.Writes f b raw) (hn : e ≠ f)
    (ha : a.Covers l) (hb : b.Covers l) (hWin : Window L l) :
    ByteCausality L X l (.thread e) (.thread f) ∨ ByteCausality L X l (.thread f) (.thread e) := by
  obtain ⟨_, _, hCta, hWarp, hLane, _⟩ := writer_geometry hpre hX hs ht he ha hWin
  obtain ⟨_, _, hCta', hWarp', hLane', _⟩ := writer_geometry hpre hX hs ht hf hb hWin
  have hG : e.1 = f.1 := by
    have hCta := hCta.trans hCta'.symm
    have hWarp := hWarp.trans hWarp'.symm
    have hLane := hLane.trans hLane'.symm
    simp only [warpOf, laneOf, tidOf_eq hpre] at hWarp hLane
    unfold ctaOf at hCta
    rw [hpre.block] at hCta
    omega
  have hE : X.Access e a true := .inr (.inl ⟨bytes, he, rfl⟩)
  have hF : X.Access f b true := .inr (.inl ⟨raw, hf, rfl⟩)
  rcases Nat.lt_or_gt_of_ne (fun h => hn (Prod.ext hG h)) with hLt | hLt
  · exact .inl (.direct (.inl (.single (.inl (po_of_overlap hE hF hG hLt ⟨l, ha, hb⟩)))))
  · exact .inr (.direct (.inl (.single (.inl (po_of_overlap hF hE hG.symm hLt ⟨l, hb, ha⟩)))))

private theorem consumer_read_of_access {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    {l : Loc} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hr : X.Reads i a bytes) (ha : a.Covers l) (hWin : Window L l) :
    ∃ block, IndexRing.ConsumerRead P L X i.1 i.2 block := by
  obtain ⟨g, j⟩ := i
  rcases OrdinaryReadWindow.index_read_of_cover hpre hX hs ht hr ha hWin.2.1 hWin.2.2 with
    ⟨d, hd, hSite⟩ | ⟨d, hd, hSite⟩
  · exact ⟨d.block, .inl ⟨d, rfl, hSite, hd⟩⟩
  · exact ⟨d.block, .inr ⟨d, rfl, hSite, hd⟩⟩

/-- All ordinary conflicts at index coordinates or mask bytes have a bytewise causal order. -/
theorem ordinary_conflict_ordered {e f : EvId} {a b : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hc : Conflict X (.thread e) (.thread f) a b)
    (ha : a.Covers l) (hb : b.Covers l) (hWin : Window L l) :
    ByteCausality L X l (.thread e) (.thread f) ∨
      ByteCausality L X l (.thread f) (.thread e) := by
  obtain ⟨hne, ea, fb, hA, hB, hWrite, _⟩ := hc
  have plain {i : EvId} {a : Acc} {w : Bool} (h : X.Access i a w) :
      (∃ bytes, X.Reads i a bytes ∧ w = false) ∨ ∃ bytes, X.Writes i a bytes ∧ w = true :=
    (Execution.access_iff_of_not_rmw (fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩)).mp h
  rcases plain hA with ⟨bytes, hRead, hEa⟩ | ⟨bytes, hWr, _⟩ <;>
    rcases plain hB with ⟨raw, hRead', hFb⟩ | ⟨raw, hWr', _⟩
  · rw [hEa, hFb] at hWrite
    simp at hWrite
  · obtain ⟨block, hRole⟩ := consumer_read_of_access hpre hX hs ht hRead ha hWin
    obtain ⟨g, i⟩ := e
    obtain ⟨w, j⟩ := f
    exact (read_write_ordered hpre hX hs ht hRead hRole hWr' ha hb hWin).symm
  · obtain ⟨block, hRole⟩ := consumer_read_of_access hpre hX hs ht hRead' hb hWin
    obtain ⟨g, i⟩ := f
    obtain ⟨w, j⟩ := e
    exact read_write_ordered hpre hX hs ht hRead' hRole hWr hb ha hWin
  · exact writes_ordered hpre hX hs ht hWr hWr'
      (fun h => hne (congrArg Ref.thread h)) ha hb hWin

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.IndexSharedConflicts
