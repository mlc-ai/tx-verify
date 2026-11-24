-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Arith.MixedRadix
public import Lemmas.Arith.WarpPrefix
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

/-- The number of dual-stage query tiles assigned to one request. -/
def requestTiles (p : Params) (b : Nat) : Nat := (p.qLength b + 255) / 256

/-- Number of query tiles for requests preceding `b`, without head replication. -/
def tilePrefix (p : Params) (b : Nat) : Nat := ∑ i ∈ Finset.range b, requestTiles p i

theorem requestTiles_mul_le (p : Params) (b : Nat) :
    requestTiles p b * 256 ≤ p.qLength b + 255 :=
  Nat.div_mul_le_self _ _

theorem requestTile_has_row {p : Params} {b tile : Nat} (ht : tile < requestTiles p b) :
    tile * 256 < p.qLength b := by
  have hm := requestTiles_mul_le p b
  omega

theorem row_in_requestTile {p : Params} {b row : Nat} (hr : row < p.qLength b) :
    row / 256 < requestTiles p b := by
  unfold requestTiles
  omega

theorem tilePrefix_succ (p : Params) (b : Nat) :
    tilePrefix p (b + 1) = tilePrefix p b + requestTiles p b := by
  exact Finset.sum_range_succ ..

/-- The cumulative Q array is the sum of its successive request lengths. -/
theorem Pre.sum_qLength {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b : Nat} (hb : b ≤ p.batch) :
    (∑ i ∈ Finset.range b, p.qLength i) = p.qOffset b := by
  induction b with
  | zero => simpa using hp.shape.2.2.2.2.1.symm
  | succ b ih =>
    rw [Finset.sum_range_succ, ih (by omega), Params.qLength,
      Nat.add_sub_of_le (hp.lengths b (by omega)).1]

/-- The padded launch grid has a CTA for every head of every valid query tile. -/
theorem Pre.tiles_fit_grid {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    tilePrefix p p.batch * p.heads ≤ l.grid := by
  have htiles : tilePrefix p p.batch * 256 ≤ p.totalQ + 255 * p.batch := by
    unfold tilePrefix
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ i ∈ Finset.range p.batch, (p.qLength i + 255) :=
        Finset.sum_le_sum fun i _ => requestTiles_mul_le p i
      _ = _ := by
        rw [Finset.sum_add_distrib, hp.sum_qLength (Nat.le_refl _)]
        simp [Params.totalQ, Nat.mul_comm]
  rw [hp.grid.2.1, Params.grid]
  exact Nat.mul_le_mul_right _ ((Nat.le_div_iff_mul_le (by decide)).2 htiles)

theorem tilePrefix_mono (p : Params) : Monotone (tilePrefix p) := by
  intro a b hab
  unfold tilePrefix
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun i _ _ => Nat.zero_le (requestTiles p i))

/-- The scheduler's prefix intervals identify one request for every valid work item.
Requests with zero query rows have empty intervals. -/
theorem tileBatch_existsUnique (p : Params) {item : Nat}
    (hItem : item < tilePrefix p p.batch * p.heads) :
    ∃! b, b < p.batch ∧ tilePrefix p b * p.heads ≤ item ∧
      item < tilePrefix p (b + 1) * p.heads := by
  have existsBatch (n : Nat) (h : item < tilePrefix p n * p.heads) :
      ∃ b < n, tilePrefix p b * p.heads ≤ item ∧
        item < tilePrefix p (b + 1) * p.heads := by
    induction n with
    | zero => simp [tilePrefix] at h
    | succ n ih =>
      by_cases hh : item < tilePrefix p n * p.heads
      · obtain ⟨b, hb, hlo, hhi⟩ := ih hh
        exact ⟨b, by omega, hlo, hhi⟩
      · exact ⟨n, by omega, Nat.le_of_not_lt hh, h⟩
  obtain ⟨b, hb, hlo, hhi⟩ := existsBatch p.batch hItem
  refine ⟨b, ⟨hb, hlo, hhi⟩, ?_⟩
  intro b' hb'
  rcases Nat.lt_trichotomy b' b with h | h | h
  · have hle := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b' + 1 ≤ b by omega))
    omega
  · exact h
  · have hle := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b + 1 ≤ b' by omega))
    omega

/-- The LPT scheduler groups query heads by an L2 capacity of 800 key blocks.
A work tile contains two 128-row stages, so the scheduler estimates two key blocks per tile. -/
def sectionWidth (tiles heads : Nat) : Nat :=
  min heads
    (if 32 * tiles ≤ 800 then 16 else if 16 * tiles ≤ 800 then 8
      else if 8 * tiles ≤ 800 then 4 else if 4 * tiles ≤ 800 then 2 else 1)

/-- Coordinates inside one request. Sections visit the last query tile first.
The final section uses the remaining head count as its stride. -/
def sectionCoords (tiles heads width item : Nat) : Nat × Nat :=
  let sectionId := item / (width * tiles)
  let start := sectionId * width
  let count := min width (heads - start)
  let pos := item % (width * tiles)
  (tiles - 1 - pos / count, start + pos % count)

/-- Flat index within the request for one query tile and head. -/
def sectionItem (tiles heads width tile head : Nat) : Nat :=
  let start := head / width * width
  let count := min width (heads - start)
  start * tiles + (tiles - 1 - tile) * count + head % width

/-- Each query tile and head belongs to the request and is recovered by the LPT decoder. -/
theorem sectionCoords_item {tiles heads width tile head : Nat}
    (hw : 0 < width) (ht : tile < tiles) (hh : head < heads) :
    sectionItem tiles heads width tile head < tiles * heads ∧
      sectionCoords tiles heads width (sectionItem tiles heads width tile head) = (tile, head) := by
  let sectionId := head / width
  let start := sectionId * width
  let count := min width (heads - start)
  let offset := head % width
  let back := tiles - 1 - tile
  have hHead : offset + start = head := Nat.mod_add_div' _ _
  have hStart : start ≤ head := by omega
  have hCount : offset < count := by
    exact Nat.lt_min.mpr ⟨Nat.mod_lt _ hw, by omega⟩
  have hCountW : count ≤ width := Nat.min_le_left _ _
  have hCountH : start + count ≤ heads := by
    have := Nat.min_le_right width (heads - start)
    omega
  have hBack : back + 1 ≤ tiles := by omega
  have hPos : back * count + offset < tiles * count := by
    have h := Nat.mul_le_mul_right count hBack
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  have hPosW : back * count + offset < width * tiles :=
    Nat.lt_of_lt_of_le hPos (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left tiles hCountW)
  have hItem : sectionItem tiles heads width tile head =
      sectionId * (width * tiles) + (back * count + offset) := by
    change (sectionId * width) * tiles + back * count + offset = _
    ring
  have hBound : sectionItem tiles heads width tile head < tiles * heads := by
    change start * tiles + back * count + offset < tiles * heads
    have h := Nat.mul_le_mul_right tiles hCountH
    rw [Nat.add_mul, Nat.mul_comm count, Nat.mul_comm heads] at h
    omega
  have ⟨hSection, hPosEq⟩ := Nat.digits_of_lt (q := sectionId) hPosW
  have ⟨hBackEq, hOffsetEq⟩ := Nat.digits_of_lt (q := back) hCount
  refine ⟨hBound, ?_⟩
  rw [hItem]
  simp only [sectionCoords, hSection, hPosEq]
  change (tiles - 1 - (back * count + offset) / count,
    start + (back * count + offset) % count) = (tile, head)
  rw [hBackEq, hOffsetEq]
  congr <;> omega

/-- Every in-range flat index decodes to an in-range coordinate and can be recovered from it. -/
theorem sectionItem_coords {tiles heads width item : Nat}
    (hw : 0 < width) (hi : item < tiles * heads) :
    let pos := sectionCoords tiles heads width item
    pos.1 < tiles ∧ pos.2 < heads ∧ sectionItem tiles heads width pos.1 pos.2 = item := by
  let sectionId := item / (width * tiles)
  let start := sectionId * width
  let count := min width (heads - start)
  let pos := item % (width * tiles)
  have ht : 0 < tiles := Nat.pos_of_ne_zero fun ht => by simp [ht] at hi
  have hwT : 0 < width * tiles := Nat.mul_pos hw ht
  have hJoin : pos + start * tiles = item := by
    simpa only [start, sectionId, pos, Nat.mul_assoc] using Nat.mod_add_div' item (width * tiles)
  have hStart : start < heads := by
    by_contra! hs
    have h := Nat.mul_le_mul_right tiles hs
    rw [Nat.mul_comm heads] at h
    omega
  have hCount : 0 < count := Nat.lt_min.mpr ⟨hw, by omega⟩
  have hPos : pos < count * tiles := by
    by_cases hWidth : width ≤ heads - start
    · rw [show count = width from Nat.min_eq_left hWidth]
      exact Nat.mod_lt _ hwT
    · have he : count + start = heads := by
        dsimp [count]
        rw [Nat.min_eq_right (by omega)]
        omega
      have h := congrArg (fun n => n * tiles) he
      rw [Nat.add_mul, Nat.mul_comm heads] at h
      omega
  let back := pos / count
  let offset := pos % count
  have hBack : back < tiles :=
    (Nat.div_lt_iff_lt_mul hCount).2 (by simpa only [Nat.mul_comm] using hPos)
  have hOffset : offset < count := Nat.mod_lt _ hCount
  have hWidth : count ≤ width := Nat.min_le_left _ _
  have hCountHead : count ≤ heads - start := Nat.min_le_right _ _
  have hOffsetWidth : offset < width := Nat.lt_of_lt_of_le hOffset hWidth
  have ⟨hSection, hHead⟩ := Nat.digits_of_lt (q := sectionId) hOffsetWidth
  change (tiles - 1 - back) < tiles ∧ start + offset < heads ∧
    sectionItem tiles heads width (tiles - 1 - back) (start + offset) = item
  refine ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega), by omega, ?_⟩
  unfold sectionItem
  change ((sectionId * width + offset) / width * width) * tiles +
    (tiles - 1 - (tiles - 1 - back)) *
      min width (heads - ((sectionId * width + offset) / width * width)) +
    (sectionId * width + offset) % width = item
  rw [hSection, hHead, Nat.sub_sub_self (Nat.le_sub_one_of_lt hBack)]
  change start * tiles + back * count + offset = item
  have h := Nat.mod_add_div' pos count
  change offset + back * count = pos at h
  omega

theorem sectionWidth_pos {tiles heads : Nat} (h : 0 < heads) :
    0 < sectionWidth tiles heads := by
  unfold sectionWidth
  apply Nat.lt_min.mpr
  refine ⟨h, ?_⟩
  split <;> try decide
  split <;> try decide
  split <;> try decide
  split <;> decide

/-- The CTA assigned to a query tile and head. -/
def workItem (p : Params) (batch tile head : Nat) : Nat :=
  let tiles := requestTiles p batch
  tilePrefix p batch * p.heads +
    sectionItem tiles p.heads (sectionWidth tiles p.heads) tile head

/-- Every valid query row has a CTA whose scheduler coordinates select its tile and head. -/
theorem Pre.row_workItem {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch row head : Nat} (hb : batch < p.batch) (hr : row < p.qLength batch)
    (hh : head < p.heads) :
    let g := workItem p batch (row / 256) head
    g < l.grid ∧ tilePrefix p batch * p.heads ≤ g ∧
      g < tilePrefix p (batch + 1) * p.heads ∧
      sectionCoords (requestTiles p batch) p.heads
        (sectionWidth (requestTiles p batch) p.heads) (g - tilePrefix p batch * p.heads) =
        (row / 256, head) := by
  obtain ⟨hbound, hcoord⟩ :=
    sectionCoords_item (sectionWidth_pos (Nat.zero_lt_of_lt hh)) (row_in_requestTile hr) hh
  have hgt : workItem p batch (row / 256) head < tilePrefix p (batch + 1) * p.heads := by
    unfold workItem
    dsimp only
    rw [tilePrefix_succ, Nat.add_mul]
    exact Nat.add_lt_add_left hbound _
  have hG := Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch + 1 ≤ p.batch by omega))
  refine ⟨lt_of_lt_of_le hgt (hG.trans hp.tiles_fit_grid), ?_, hgt, ?_⟩
  · exact Nat.le_add_right _ _
  · simpa [workItem] using hcoord

/-- Lane 31 carries the last request's ending offset, leaving 31 request counts per group. -/
def groupLaneTiles (p : Params) (first lane : Nat) : Nat :=
  if lane < 31 ∧ first + lane < p.batch then requestTiles p (first + lane) else 0

/-- Prefix sums in a warp recover the batch prefix, clipping the final partial group. -/
theorem groupTiles_eq (p : Params) {first n : Nat}
    (hf : first ≤ p.batch) (hn : n ≤ 32) :
    tilePrefix p first + (∑ lane ∈ Finset.range n, groupLaneTiles p first lane) =
      tilePrefix p (min p.batch (first + min 31 n)) := by
  induction n with
  | zero => simp [Nat.min_eq_right hf]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih (by omega)]
    by_cases hLane : n < 31
    · have hm : min 31 n = n := Nat.min_eq_right (by omega)
      have hm' : min 31 (n + 1) = n + 1 := Nat.min_eq_right (by omega)
      by_cases hNext : first + n < p.batch
      · rw [hm, hm', Nat.min_eq_right (show first + n ≤ p.batch by omega),
          Nat.min_eq_right (show first + (n + 1) ≤ p.batch by omega)]
        simp [groupLaneTiles, hLane, hNext, ← Nat.add_assoc, tilePrefix_succ]
      · rw [hm, hm', Nat.min_eq_left (show p.batch ≤ first + n by omega),
          Nat.min_eq_left (show p.batch ≤ first + (n + 1) by omega)]
        simp [groupLaneTiles, hNext]
    · rw [Nat.min_eq_left (show 31 ≤ n by omega),
        Nat.min_eq_left (show 31 ≤ n + 1 by omega)]
      simp [groupLaneTiles, hLane]

theorem Pre.heads_signed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) :
    p.heads < 2 ^ 31 := by
  have hgrid := hp.grid.2.1
  have hGridPos := hp.grid.1
  unfold Params.grid at hgrid hGridPos
  set padded := (p.totalQ + 255 * p.batch) / 256
  have hPos : 0 < padded := Nat.pos_of_ne_zero fun h => by simp [h] at hGridPos
  have h := Nat.mul_le_mul_right p.heads (show 1 ≤ padded from hPos)
  rw [Nat.one_mul, ← hgrid] at h
  exact lt_of_le_of_lt h hp.grid.2.2

/-- All request-prefix offsets multiplied by the number of heads fit the signed scheduler word. -/
theorem Pre.prefixWork_signed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch : Nat} (hb : batch ≤ p.batch) : tilePrefix p batch * p.heads < 2 ^ 31 := by
  have h := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hb)
  exact lt_of_le_of_lt (h.trans hp.tiles_fit_grid) hp.grid.2.2

/-- No prefix intermediate exceeds the signed word range, including inactive lanes. -/
theorem Pre.groupWindow_signed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {first lane : Nat} (hf : first ≤ p.batch) (hl : lane < 32) (width : Nat) :
    prefixWindow (groupLaneTiles p first) width lane < 2 ^ 31 := by
  have hsum := groupTiles_eq p hf (show (32 : Nat) ≤ 32 by decide)
  have hsigned := hp.prefixWork_signed (Nat.min_le_left p.batch (first + 31))
  have hPos : 1 ≤ p.heads := by
    have h := hp.shape.2.2.1
    simp [Params.heads]
    omega
  have h := Nat.mul_le_mul_left (tilePrefix p (min p.batch (first + 31))) hPos
  rw [Nat.mul_one] at h
  have hbound := prefixWindow_le_warp (groupLaneTiles p first) width hl
  change tilePrefix p first + (∑ lane ∈ Finset.range 32, groupLaneTiles p first lane) =
    tilePrefix p (min p.batch (first + 31)) at hsum
  omega

/-- Skipping a full group advances by 31; the clipped final group ends the scan. -/
theorem groupSkip_progress {first batch : Nat} (hf : first < batch) :
    first < min batch (first + 31) ∧ min batch (first + 31) ≤ batch := by
  exact ⟨Nat.lt_min.mpr ⟨hf, by omega⟩, Nat.min_le_left _ _⟩

/-- Passing the group-end test identifies a request inside the current group. -/
theorem groupContains_request (p : Params) {first item : Nat}
    (hLow : tilePrefix p first * p.heads ≤ item)
    (hHigh : item < tilePrefix p (min p.batch (first + 31)) * p.heads) :
    ∃! b, first ≤ b ∧ b < first + 31 ∧ b < p.batch ∧
      tilePrefix p b * p.heads ≤ item ∧ item < tilePrefix p (b + 1) * p.heads := by
  have hEnd := Nat.mul_le_mul_right p.heads (tilePrefix_mono p
    (show min p.batch (first + 31) ≤ p.batch from Nat.min_le_left _ _))
  obtain ⟨b, ⟨hb, hStart, hStop⟩, hUnique⟩ :=
    tileBatch_existsUnique p (lt_of_lt_of_le hHigh hEnd)
  have hf : first ≤ b := by
    by_contra! hn
    have h := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b + 1 ≤ first by omega))
    omega
  have hg : b < first + 31 := by
    by_contra! hn
    have h := Nat.mul_le_mul_right p.heads (tilePrefix_mono p
      (Nat.le_trans (Nat.min_le_right p.batch (first + 31)) hn))
    omega
  exact ⟨b, ⟨hf, hg, hb, hStart, hStop⟩,
    fun b' h => hUnique b' ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-- In the selected group, the ballot masks exactly the lanes before the selected batch. -/
theorem groupBallot_iff (p : Params) {first lane b item : Nat} (hf : first ≤ b)
    (hGroup : b < first + 31) (hb : b < p.batch) (hl : lane < 32)
    (hlo : tilePrefix p b * p.heads ≤ item)
    (hhi : item < tilePrefix p (b + 1) * p.heads) :
    (tilePrefix p first + (∑ i ∈ Finset.range (lane + 1), groupLaneTiles p first i)) *
      p.heads ≤ item ↔ first + lane < b := by
  rw [groupTiles_eq p (by omega) (by omega)]
  constructor
  · intro hEnd
    by_contra! hn
    have hi : b + 1 ≤ min p.batch (first + min 31 (lane + 1)) := by omega
    have hp := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hi)
    omega
  · intro hLane
    have hi : min p.batch (first + min 31 (lane + 1)) ≤ b := by omega
    exact Nat.le_trans (Nat.mul_le_mul_right p.heads (tilePrefix_mono p hi)) hlo

end PTX.Kernels.TmlFa4Fwd
