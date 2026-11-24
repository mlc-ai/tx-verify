-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaIssue
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The MMA thread's counts at its MMAs

At an MMA (`mma_origin`) of a thread, which led every election of its trace
(`mma_electLead`), the run invariant `Mma.Counts` gives each count of the thread's earlier events
as a formula in the state's item `i`, trip `t` and site `.mma b j` (`MmaSt`), with `n` KV trips
per item:

* the MMAs before it: `32 n i + 8 (blk b t) + j` (`mmas_at`), `blk b t` the number of the asm
  block in the item (blocks 0, 1 of the first K; blocks `2 … 5` of trip `t`, `4 t + 2 …`; the
  last V's blocks 6, 7 at `4 t + 2`, `4 t + 3` with `t = n - 1`);
* the commits to the S-full object of stage `k`: `n i + sv k b t`; the successful polls of the
  P-ready and second P-ready objects of stage `k`: `n i + pv k b t`, `n i + p2v k b j t`; the
  commits to the O-full object of stage `k`: `i + ofv k b`.

Distinct MMAs of a thread have distinct MMA counts, and the count decodes the item, trip and
site (`mma_num_inj`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Mma

/-- The number of asm block `b` within the item, at trip `t`. -/
def blk : Fin 8 → Nat → Nat
  | 0, _ => 0
  | 1, _ => 1
  | 2, t => 2 + 4 * t
  | 3, t => 3 + 4 * t
  | 4, t => 4 + 4 * t
  | 5, t => 5 + 4 * t
  | 6, t => 2 + 4 * t
  | 7, t => 3 + 4 * t

/-- The trips at which block `b` runs: 0 for the first K's blocks, a loop trip before the last
for the loop's blocks, the last trip for the last V's blocks. -/
def TripAt (n : Nat) (b : Fin 8) (t : Nat) : Prop :=
  if b.val < 2 then t = 0 else if b.val < 6 then t + 1 < n else t + 1 = n

/-- S-full commits of stage `k` before MMA block `b` of the item (beyond `n i`). -/
def sv : Fin 2 → Fin 8 → Nat → Nat
  | 0, 0, _ => 0
  | 0, 1, _ => 1
  | 0, 4, t => 2 + t
  | 0, 5, t => 2 + t
  | 0, _, t => 1 + t
  | 1, 0, _ => 0
  | 1, 1, _ => 0
  | 1, _, t => 1 + t

/-- Successful P-ready polls of stage `k` before MMA block `b` of the item (beyond `n i`). -/
def pv : Fin 2 → Fin 8 → Nat → Nat
  | _, 0, _ => 0
  | _, 1, _ => 0
  | 0, _, t => 1 + t
  | 1, 2, t => t
  | 1, 3, t => t
  | 1, 6, t => t
  | 1, _, t => 1 + t

/-- Successful second P-ready polls of stage `k` before MMA `j` of block `b` of the item (beyond
`n i`). -/
def p2v : Fin 2 → Fin 8 → Fin 8 → Nat → Nat
  | _, 0, _, _ => 0
  | _, 1, _, _ => 0
  | 0, 2, j, t => if j.val < 6 then t else 1 + t
  | 0, 6, j, t => if j.val < 6 then t else 1 + t
  | 0, _, _, t => 1 + t
  | 1, 4, j, t => if j.val < 6 then t else 1 + t
  | 1, 7, j, t => if j.val < 6 then t else 1 + t
  | 1, 5, _, t => 1 + t
  | 1, _, _, t => t

/-- O-full commits of stage `k` before MMA block `b` of the item (beyond `i`). -/
def ofv : Fin 2 → Fin 8 → Nat
  | 0, 7 => 1
  | _, _ => 0

theorem tripAt_of_inv {g : Nat} {d : D} {b j : Fin 8} (hinv : Inv L g d)
    (hs : d.site = .mma b j) : TripAt (trips L) b d.t := by
  have h := hinv.trip
  unfold TripOk at h
  rw [hs] at h
  unfold TripAt
  fin_cases b <;> simp_all [region]

theorem mmaA_eq (b j : Fin 8) (t : Nat) :
    mmaA (.mma b j) + 32 * (t * (Site.mma b j).loop) = 8 * blk b t + j.val := by
  fin_cases b <;> fin_cases j <;>
    simp [mmaA, blk, Site.after, Site.inTrip, Site.loop, Site.ord, mmaOrd, blockPos, isPv] <;>
    omega

theorem sA_eq (k : Fin 2) (b j : Fin 8) (t : Nat) :
    sA k (.mma b j) + 1 * (t * (Site.mma b j).loop) = sv k b t := by
  fin_cases k <;> fin_cases b <;> fin_cases j <;>
    simp [sA, sv, Site.after, Site.inTrip, Site.loop, Site.ord, mmaOrd, isPv]

theorem pA_eq (k : Fin 2) (b j : Fin 8) (t : Nat) :
    pA k (.mma b j) + 1 * (t * (Site.mma b j).loop) = pv k b t := by
  fin_cases k <;> fin_cases b <;> fin_cases j <;>
    simp [pA, pv, Site.after, Site.inTrip, Site.loop, Site.ord, mmaOrd, isPv]

set_option maxHeartbeats 2000000 in
theorem p2A_eq (k : Fin 2) (b j : Fin 8) (t : Nat) :
    p2A k (.mma b j) + 1 * (t * (Site.mma b j).loop) = p2v k b j t := by
  fin_cases k <;> fin_cases b <;> fin_cases j <;>
    simp [p2A, p2v, Site.after, Site.inTrip, Site.loop, Site.ord, mmaOrd, isPv]

theorem ofA_eq (k : Fin 2) (b j : Fin 8) : ofA k (.mma b j) = ofv k b := by
  fin_cases k <;> fin_cases b <;> fin_cases j <;>
    simp [ofA, ofv, Site.after, Site.ord, mmaOrd, isPv]

/-- A block and trip that run fit in the item's `4 n` blocks. -/
theorem blk_lt {n : Nat} {b : Fin 8} {t : Nat} (hn : 1 ≤ n) (h : TripAt n b t) :
    blk b t < 4 * n := by
  unfold TripAt at h
  fin_cases b <;> simp_all [blk] <;> omega

/-- The block number and trip decode the block. -/
theorem blk_inj {n : Nat} {b b' : Fin 8} {t t' : Nat} (h : TripAt n b t) (h' : TripAt n b' t')
    (he : blk b t = blk b' t') : b = b' ∧ t = t' := by
  unfold TripAt at h h'
  fin_cases b <;> fin_cases b' <;> simp_all [blk] <;> omega

end Mma

/-- The state of an MMA of thread `g` at its event `k`: the MMA warp's state `d` at site
`.mma b j`, with the role's run invariant and state invariant, the MMA the site names, and
every election of the thread's trace returned its lane. -/
structure MmaSt (L : Launch) (X : Execution) (g k : Nat) (d : Mma.D) (b j : Fin 8) : Prop where
  state : Frame.stateAt (code L) X g k = some (some (.inr (.mma d)))
  site : d.site = .mma b j
  counts : Mma.Counts L g d ((X.tr g).take k)
  inv : Mma.Inv L g d
  lt : g < L.threads
  warp : warpOf L g = 12
  issue : X.MmaIssue (g, k) (Mma.mmaCol b) (Mma.mmaSpec L g d b j) (Mma.mmaAcc d b j)
    (List.replicate 8 0)
  lead : ElectLead L g (X.tr g)

/-- **An MMA's state.** -/
theorem mmaSt_of (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k dd : Nat} {s : OperandSpec} {acc : Bool}
    {mask : List Nat} (hi : X.MmaIssue (g, k) dd s acc mask) :
    ∃ d b j, MmaSt L X g k d b j ∧ dd = Mma.mmaCol b ∧ s = Mma.mmaSpec L g d b j ∧
      acc = Mma.mmaAcc d b j ∧ mask = List.replicate 8 0 := by
  have hl := mma_electLead hpre hX ht ⟨_, _, _, _, hi⟩
  obtain ⟨d, b, j, hσ, hs, hJ, hinv, hg, hw, rfl, rfl, rfl, rfl⟩ := mma_origin hpre hX ht hi
  exact ⟨d, b, j, ⟨hσ, hs, hJ, hinv, hg, hw, hi, hl⟩, rfl, rfl, rfl, rfl⟩

theorem trips_pos (hpre : Pre P L mem0) : 1 ≤ Mma.trips L := by
  have h1 := skOf_eq hpre
  have h2 := hpre.skPos
  unfold Mma.trips
  omega

namespace MmaSt

variable {g k : Nat} {d : Mma.D} {b j : Fin 8}

theorem tripAt (h : MmaSt L X g k d b j) : Mma.TripAt (Mma.trips L) b d.t :=
  Mma.tripAt_of_inv h.inv h.site

theorem leadTake (h : MmaSt L X g k d b j) : ElectLead L g ((X.tr g).take k) := h.lead.take k

/-- The MMAs before it. -/
theorem mmas (h : MmaSt L X g k d b j) :
    ((X.tr g).take k).countP Mma.isMma = 32 * Mma.trips L * d.i + 8 * Mma.blk b d.t + j.val := by
  rw [h.counts.mmas h.leadTake]
  unfold Mma.cnt
  rw [h.site, Nat.add_assoc, Mma.mmaA_eq]
  ring

/-- The S-full commits of stage `st` before it. -/
theorem sCommits (h : MmaSt L X g k d b j) (st : Fin 2) :
    sCommits L X g st k = Mma.trips L * d.i + Mma.sv st b d.t := by
  unfold PTX.Kernels.FlashAttn4Fwd.Proof.sCommits
  rw [show sFullBar L (ctaOf L g) st = Mma.bar L g (.sFull st) from rfl,
    h.counts.sFull h.leadTake st]
  unfold Mma.cnt
  rw [h.site, Nat.add_assoc, Mma.sA_eq]
  ring

/-- The successful P-ready polls of stage `st` before it. -/
theorem pPolls (h : MmaSt L X g k d b j) (st : Fin 2) :
    pPolls L X g st k = Mma.trips L * d.i + Mma.pv st b d.t := by
  unfold PTX.Kernels.FlashAttn4Fwd.Proof.pPolls
  rw [show pReadyBar L (ctaOf L g) st = Mma.bar L g (.pReady st) from rfl,
    h.counts.pReady st]
  unfold Mma.cnt
  rw [h.site, Nat.add_assoc, Mma.pA_eq]
  ring

/-- The successful second P-ready polls of stage `st` before it. -/
theorem p2Polls (h : MmaSt L X g k d b j) (st : Fin 2) :
    p2Polls L X g st k = Mma.trips L * d.i + Mma.p2v st b j d.t := by
  unfold PTX.Kernels.FlashAttn4Fwd.Proof.p2Polls
  rw [show pReady2Bar L (ctaOf L g) st = Mma.bar L g (.pReady2 st) from rfl,
    h.counts.pReady2 st]
  unfold Mma.cnt
  rw [h.site, Nat.add_assoc, Mma.p2A_eq]
  ring

/-- The O-full commits of stage `st` before it. -/
theorem oFullCommits (h : MmaSt L X g k d b j) (st : Fin 2) :
    oFullCommits L X g st k = d.i + Mma.ofv st b := by
  unfold PTX.Kernels.FlashAttn4Fwd.Proof.oFullCommits
  rw [show oFullBar L (ctaOf L g) st = Mma.bar L g (.oFull st) from rfl,
    h.counts.oFull h.leadTake st]
  unfold Mma.cnt
  rw [h.site, Mma.ofA_eq]
  ring

/-- The item is one of the cluster's, on the leader CTA. -/
theorem item (h : MmaSt L X g k d b j) : Mma.work L g d.i < totOf L ∧ Mma.rank L g = 0 :=
  h.inv.i (by rw [h.site]; trivial)

/-- The cells it writes. -/
theorem cell_iff (h : MmaSt L X g k d b j) (cell : Cell) :
    X.MmaCell (g, k) cell ↔ ∃ row col, row < 256 ∧ col < 128 ∧
      cell = ⟨if row < 128 then Mma.pairLo L g else Mma.pairLo L g + 1, row % 128,
        Mma.mmaCol b + col⟩ := by
  have hb : Mma.mmaCol b + 128 ≤ 512 := by
    rcases Mma.mmaCol_cases b with ⟨-, h⟩ | ⟨-, h⟩ <;> have := Mma.mmaStage_lt b <;> omega
  constructor
  · rintro ⟨d', s', a', m', row, col, hi', hw'⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := mmaIssue_unique hi' h.issue
    rw [Mma.writeCell_eq (Mma.mmaSpec_descOk ..) hb, Mma.resultCell_iff (Mma.mmaSpec_descOk ..) hb,
      Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta] at hw'
    exact ⟨row, col, hw'⟩
  · rintro ⟨row, col, hr, hc, rfl⟩
    refine ⟨_, _, _, _, row, col, h.issue, ?_⟩
    rw [Mma.writeCell_eq (Mma.mmaSpec_descOk ..) hb, Mma.resultCell_iff (Mma.mmaSpec_descOk ..) hb,
      Mma.mmaSpec_lowCta, Mma.mmaSpec_highCta]
    exact ⟨hr, hc, rfl⟩

/-- Its cells are in the S region of its block's stage (a QK block) or in the O region (a PV
block). -/
theorem inS_iff (h : MmaSt L X g k d b j) {st : Nat} (hst : st < 2) :
    (∃ cell, X.MmaCell (g, k) cell ∧ InS st cell) ↔
      Mma.isPv b = false ∧ (Mma.mmaStage b).val = st := by
  have := Mma.mmaStage_lt b
  constructor
  · rintro ⟨cell, hc, hS⟩
    obtain ⟨row, col, -, hcol, rfl⟩ := (h.cell_iff cell).mp hc
    simp only [InS] at hS
    rcases Mma.mmaCol_cases b with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] at hS
    · exact ⟨hp, by omega⟩
    · omega
  · rintro ⟨hp, rfl⟩
    refine ⟨_, (h.cell_iff _).mpr ⟨0, 0, by decide, by decide, rfl⟩, ?_⟩
    rcases Mma.mmaCol_cases b with ⟨-, he⟩ | ⟨hp', -⟩
    · simp only [InS]; omega
    · rw [hp] at hp'; cases hp'

theorem inO_iff (h : MmaSt L X g k d b j) {st : Nat} :
    (∃ cell, X.MmaCell (g, k) cell ∧ InO st cell) ↔
      Mma.isPv b = true ∧ (Mma.mmaStage b).val = st := by
  have := Mma.mmaStage_lt b
  constructor
  · rintro ⟨cell, hc, hO⟩
    obtain ⟨row, col, -, hcol, rfl⟩ := (h.cell_iff cell).mp hc
    simp only [InO] at hO
    rcases Mma.mmaCol_cases b with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] at hO
    · omega
    · exact ⟨hp, by omega⟩
  · rintro ⟨hp, rfl⟩
    refine ⟨_, (h.cell_iff _).mpr ⟨0, 0, by decide, by decide, rfl⟩, ?_⟩
    rcases Mma.mmaCol_cases b with ⟨hp', -⟩ | ⟨-, he⟩
    · rw [hp] at hp'; cases hp'
    · simp only [InO]; omega

end MmaSt

end
end PTX.Kernels.FlashAttn4Fwd.Proof
