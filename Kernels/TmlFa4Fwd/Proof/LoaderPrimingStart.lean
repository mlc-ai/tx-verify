-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingScratchLoop
public import Kernels.TmlFa4Fwd.Proof.LoaderTripStart
public import Lemmas.Flow.OrBits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- Each loader lane computes page scratch for the rows it will publish via warp shuffles. -/
def primingLaneRow (tile lane : Nat) : Nat :=
  128 * tile + lane / 8 % 8 + kvCopyColumn lane false

private theorem primingStartCore {l : Launch} {g tile lane : Nat}
    (hTile : 128 * tile < 4294967296) :
    Seg kernel [] l g 7 481
      [(108, .pred true), (1044, .bits 16 3), (1081, b32 (lane / 8 % 8)),
       (1082, b32 (kvCopyColumn lane false)), (1838, b32 (128 * tile)), (7520, b64 1)]
      488 [(1093, b32 1), (1094, b32 3), (1095, b32 (primingLaneRow tile lane)),
        (7302, b64 1), (7172, b32 0), (772, .pred true)] := by
  let offset := lane / 8 % 8 + kvCopyColumn lane false
  have hOffsetEq : lane / 8 % 8 + kvCopyColumn lane false = offset := rfl
  have hCol : kvCopyColumn lane false = 8 * (lane % 8) := by rfl
  have hOffset : offset < 128 := by
    have h0 := Nat.mod_lt (lane / 8) (show 0 < 8 by decide)
    have h1 := Nat.mod_lt lane (show 0 < 8 by decide)
    dsimp [offset]
    rw [hCol]
    omega
  have hOr : offset ||| (128 * tile) = 128 * tile + offset := by
    rw [Nat.or_comm]
    exact lor_eq_add (k := 7) (by omega) hOffset
  have hRow : 128 * tile + offset = primingLaneRow tile lane := by
    simp only [primingLaneRow, offset, Nat.add_assoc]
  have hCol32 : kvCopyColumn lane false < 4294967296 := by dsimp only [offset] at hOffset; omega
  have hLane32 : lane / 8 % 8 < 4294967296 := by omega
  have hOffset32 : offset < 4294967296 := by omega
  have hRow32 : 128 * tile + offset < 4294967296 := by omega
  have hOffset64 : offset < 18446744073709551616 := by omega
  have hTile64 : 128 * tile < 18446744073709551616 := by omega
  have hRow64 : 128 * tile + offset < 18446744073709551616 := by omega
  intro t ht
  seg_fp ht using
    first
    | decide
    | norm_bits [hOffsetEq, hOr, ← hRow,
        Nat.mod_eq_of_lt hTile, Nat.mod_eq_of_lt hCol32, Nat.mod_eq_of_lt hLane32,
        Nat.mod_eq_of_lt hOffset32, Nat.mod_eq_of_lt hRow32, Nat.mod_eq_of_lt hRow64,
        Nat.mod_eq_of_lt hOffset64, Nat.mod_eq_of_lt hTile64]

def primingEntryInputs (p : Params) (l : Launch) (batch lane : Nat) :
    List (Nat × Value) :=
  [(108, .pred true), (1044, .bits 16 3), (1081, b32 (lane / 8 % 8)),
   (1082, b32 (kvCopyColumn lane false)), (7520, b64 1),
   (1086, b32 (p.kLength batch)), (7299, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride))),
   (7295, b64 (l.localBase + 96)), (7294, b64 (l.localBase + 64)),
   (7296, b64 16), (2535, b32 l.sharedBase)]

private theorem tripCountersTail {l : Launch} {g n upper lower : Nat}
    (hu : upper < 2 ^ 31) (hl : lower < 2 ^ 31) :
    Seg kernel [] l g 3 474 [(1088, b32 n), (1818, b32 upper), (1836, b32 lower)] 477
      [(1088, b32 n), (1837, b32 (min upper lower))] := by
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  have signed {x : Nat} (h : x < 2 ^ 31) : toSigned 32 (BitVec.ofNat 64 x) = (x : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show x < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega), ite_eq_left h]
  have hu32 : upper < 2 ^ 32 := by omega
  have hl32 : lower < 2 ^ 32 := by omega
  by_cases h : upper < lower
  · intro t ht
    seg_fp ht using simp only [hMin, b32, truncBits_ofNat hu32 (by decide),
      truncBits_ofNat hl32 (by decide), compare, kind_s_beq_s, Bool.false_eq_true,
      signed hu, signed hl, Int.ofNat_lt, h, decide_true, ↓reduceIte, min_eq_left h.le]
  · have hle : lower ≤ upper := by omega
    intro t ht
    seg_fp ht using simp only [hMin, b32, truncBits_ofNat hu32 (by decide),
      truncBits_ofNat hl32 (by decide), compare, kind_s_beq_s, Bool.false_eq_true,
      signed hu, signed hl, Int.ofNat_lt, h, decide_false, ↓reduceIte, min_eq_right hle]

private theorem loaderVisibleTripCheckpointCore {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch tile : Nat} (hb : batch < p.batch)
    (hTile : 256 * tile < p.qLength batch) {t : TState}
    (ht : At t 439 [(1801, b32 (256 * tile)), (1086, b32 (p.kLength batch)),
      (1085, b32 (2 ^ 32 - p.qLength batch))]) :
    ∃ u, run kernel [] l g 38 t = some u ∧ At u 477 [(1088, b32 (Mma.trips p batch tile))] := by
  obtain ⟨v, hv, hV⟩ := loaderVisibleTripsCore hp (g := g) hb hTile ht
  obtain ⟨_, hQuery, hKey⟩ := hp.lengths batch hb
  have hLower : (p.kLength batch - p.qLength batch +
      256 * tile + 128 + 127) / 128 < 2 ^ 31 := by omega
  obtain ⟨u, hu, hU⟩ := tripCountersTail (l := l) (g := g) (by omega) (by omega) v hV
  exact ⟨u, run_comp hv hu, hU.mono ⟨hU.2.2.2.2.1, trivial⟩⟩

/-- The visible-trip computation reaches the priming checkpoint by local steps. -/
theorem loaderVisibleTripCheckpoint {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch tile : Nat} (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {t : TState}
    (ht : At t 439 [(1801, b32 (256 * tile)), (1086, b32 (p.kLength batch)),
      (1085, b32 (2 ^ 32 - p.qLength batch))]) :
    ∃ u, run kernel Assumptions.all l g 38 t = some u ∧
      At u 477 [(1088, b32 (Mma.trips p batch tile))] := by
  obtain ⟨u, hu, hU⟩ := loaderVisibleTripCheckpointCore hp (g := g) hb hTile ht
  exact ⟨u, (loaderLinear (regs := []) (by decide) (by decide) ht.1 (by simp)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu).1, hU⟩

variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch tile lane : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
include hp hb hTile

/-- The checked trip count and swizzle operands enter the actual page scratch loop
without an intervening event. Both rows are bounded for the loop's signed compare. -/
theorem loaderPrimingScratchStartFrame {t : TState} {extra : List (Nat × Value)}
    (hTrip : ((kernel.code.drop 477).take 4).all
      (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hStart : ((kernel.code.drop 481).take 7).all
      (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (ht : At t 477 ((1088, b32 (Mma.trips p batch tile)) ::
      (primingEntryInputs p l batch lane ++ extra))) :
    let n := Mma.trips p batch tile - 1
    let base := primingLaneRow n lane
    128 * n + 127 < 2 ^ 31 ∧
      ∃ u, run kernel Assumptions.all l g 11 t = some u ∧
        At u 488 ((1091, b32 n) :: (primingScratchFacts p l batch base 0 ++
          (121, .pred true) :: (1092, b32 (128 * n)) :: (primingEntryInputs p l batch lane ++
      extra))) := by
  dsimp only
  let n := Mma.trips p batch tile - 1
  let base := primingLaneRow n lane
  let F := primingEntryInputs p l batch lane
  have hTrips := Mma.trips_bounds hp hb hTile
  have hCount := hTrips.2.1
  change Mma.trips p batch tile ≤ (p.kLength batch + 127) / 128 at hCount
  have hUpper : 128 * n < p.kLength batch := by
    have hPos := hTrips.1
    dsimp only [n]
    omega
  have hLen := (hp.lengths batch hb).2.2
  refine ⟨by omega, ?_⟩
  obtain ⟨v, hv, hV⟩ := loaderTripStartFull hp (g := g) hb hTile t
    (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  obtain ⟨hvA, hvFrame⟩ := loaderLinear (regs := (F ++
      extra).map Prod.fst) (by decide) (by decide) ht.1
    (primingKeepAppend (F := F) (G := extra) (pc := 477) (n := 4)
      (by set_option maxRecDepth 100000 in kernel_rfl) hTrip)
    (by set_option maxRecDepth 100000 in kernel_rfl) hv
  have hBefore : Holds v.regs (F ++ extra) := holdsSchedulerFrame ht.2.2.2.2.2 hvFrame
    (fun _ hm => List.mem_map_of_mem hm)
  have hFrame : Holds v.regs F := ((holds_append ..).mp hBefore).1
  have hArgs : At v 481
      [(108, .pred true), (1044, .bits 16 3), (1081, b32 (lane / 8 % 8)),
       (1082, b32 (kvCopyColumn lane false)), (1838, b32 (128 * n)), (7520, b64 1)] :=
    hV.mono ⟨hFrame.1, hFrame.2.1, hFrame.2.2.1, hFrame.2.2.2.1, hV.2.2.2.2.2.1,
      hFrame.2.2.2.2.1, trivial⟩
  obtain ⟨u, hu, hU⟩ := primingStartCore (by omega) v hArgs
  let G := (1091, b32 n) :: (121, .pred true) :: (1092, b32 (128 * n)) :: F
  obtain ⟨huA, huFrame⟩ := loaderLinear (regs := (G ++
      extra).map Prod.fst) (by decide) (by decide) hV.1
    (primingKeepAppend (F := G) (G := extra) (pc := 481) (n := 7)
      (by set_option maxRecDepth 100000 in kernel_rfl) hStart)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hLive : Holds u.regs (G ++ extra) := holdsSchedulerFrame
    ⟨hV.2.2.2.2.1, hV.2.2.2.2.2.2.1, hV.2.2.2.2.2.2.2.1, hBefore⟩
    huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hKeep : Holds u.regs F := ((holds_append ..).mp hLive.2.2.2).1
  have hNew := hU.2.2.2.2
  have hScratch : Holds u.regs (primingScratchFacts p l batch base 0) :=
    ⟨hNew.2.2.2.2.1, hNew.2.2.2.2.2.1, hNew.2.2.1, hNew.2.2.2.1,
      hNew.1, hNew.2.1, hKeep.2.2.2.2.2.1, hKeep.2.2.2.2.2.2⟩
  exact ⟨u, run_comp hvA huA, hU.mono ⟨hLive.1, (holds_append ..).mpr ⟨hScratch, hLive.2⟩⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
