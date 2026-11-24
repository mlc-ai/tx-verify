-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKActive
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVScratch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The signed difference between the lower-stage and upper-stage trip counts. -/
def vPrimingResidual (p : Params) (batch tile : Nat) : Nat :=
  (min ((p.kLength batch + 127) / 128)
      ((p.kLength batch - p.qLength batch + 256 * tile + 128 + 127) / 128) +
    2 ^ 32 - Mma.trips p batch tile) % 2 ^ 32

private theorem primingVTripTail {l : Launch} {g upper lower n : Nat}
    (hu : upper < 2 ^ 31) (hl : lower < 2 ^ 31) (hn : n < 2 ^ 31) :
    Seg kernel [] l g 3 474 [(1088, b32 n), (1818, b32 upper), (1836, b32 lower)]
      477 [(1088, b32 n), (1089, b32 ((min upper lower + 2 ^ 32 - n) % 2 ^ 32)),
        (1090, b32 (min upper lower - n))] := by
  have hMin : (IntOp.min false == IntOp.max false) = false := rfl
  have hu32 : upper < 2 ^ 32 := by omega
  have hl32 : lower < 2 ^ 32 := by omega
  have hWord (a : Nat) (ha : a < 2 ^ 32) :
      truncBits 32 (BitVec.ofNat 64 a - truncBits 32 (BitVec.ofNat 64 n)) =
        BitVec.ofNat 64 ((a + 2 ^ 32 - n) % 2 ^ 32) := by
    rw [truncBits_ofNat (show n < 2 ^ 32 by omega) (by decide)]
    apply BitVec.eq_of_toNat_eq
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_sub]
    omega
  have hMax : (IntOp.max false == IntOp.max false) = true := rfl
  have hClamp (x : Nat) (hx : x < 2 ^ 31) :
      let residual := truncBits 32 (BitVec.ofNat 64 ((x + 2 ^ 32 - n) % 2 ^ 32))
      (if 0 < toSigned 32 residual then residual else truncBits 32 (BitVec.ofInt 64 0)) =
        BitVec.ofNat 64 (x - n) := by
    dsimp only
    rw [truncBits_ofNat (Nat.mod_lt _ (by decide)) (by decide)]
    rcases Nat.lt_trichotomy n x with hPos | rfl | hNeg
    · have hResid : (x + 2 ^ 32 - n) % 2 ^ 32 = x - n := by omega
      have hs : x - n < 2 ^ 31 := by omega
      rw [hResid, int32Signed hs, ite_eq_left (by omega)]
    · have hResid : (n + 2 ^ 32 - n) % 2 ^ 32 = 0 := by omega
      rw [hResid, Nat.sub_self]
      rfl
    · let word := x + 2 ^ 32 - n
      have hResid : (x + 2 ^ 32 - n) % 2 ^ 32 = word := by dsimp [word]; omega
      have h32 : word < 2 ^ 32 := by dsimp [word]; omega
      have hHigh : ¬ word < 2 ^ 31 := by dsimp [word]; omega
      have hs : toSigned 32 (BitVec.ofNat 64 word) = (word : Int) - 2 ^ 32 := by
        simp only [toSigned, toNat_ofNat_lt (by omega : word < 2 ^ 64),
          Nat.mod_eq_of_lt h32, ite_eq_right hHigh]
      rw [hResid, hs, ite_eq_right (by omega), Nat.sub_eq_zero_of_le hNeg.le]
      rfl
  by_cases h : upper < lower
  · intro t ht
    seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat hu32 (by decide), truncBits_ofNat hl32 (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hu, int32Signed hl,
        Int.ofNat_lt, h, decide_true, ↓reduceIte, min_eq_left h.le, hWord upper hu32,
        hMax, decide_eq_true_eq, show toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 by rfl,
        hClamp upper hu]
  · have hle : lower ≤ upper := by omega
    intro t ht
    seg_fp ht using
      simp only [hMin, b32, truncBits_ofNat hu32 (by decide), truncBits_ofNat hl32 (by decide),
        compare, kind_s_beq_s, Bool.false_eq_true, int32Signed hu, int32Signed hl,
        Int.ofNat_lt, h, decide_false, ↓reduceIte, min_eq_right hle, hWord lower hl32,
        hMax, decide_eq_true_eq, show toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 by rfl,
        hClamp lower hl]

/-- Facts needed by the V packet that are available before the actual K metadata loop. -/
def primingVAdmissionCarry (p : Params) (l : Launch) (batch queryHead queryTile : Nat) :
    List (Nat × Value) :=
  [(1089, b32 (vPrimingResidual p batch queryTile)), (2535, b32 l.sharedBase),
   (7295, b64 (l.localBase + 96))] ++ primingVScratchAbi p l (queryHead / 6)

/-- The selected request's live trip counters, loader role and first Bias coordinates. -/
def primingVTripFrame (p : Params) (batch tile head warp : Nat) : List (Nat × Value) :=
  [(1088, b32 (Mma.trips p batch tile)), (1091, b32 (Mma.trips p batch tile - 1)),
   (1062, b32 warp), (1087, b32 (p.qOffset batch + 256 * tile)), (7169, b32 head),
   (1090, b32 0)]

private def primingVAdmissionFrame (p : Params) (l : Launch)
    (batch head tile warp lane : Nat) : List (Nat × Value) :=
  (1088, b32 (Mma.trips p batch tile)) :: (1090, b32 0) ::
    (primingKTripCarry p l (head / 6) warp lane ++
      primingVAdmissionCarry p l batch head tile ++
      [(1087, b32 (p.qOffset batch + 256 * tile)), (7169, b32 head)])

section
variable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hh : head < 2 ^ 31) (hTile : 256 * tile < p.qLength batch)
include hp hb hh hTile

set_option maxRecDepth 10000 in
private theorem primingVAdmissionToTripTail {s : TState} {G : List (Nat × Value)}
    (hAddressFrame : ((kernel.code.drop 415).take (439 - 415)).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTripFrame : ((kernel.code.drop 439).take (474 - 439)).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTailFrame : ((kernel.code.drop 474).take 3).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 415 (primingKAddressFacts p l batch head tile warp lane ++ G)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t 477 ((1088, b32 (Mma.trips p batch tile)) ::
        (primingEntryInputs p l batch (32 * warp + lane) ++
          (primingVAdmissionFrame p l batch head tile warp lane ++ G))) := by
  have hTrips := Mma.trips_bounds hp hb hTile
  have hCount := hTrips.2.1
  have hLen := (hp.lengths batch hb).2.2
  change Mma.trips p batch tile ≤ (p.kLength batch + 127) / 128 at hCount
  have hLower : (p.kLength batch - p.qLength batch + 256 * tile + 128 + 127) / 128 < 2 ^ 31 := by
    have := (hp.lengths batch hb).2.1
    omega
  let tid := 32 * warp + lane
  let coordinates := [(1087, b32 (p.qOffset batch + 256 * tile)), (7169, b32 head)]
  let F := (primingEntryInputs p l batch tid ++ primingKTripCarry p l (head / 6) warp lane) ++
    primingVScratchAbi p l (head / 6) ++ coordinates
  let addressCarry := (7169, b32 head) :: primingKAddressCarry p l batch tile warp lane
  have ⟨hsCore, hsG⟩ := (holds_append ..).mp hs.2.2.2.2
  have hAddressKeep : ((kernel.code.drop 415).take (439 - 415)).all
      (fun ins => ((addressCarry ++ G).map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true := by
    rw [List.map_append]
    apply List.all_eq_true.mpr
    intro ins hm
    rw [List.all_append, Bool.and_eq_true]
    refine ⟨?_, List.all_eq_true.mp hAddressFrame ins hm⟩
    have hTab : ((kernel.code.drop 415).take (439 - 415)).all
        (fun i => (addressCarry.map Prod.fst).all (fun r => !(writesRegs i.op).contains r)) =
        true := by
      set_option maxRecDepth 100000 in kernel_rfl
    exact List.all_eq_true.mp hTab ins hm
  have hSeed : At s 415
      (addressPreludeInputs p batch head ++ addressCacheInputs p ++ (addressCarry ++ G)) := by
    obtain ⟨hPrelude, hCarry⟩ := (holds_append ..).mp hsCore
    apply hs.mono
    exact (holds_append ..).mpr ⟨hPrelude, (holds_append ..).mpr
      ⟨⟨holds_lookup hsCore rfl, hCarry⟩, hsG⟩⟩
  obtain ⟨a, ha, hA⟩ := loaderAddressPreludeRun hp hb hh hTile
    (F := addressCarry ++ G) hAddressKeep hSeed
  have haCore : Holds a.regs (addressPreludeOutputs p batch head ++ addressCarry) := by
    have held := hA.2.2.2.2
    rw [← List.append_assoc] at held
    exact ((holds_append ..).mp held).1
  have haG : Holds a.regs G := by
    have held := hA.2.2.2.2
    rw [← List.append_assoc] at held
    exact ((holds_append ..).mp held).2
  have hf : Holds a.regs F := by
    simp only [F, primingEntryInputs, primingKTripCarry, primingVScratchAbi, coordinates,
      List.cons_append,
      List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup haCore; rfl)
  obtain ⟨b, hbRun, hB⟩ := loaderVisibleTripsCore hp (g := g) hb hTile (hA.mono (by
    exact ⟨holds_lookup haCore rfl, holds_lookup haCore rfl,
      holds_lookup haCore rfl, trivial⟩))
  obtain ⟨hbA, hBRegs⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hA.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hbRun
  have hBF : Holds b.regs F := holdsSchedulerFrame hf hBRegs (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨c, hc, hC⟩ := primingVTripTail (l := l) (g := g) (by omega) hLower
    (by omega) b hB
  obtain ⟨hcA, hCRegs⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hB.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hc
  have hCF := holdsSchedulerFrame hBF hCRegs (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨_, frameB⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hA.1
    hTripFrame (by set_option maxRecDepth 100000 in kernel_rfl) hbRun
  have hGB := holdsSchedulerFrame haG frameB (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨_, frameC⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hB.1
    hTailFrame (by decide) hc
  have hGC := holdsSchedulerFrame hGB frameC (fun _ hm => List.mem_map_of_mem hm)
  let extra := primingVAdmissionFrame p l batch head tile warp lane
  have hZero :
      min ((p.kLength batch + 127) / 128)
        ((p.kLength batch - p.qLength batch + 256 * tile + 128 + 127) / 128) -
        Mma.trips p batch tile = 0 := by
    unfold Mma.trips
    omega
  have hStart : At c 477 ((1088, b32 (Mma.trips p batch tile)) ::
      (primingEntryInputs p l batch tid ++ (extra ++ G))) := by
    apply hC.mono
    refine ⟨hC.2.2.2.2.1, ?_⟩
    obtain ⟨hCore, hCoords⟩ := (holds_append ..).mp hCF
    obtain ⟨hBoth, hV⟩ := (holds_append ..).mp hCore
    obtain ⟨hArgs, hK⟩ := (holds_append ..).mp hBoth
    have hBase : Holds c.regs extra :=
      ⟨hC.2.2.2.2.1, hZero ▸ hC.2.2.2.2.2.2.1,
        (holds_append ..).mpr ⟨(holds_append ..).mpr
          ⟨hK, hC.2.2.2.2.2.1, holds_lookup hArgs rfl, holds_lookup hArgs rfl, hV⟩, hCoords⟩⟩
    exact (holds_append ..).mpr ⟨hArgs, (holds_append ..).mpr ⟨hBase, hGC⟩⟩
  exact ⟨c, run_rtg (run_comp (run_comp ha hbA) hcA), hStart⟩

set_option maxRecDepth 10000 in
/-- Actual K/V address and trip arithmetic from a lane at its address checkpoint. -/
theorem primingVAdmissionWithTripsLaneExtra (hl : lane < 32) {s : TState} {G : List (Nat × Value)}
    (hAddressFrame : ((kernel.code.drop 415).take (439 - 415)).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTripFrame : ((kernel.code.drop 439).take (474 - 439)).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hTailFrame : ((kernel.code.drop 474).take 3).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hSeedFrame : ((kernel.code.drop 477).take 4).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hScratchFrame : ((kernel.code.drop 481).take 7).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hs : At s 415 (primingKAddressFacts p l batch head tile warp lane ++ G)) :
    let keyTile := Mma.trips p batch tile - 1
    128 * keyTile + 127 < 2 ^ 31 ∧
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 488 (primingKInitialScratchFacts p l batch (head / 6) keyTile warp lane ++
        primingVAdmissionCarry p l batch head tile ++
        primingVTripFrame p batch tile head warp ++ G) := by
  dsimp only
  let tid := 32 * warp + lane
  let extra := primingVAdmissionFrame p l batch head tile warp lane
  have hTrips := Mma.trips_bounds hp hb hTile
  have hLen := (hp.lengths batch hb).2.2
  have hCount : Mma.trips p batch tile ≤ (p.kLength batch + 127) / 128 := hTrips.2.1
  refine ⟨by omega, ?_⟩
  obtain ⟨c, hRun, hStart⟩ :=
    primingVAdmissionToTripTail hp (g := g) hb hh hTile hAddressFrame hTripFrame hTailFrame hs
  have hAppend {start count : Nat}
      (hCore : ((kernel.code.drop start).take count).all
        (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
      (hG : ((kernel.code.drop start).take count).all
        (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true) :
      ((kernel.code.drop start).take count).all
        (fun ins => ((extra ++ G).map Prod.fst).all
          (fun r => !(writesRegs ins.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro ins hm
    simp only [List.map_append, List.all_append, Bool.and_eq_true]
    exact ⟨List.all_eq_true.mp hCore ins hm, List.all_eq_true.mp hG ins hm⟩
  obtain ⟨_, u, hu, hU⟩ := loaderPrimingScratchStartFrame hp hb hTile
    (extra := extra ++ G) (hAppend (by set_option maxRecDepth 100000 in kernel_rfl) hSeedFrame)
    (hAppend (by set_option maxRecDepth 100000 in kernel_rfl) hScratchFrame) hStart
  have hWarp : tid / 32 = warp := by dsimp [tid]; omega
  refine ⟨u, hRun.trans (run_rtg hu), hU.mono ?_⟩
  have huG : Holds u.regs G := by
    obtain ⟨_, tail⟩ := (holds_append ..).mp hU.2.2.2.2.2
    obtain ⟨_, extraFrame⟩ := (holds_append ..).mp tail.2.2
    exact ((holds_append ..).mp extraFrame).2
  apply (holds_append ..).mpr
  refine ⟨?_, huG⟩
  simp only [primingKInitialScratchFacts, primingKPackFrame, primingKMaskInputs,
    primingScratchFacts, primingVAdmissionCarry, primingVScratchAbi, primingVTripFrame,
    List.cons_append, List.nil_append, Holds]
  repeat' apply And.intro
  all_goals first
    | trivial
    | (apply holds_lookup hU.2.2.2.2; rfl)
    | (rw [← hWarp]; apply holds_lookup hU.2.2.2.2; rfl)

/-- Actual K/V address and trip arithmetic from a lane at its address checkpoint. -/
theorem primingVAdmissionWithTripsLane (hl : lane < 32) {s : TState}
    (hs : At s 415 (primingKAddressFacts p l batch head tile warp lane)) :
    let keyTile := Mma.trips p batch tile - 1
    128 * keyTile + 127 < 2 ^ 31 ∧
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 488 (primingKInitialScratchFacts p l batch (head / 6) keyTile warp lane ++
        primingVAdmissionCarry p l batch head tile ++
        primingVTripFrame p batch tile head warp) :=
  primingVAdmissionWithTripsLaneExtra hp hb hh hTile hl (G := [])
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simpa only [List.append_nil] using hs)
end

/-- The actual K/V address and trip arithmetic retain the runtime V ABI at priming scratch entry. -/
theorem primingVAdmissionWithTripsFromAddresses {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch head tile warp shuffles votes : Nat}
    (hb : batch < p.batch) (hh : head < 2 ^ 31) (hTile : 256 * tile < p.qLength batch)
    (cur : SchedulerWarpAt l X g 415 (primingKAddressFacts p l batch head tile warp)
      shuffles votes) :
    let keyTile := Mma.trips p batch tile - 1
    128 * keyTile + 127 < 2 ^ 31 ∧
    Nonempty (SchedulerWarpAt l X g 488 (fun lane =>
      primingKInitialScratchFacts p l batch (head / 6) keyTile warp lane ++
        primingVAdmissionCarry p l batch head tile ++ primingVTripFrame p batch tile head warp)
      shuffles votes) := by
  dsimp only
  refine ⟨(primingVAdmissionWithTripsLane hp hb hh hTile (g := warpLane l g 0)
    (by decide : 0 < 32) (cur.checkpoint 0 (by decide))).1, cur.advanceLocal ?_⟩
  intro lane hl
  exact (primingVAdmissionWithTripsLane hp hb hh hTile (g := warpLane l g lane)
    hl (cur.checkpoint lane hl)).2

/-- The active loader's actual selected coordinates reach the K metadata loop with the
V page and row strides, GQA head base, and the retained lower-stage count difference. -/
theorem actualPrimingVAdmissionWithTrips {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (hActive : g / l.block < tilePrefix p p.batch * p.heads)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      head < p.kvHeads ∧ 128 * tile + 127 < 2 ^ 31 ∧
      ∃ shuffles votes, Nonempty (SchedulerWarpAt l X g 488
        (fun lane =>
          primingKInitialScratchFacts p l batch head tile (Prologue.warpIndex l g) lane ++
          primingVAdmissionCarry p l batch coords.2 coords.1 ++
          primingVTripFrame p batch coords.1 coords.2 (Prologue.warpIndex l g))
        shuffles votes) := by
  rcases loaderSchedule hp hX hComplete hg hWarp writes with
    ⟨hBad, _⟩ | ⟨first, batch, _, hf, hGroup, hb, hLo, hHi, ⟨selected⟩⟩
  · omega
  obtain ⟨prep⟩ := loaderSelectedPrefix hp hX hg hf hGroup hb selected
  obtain ⟨coord⟩ := loaderSelectedCoordinates hp hX hg hf hGroup hb hLo hHi prep
  obtain ⟨ready⟩ := primingKActiveEntryFromCoordinates hp hb hLo hHi coord
  let coords := assignedCoordinates p batch (g / l.block)
  have ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hHeadSigned := hHead.trans hp.heads_signed
  have hKV : coords.2 / 6 < p.kvHeads := by
    change coords.2 < p.heads at hHead
    unfold Params.heads at hHead
    omega
  obtain ⟨active⟩ := primingKActiveMetadataFromTrace hp hX hg hb hTile writes ready
  obtain ⟨addresses⟩ := primingKActiveToAddress hp hb hTile active
  obtain ⟨hKey, hScratch⟩ :=
    primingVAdmissionWithTripsFromAddresses hp hb hHeadSigned hTile addresses
  exact ⟨batch, hb, hLo, hHi, hKV, hKey, _, _, hScratch⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
