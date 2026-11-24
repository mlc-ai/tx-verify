-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKFromScratch
public import Kernels.TmlFa4Fwd.Proof.LoaderWalkCheckpoint
public import Kernels.TmlFa4Fwd.Proof.LoaderAddressPrelude

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue

noncomputable section

/-- Register facts carried from the resolved ABI and lane swizzle. -/
def primingKTripCarry (p : Params) (l : Launch) (head warp lane : Nat) : List (Nat × Value) :=
  let tid := 32 * warp + lane
  [(1062, b32 (tid / 32)), (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
   (7495, b64 p.kLayout.pageStride), (7493, b64 p.kLayout.rowStride),
   (7300, b64 (p.kLayout.base + 2 * (head * p.kLayout.headStride))), (7292, b64 l.localBase)]

def primingKTripFacts (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  (1088, b32 (Mma.trips p batch tile)) :: (primingEntryInputs p l batch (32 * warp + lane) ++
    primingKTripCarry p l head warp lane)

def primingKVisibleFacts (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  [(1801, b32 (256 * tile)), (1086, b32 (p.kLength batch)),
   (1085, b32 (2 ^ 32 - p.qLength batch))] ++
    (primingEntryInputs p l batch (32 * warp + lane) ++ primingKTripCarry p l head warp lane)

/-- Preserve ABI and swizzle facts when the actual visible-trip arithmetic runs. -/
theorem primingKTripSeedLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {s : TState} (hs : At s 439 (primingKVisibleFacts p l batch head tile warp lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
        At u 477 (primingKTripFacts p l batch head tile warp lane) := by
  let F := primingEntryInputs p l batch (32 * warp + lane) ++ primingKTripCarry p l head warp lane
  obtain ⟨u, hu, hU⟩ := loaderVisibleTripCheckpoint hp hb hTile (hs.mono
    ((holds_append ..).mp hs.2.2.2.2).1)
  obtain ⟨_, hFrame⟩ := loaderSegmentFrame (regs := F.map Prod.fst) (lower := 439) (stop := 477)
    (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) hu
    (by rw [hs.1]) (by rw [hs.1])
  have hHeld := holdsSchedulerFrame ((holds_append ..).mp hs.2.2.2.2).2 hFrame
    (fun _ hm => List.mem_map_of_mem hm)
  exact ⟨u, run_rtg hu, hU.mono ⟨hU.2.2.2.2.1, hHeld⟩⟩

/-- The decoded trip seed sets the row selector for the last visible KV tile. -/
theorem primingKEnterScratchLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    {s : TState} (hs : At s 477 (primingKTripFacts p l batch head tile warp lane)) :
    128 * (Mma.trips p batch tile - 1) + 127 < 2 ^ 31 ∧
      ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
        At u 488 (primingKInitialScratchFacts p l batch head
          (Mma.trips p batch tile - 1) warp lane) := by
  have hTrips := Mma.trips_bounds hp hb hTile
  have hCount := hTrips.2.1
  have hLen := (hp.lengths batch hb).2.2
  change Mma.trips p batch tile ≤ (p.kLength batch + 127) / 128 at hCount
  refine ⟨by omega, ?_⟩
  obtain ⟨_, u, hu, hU⟩ := loaderPrimingScratchStartFrame hp hb hTile
    (extra := primingKTripCarry p l head warp lane)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    hs
  refine ⟨u, run_rtg hu, hU.mono ((holds_append ..).mpr ⟨?_, ?_⟩)⟩
  · exact ((holds_append ..).mp hU.2.2.2.2.2).1
  · simp only [primingKPackFrame, primingKMaskInputs, List.cons_append, List.nil_append, Holds]
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup hU.2.2.2.2; rfl)

/-- The actual selected tile's trip and swizzle inputs are live during K/V address arithmetic. -/
def primingKAddressCarry (p : Params) (l : Launch) (batch tile warp lane : Nat) :
    List (Nat × Value) :=
  let tid := 32 * warp + lane
  [(1801, b32 (256 * tile)), (1086, b32 (p.kLength batch)),
   (1085, b32 (2 ^ 32 - p.qLength batch)),
   (7294, b64 (l.localBase + 64)), (7295, b64 (l.localBase + 96)), (2535, b32 l.sharedBase),
   (7296, b64 16), (1081, b32 (tid / 8 % 8)), (1082, b32 (kvCopyColumn tid false)),
   (1062, b32 (tid / 32)), (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false)),
   (7495, b64 p.kLayout.pageStride), (7493, b64 p.kLayout.rowStride),
   (7292, b64 l.localBase), (7497, b64 p.vLayout.rowStride),
   (7499, b64 p.vLayout.pageStride), (1087, b32 (p.qOffset batch + 256 * tile))]

def primingKAddressFacts (p : Params) (l : Launch) (batch head tile warp lane : Nat) :
    List (Nat × Value) :=
  addressPreludeInputs p batch head ++ addressCacheInputs p ++
    primingKAddressCarry p l batch tile warp lane

/-- The decoded address prelude sets the selected batch's page-table base and
the K pointer base for the selected Q head's KV group. -/
theorem primingKAddressToVisibleLane {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g batch head tile warp lane : Nat}
    (hb : batch < p.batch) (hh : head < 2 ^ 31) (hTile : 256 * tile < p.qLength batch)
    {s : TState} (hs : At s 415 (primingKAddressFacts p l batch head tile warp lane)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
        At u 439 (primingKVisibleFacts p l batch (head / 6) tile warp lane) := by
  obtain ⟨u, hu, hU⟩ := loaderAddressPreludeRun hp hb hh hTile
    (F := primingKAddressCarry p l batch tile warp lane)
    (by set_option maxRecDepth 100000 in kernel_rfl) hs
  refine ⟨u, run_rtg hu, hU.mono ?_⟩
  simp only [primingKVisibleFacts, primingEntryInputs, primingKTripCarry, List.cons_append,
    List.nil_append, Holds]
  repeat' apply And.intro
  all_goals first | trivial | (apply holds_lookup hU.2.2.2.2; rfl)

end
end PTX.Kernels.TmlFa4Fwd.Loader
