-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPackProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerReloadProgress
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKReload
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The first K request's saved row pointer in each physical loader lane. -/
def primingKeyLaneBase (p : Params) (batch head tile warp lane : Nat) : Nat :=
  primingKRowPointer p batch head (primingLaneRow tile (32*warp+lane))

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch head tile shuffles votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hh : head < p.kvHeads) (hTile : 128*tile+7 < 2^31)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 538
      (primingKMaskInputs p l batch tile (warpIndex l g)) shuffles votes ends)
    (hSaved : ∀ lane < 32,
      let thread := warpLane l g lane
      PrimingCellValue X thread (cur.pos lane) 534 (sourceScratchAccess l thread 0)
        (b64 (primingKeyLaneBase p batch head tile (warpIndex l g) lane)).toBytes)
include hp hMax hg hb hh hTile cur hSaved

/-- Both actual vector-load elements of the first K pointer reach the broadcast frame. -/
theorem primingKeyFirstPointerReloadWithEvents :
    ∃ _done : SchedulerWarpReached l X g 544
      (primingKSourceInputs p l batch tile (warpIndex l g)
        (primingKeyLaneBase p batch head tile (warpIndex l g))) shuffles votes ends,
      ∀ lane < 32,
        let thread := warpLane l g lane
        let base := primingKeyLaneBase p batch head tile (warpIndex l g) lane
        X.get (thread,cur.pos lane) = some ⟨543,
          .rd (primingKPointerReload.word thread l.localBase 0) (pointerReadBytes base 0)⟩ := by
  let bases := primingKeyLaneBase p batch head tile (warpIndex l g)
  let F := primingKSourceFrame p l batch tile (warpIndex l g)
  let site := primingKPointerReload
  obtain ⟨start,hPos,hBefore⟩ := cur.toSchedulerWarpAt.advanceLocalPreserving
    (pc' := 543) (G := F) (fun lane hl => primingKMaskDecode hp hb hTile (cur.checkpoint lane hl))
  let ready := cur.reframe start hPos hBefore
  have hLocal := hp.localMemory.2.1
  have hAlign := hp.localMemory.1
  have hBase (lane : Nat) (_ : lane < 32) : bases lane < 2^64 := by
    let row := primingLaneRow tile (32*warpIndex l g+lane)
    have hPage := primingScratchPageBound hp (row := row) hb
    obtain ⟨hAddrEq,hAddr,_⟩ := sourceScratchPayload_live hp 0 hPage (Nat.mod_lt row (by decide)) hh
    rw [hAddrEq] at hAddr
    exact hAddr
  obtain ⟨done,hRead⟩ := site.warpReadOfMaximal hp hMax hg (addr := l.localBase) (store := 534)
    (by decide) Flow.code_543 (by change l.localBase+0 < 2^64; omega)
    (by change (l.localBase+0)%8 = 0; omega) (by decide) bases hBase ready
    (fun _ _ => by simp [F,site,primingKPointerReload,primingKSourceFrame])
    (fun _ _ => by simp [F,site,primingKPointerReload,primingKSourceFrame])
    (fun lane hl => by
      change PrimingCellValue X (warpLane l g lane) (start.pos lane) 534 _ _
      rw [hPos]
      exact hSaved lane hl)
  refine ⟨done,fun lane hl => ?_⟩
  rw [← hPos]
  exact hRead lane hl

end

/-- The actual broadcast frame at the entry to first key copy preparation. -/
abbrev PrimingKeyBroadcastReady (p : Params) (l : Launch) (X : Execution)
    (g batch tile warp shuffles votes : Nat) (bases : Nat → Nat) (ends : Nat → Option TState) :=
  SchedulerWarpReached l X g 546 (fun lane =>
    [(1855,b32 (bases (pointerBroadcastLane lane)%2^32)),
     (1856,b32 (bases (pointerBroadcastLane lane)/2^32))] ++
      primingKSourceInputs p l batch tile warp bases lane) shuffles votes ends

/-- A maximal loader warp records both halves of the real K row pointer broadcast. -/
theorem primingKeyBroadcastOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes : Nat} (hg : g < l.threads) (bases : Nat → Nat)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 544
      (primingKSourceInputs p l batch tile warp bases)
      shuffles votes ends) :
    Nonempty (PrimingKeyBroadcastReady p l X g batch tile warp (shuffles+2) votes bases ends) := by
  have hFresh0 (lane : Nat) (_ : lane < 32) : ∀ pair ∈
      primingKSourceInputs p l batch tile warp bases lane, pair.1 ≠ primingKShflDst 0 := by
    simp [primingKSourceInputs, primingKSourceFrame, primingKShflDst]
  have hOut0 (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (cur.state lane) = .ev
        (.shfl .idx (b32 (bases lane % 2 ^ 32)) 0 6175
          (fun v _ => next (setReg (cur.state lane) (primingKShflDst 0) v))) :=
    primingKShuffleTemplate (by rw [hp.block]) 0 (cur.checkpoint lane hl)
      (cur.checkpoint lane hl).2.2.2.2.1
  obtain ⟨first⟩ := cur.consumeShuffle hp hMax hg .idx (fun lane => b32 (bases lane % 2 ^ 32))
    (fun _ => 0) (fun _ => 6175) hFresh0 hOut0
  have hFresh1 (lane : Nat) (_ : lane < 32) :
      ∀ pair ∈ (primingKShflDst 0, b32 (bases (shflSource .idx lane 0 6175).1 % 2 ^ 32)) ::
        primingKSourceInputs p l batch tile warp bases lane, pair.1 ≠ primingKShflDst 1 := by
    simp [primingKSourceInputs, primingKSourceFrame, primingKShflDst]
  have hOut1 (lane : Nat) (hl : lane < 32) :
      out kernel Assumptions.all l (warpLane l g lane) (first.state lane) = .ev
        (.shfl .idx (b32 (bases lane / 2 ^ 32)) 0 6175
          (fun v _ => next (setReg (first.state lane) (primingKShflDst 1) v))) :=
    primingKShuffleTemplate (by rw [hp.block]) 1 (first.checkpoint lane hl)
      (first.checkpoint lane hl).2.2.2.2.2.2.1
  obtain ⟨second⟩ := first.consumeShuffle hp hMax hg .idx (fun lane => b32 (bases lane / 2 ^ 32))
    (fun _ => 0) (fun _ => 6175) hFresh1 hOut1
  apply second.advanceLocal
  intro lane hl
  refine ⟨second.state lane, .refl, ?_⟩
  have ht := second.checkpoint lane hl
  have hSrc : (shflSource .idx lane 0 6175).1 = pointerBroadcastLane lane :=
    congrArg Prod.fst (kv_shuffle_source ⟨lane, hl⟩ 0)
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ?_⟩
  exact ⟨by simpa [hSrc, primingKShflDst] using ht.2.2.2.2.2.1,
    by simpa [hSrc, primingKShflDst] using ht.2.2.2.2.1, ht.2.2.2.2.2.2⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
