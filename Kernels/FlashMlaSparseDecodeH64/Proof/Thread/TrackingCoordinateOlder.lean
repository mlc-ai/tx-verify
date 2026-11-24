-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateRf
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingRoleGeometry

public section

/-! # Earlier coordinate writes are hidden by the current published word -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.MbarRing Protocol Protocol.IndexRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem thread_eq_of_warp_lane (hpre : Pre P L mem0) {h w : Nat}
    (hCta : ctaOf L h = ctaOf L w) (hWarp : warpOf L h = warpOf L w)
    (hLane : laneOf L h = laneOf L w) : h = w := by
  have hA := Nat.div_add_mod (tidOf L h) 32
  have hB := Nat.div_add_mod (tidOf L w) 32
  unfold warpOf at hWarp
  unfold laneOf at hLane
  have hTid : tidOf L h = tidOf L w := by omega
  rw [tidOf_eq hpre, tidOf_eq hpre, ← hpre.block] at hTid
  unfold ctaOf at hCta
  have ha := Nat.div_add_mod h L.block
  have hb := Nat.div_add_mod w L.block
  rw [hCta, hTid] at ha
  exact ha.symm.trans hb

/-- An actual earlier-generation coordinate write is hidden by the visible current publication.
The overlapping byte identifies the same lane and slot even without execution-wide tracking. -/
theorem coordinate_older_source_before {g i h t w u : Nat}
    {d : Wg1Tma.D} {z current : Wg1Index.D} {e f : Event} {k : Fin 16} {j : Fin 4}
    {a source target : Acc} {bs : List (Option Byte)} {raw bytes : List Byte}
    {offset : Nat} {extra high extra' high' : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j) (hRead : e.kind = .rd a bs)
    (hf : X.get (h, t) = some f) (hKind : f.kind = .wr source raw)
    (hState : Frame.stateAt (Machine.code P L) X h t = some (some (.index z)))
    (hSource : z.site = .coord extra high)
    (hWr : X.Writes (w, u) target bytes)
    (hCurrent : Frame.stateAt (Machine.code P L) X w u = some (some (.index current)))
    (hTarget : current.site = .coord extra' high') (hBlock : current.block = d.block)
    (hOlder : z.block / 4 < d.block / 4)
    (hLoc : a.loc = target.loc) (hWidth : target.size = 4)
    (hOffset : offset < 4) (hCover : source.Covers (a.loc.at offset)) :
    ByteCausality L X (a.loc.at offset) (.thread (h, t)) (.thread (w, u)) := by
  obtain ⟨_, hCta, hSlot, hLane, _, _⟩ :=
    coordinate_source_geometry hpre hX hs he hd hSite hf hState hSource
      hRead hKind hOffset hCover
  have hTargetCover : target.Covers (a.loc.at offset) := by
    rw [hLoc]
    exact Acc.covers_at (by rw [hWidth]; exact hOffset)
  obtain ⟨tag, hGet⟩ := hWr
  obtain ⟨_, hCta', _, hLane', _, _⟩ :=
    coordinate_source_geometry hpre hX hs he hd hSite hGet hCurrent hTarget
      hRead rfl hOffset hTargetCover
  have hh := Frame.lt_of_get hX hf
  have hw := Frame.lt_of_get hX hGet
  have hWarp := RingRoleGeometry.of_trace hX hh (hs h hh).machine hState
  have hWarp' := RingRoleGeometry.of_trace hX hw (hs w hw).machine hCurrent
  change warpOf L h = 7 at hWarp
  change warpOf L w = 7 at hWarp'
  have hEq := thread_eq_of_warp_lane hpre (hCta.symm.trans hCta')
    (hWarp.trans hWarp'.symm) (hLane.trans hLane'.symm)
  subst w
  have hA := (IndexRingTrace.composed_write_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hState (.inl ⟨extra, high, hSource⟩)).1
  have hB := (IndexRingTrace.composed_write_counts hpre
    ((hs h hh).machine.produces (hX.thr h hh)) hCurrent
    (.inl ⟨extra', high', hTarget⟩)).1
  rw [hSlot] at hA
  rw [hBlock] at hB
  rw [← hB, ← hA] at hOlder
  exact .direct (.inl (IndexTma.prior_coordinate_write hf hGet hKind hOlder))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
