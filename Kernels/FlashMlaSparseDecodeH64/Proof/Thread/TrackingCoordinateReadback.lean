-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateFuture
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingCoordinateOlder
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.WriteExclusions

@[expose] public section

/-! # Readback of a coordinate word once its byte sources are classified -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.AsyncCopy PTX.Proof

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A coordinate read returns the published word when its covering writes are known to be index
stores. Earlier uses are hidden by the current publication and later uses follow the read. -/
theorem coordinate_value_of_index_writes {g i : Nat} {d : Wg1Tma.D}
    {e : Event} {k : Fin 16} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ a < L.threads, (Machine.code P L a).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .coord k j)
    (hCovering : ∀ {a bs source fp raw b}, e.kind = .rd a bs → b < 4 →
      X.MemWrites source fp raw → fp.Covers (a.loc.at b) →
      ∃ h t f z extra high, source = .thread (h, t) ∧
        X.get (h, t) = some f ∧ f.kind = .wr fp raw ∧
        Frame.stateAt (Machine.code P L) X h t = some (some (.index z)) ∧
        z.site = .coord extra high) :
    ∃ a bs, e.kind = .rd a bs ∧
      rebuild 3 bs = .ok (b32 (Wg1Tma.coordAt P L g d.block (Wg1Tma.coordPos k.val j.val))) := by
  obtain ⟨a, bs, w, aw, hRead, hSize, hLoc, hWidth, hWrite, hBefore, current, ext, hi, hw, hCur,
    hBlock⟩ := coordinate_publication_with_writer hpre hX hs he hd hSite
  have hOrdinary : X.Writes w aw _ :=
    hWrite.resolve_right (fun ⟨_, hr⟩ => GlobalWrites.no_rmw hX hr)
  refine ⟨a, bs, hRead, coordinate_value_of_publication hpre hX hs he hd hSite
    hRead hSize hLoc hWidth hWrite hBefore ?_⟩
  intro b hb source fp raw _ hWr hCover
  obtain ⟨h, t, f, z, extra, high, rfl, hf, hKind, hz, hStore⟩ :=
    hCovering hRead hb hWr hCover
  rcases lt_trichotomy (z.block / 4) (d.block / 4) with hOlder | hSame | hLater
  · exact .inr (.inl (coordinate_older_source_before hpre hX hs he hd hSite hRead hf hKind hz
      hStore hOrdinary hw hCur hBlock hOlder hLoc hWidth hb hCover))
  · exact .inl ⟨h, t, f, z, extra, high, rfl, hf, hKind, hz, hStore, hSame⟩
  · obtain ⟨_, hCta, hSlot, _⟩ :=
      coordinate_source_geometry hpre hX hs he hd hSite hf hz hStore hRead hKind hb hCover
    exact .inr (.inr (.direct (.inl (coordinate_before_future_producer hpre hX hs he hd hSite
      hf hz (.inr (.inl ⟨extra, high, hStore⟩)) hCta.symm hSlot hLater))))

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
