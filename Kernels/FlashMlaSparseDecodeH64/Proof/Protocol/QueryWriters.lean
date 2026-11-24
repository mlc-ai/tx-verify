-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryReuseTma
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader

import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingTmaCoordinate

@[expose] public section

/-! # The query byte has one actual tensor writer -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing

open PTX PTX.Flow AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem query_site_at_write {g i x y b : Nat} {a : Acc} {data : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a data) (ha : a.Covers byte)
    (hQ : TensorSharedBounds.QueryWindow L byte) :
    ∃ (d : Wg1Mma.D) (tile : Fin 8) (e : Event), X.get (g, i) = some e ∧ byte.cta = ctaOf L g ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site = .qLoad tile ∧
      x < 64 ∧ y < 64 ∧ b < 2 ∧ TensorSwizzle.offset .b128 0 byte.addr =
        L.sharedBase + 8192 * tile.val + 128 * y + 2 * x + b := by
  obtain ⟨o, address, _, _, hi, hl, _, hz, _⟩ := hw
  have hSame : a.loc = byte := by
    obtain ⟨hSpace, hCta, hlo, hhi⟩ := ha
    have hAddr : a.loc.addr = byte.addr := by omega
    cases hLoc : a.loc
    cases byte
    simpa only [Loc.mk.injEq, hLoc] using And.intro hSpace.symm (And.intro hCta.symm hAddr)
  rw [hSame] at hl
  obtain ⟨tag, he⟩ := hi
  have hFollow := MachineTracking.actual_tensor_issue_followed hpre hX hs he rfl
  obtain ⟨_, hCta, hQuery | hRaw⟩ :=
    TensorSharedBounds.write_loc_windows_at_followed hpre hX hs hFollow ⟨tag, he⟩ hl
  · obtain ⟨_, hm⟩ := hQuery
    obtain ⟨_, d, tile, hst, hsite, hspec⟩ :=
      QueryTmaRecords.actual_issue_source hpre hX hs he rfl hm
    rw [hspec] at hl
    exact ⟨d, tile, _, he, hCta, hst, hsite,
      TensorSharedBounds.query_linear_address hpre tile hl⟩
  · exact (TensorSharedBounds.query_raw_disjoint hQ hRaw.1).elim

/-- Two actual tensor writes that touch the same Q byte are one asynchronous reference. -/
theorem query_writer_unique {g i x y b g' j x' y' b' : Nat}
    {a a' : Acc} {data data' : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hw : X.MemWrites (.async (g, i) (.write (.load x y b))) a data) (ha : a.Covers byte)
    (hw' : X.MemWrites (.async (g', j) (.write (.load x' y' b'))) a' data')
    (ha' : a'.Covers byte) (hQ : TensorSharedBounds.QueryWindow L byte) :
    (.async (g, i) (.write (.load x y b)) : Ref) = .async (g', j) (.write (.load x' y' b')) := by
  obtain ⟨d, tile, e, he, hCta, hd, hsite, hx, hy, hb, hAddr⟩ :=
    query_site_at_write hpre hX hs hw ha hQ
  obtain ⟨d', tile', e', he', hCta', hd', hsite', hx', hy', hb', hAddr'⟩ :=
    query_site_at_write hpre hX hs hw' ha' hQ
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := byte.cta) hpre hX
    (fun h hh => (hs h hh).machine)
  have hLane : g = g' :=
    (hLeader g i d hCta.symm hd (by simp [hsite])).trans
      (hLeader g' j d' hCta'.symm hd' (by simp [hsite'])).symm
  subst g'
  have hEq := hAddr.symm.trans hAddr'
  have hTile : tile = tile' := Fin.ext (by omega)
  subst tile'
  have hIndex := QueryTmaSites.load_site_unique he he' hd hd' hsite hsite'
  obtain rfl : x = x' := by omega
  obtain rfl : y = y' := by omega
  obtain rfl : b = b' := by omega
  rw [hIndex]

/-- A given actual tensor writer of a reused Q byte precedes its covering dequantizer store. -/
theorem query_writer_ordered {g j : Nat} {d : Wg2.D} {r : Fin 4} {s : Fin 8}
    {a : Acc} {data : List Byte} {issue : EvId} {x y b : Nat}
    {fp : Acc} {source : List Byte} {byte : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hd : Frame.stateAt (Machine.code P L) X g j = some (some (.wg2 d)))
    (hsite : d.site = .store r s) (hw : X.Writes (g, j) a data) (ha : a.Covers byte)
    (hTma : X.MemWrites (.async issue (.write (.load x y b))) fp source) (hf : fp.Covers byte)
    (hQ : TensorSharedBounds.QueryWindow L byte) :
    ByteCausality L X byte (.async issue (.write (.load x y b))) (.thread (g, j)) := by
  obtain ⟨i', t', x', y', b', value, hSource, hBefore⟩ :=
    query_tma_before_store_byte hpre hX (fun h hh => (hs h hh).machine) hd hsite hw ha hQ.1 hQ.2
  have hcover : ({ loc := byte, size := 1 } : Acc).Covers byte :=
    Acc.covers_at (k := 0) (show 0 < 1 by decide)
  rw [query_writer_unique hpre hX hs hTma hf hSource hcover hQ]
  exact hBefore

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.GemmRing
