-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.RawGatherConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryReuseTma
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Lemmas.Order.Order
import Lemmas.TensorStore.StoreWrite

public section

/-! # Byte order for shared destinations of tensor loads -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts

open PTX PTX.Flow PTX.AsyncCopy TensorSharedBounds Protocol

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem load_write_location {i : EvId} {x y b : Nat} {a : Acc} {l : Loc}
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l) :
    ∃ address spec, X.TensorIssue i address spec ∧ TensorCopy.writeLoc spec x y b = some l := by
  obtain ⟨_, spec, address, hIssue, hLoc, hSize⟩ := hi
  rw [Acc.loc_of_one ha hSize] at hLoc
  exact ⟨address, spec, hIssue, hLoc⟩

/-- A tensor load's destination intent covers a byte of the query tile or the raw buffers,
even when the write has yet to occur. -/
theorem load_write_window {i : EvId} {x y b : Nat} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l) :
    l.space = .shared ∧ l.cta = ctaOf L i.1 ∧ (QueryWindow L l ∨ RawWindow L l) := by
  obtain ⟨_, _, hIssue, hLoc⟩ := load_write_location hi ha
  obtain ⟨hShared, hCta, h⟩ := TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc
  exact ⟨hShared, hCta, h.imp And.left And.left⟩

private theorem query_write_fields {g i x y b : Nat} {a : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async (g, i) (.write (.load x y b))) a true) (ha : a.Covers l)
    (hQ : QueryWindow L l) :
    ∃ (d : Wg1Mma.D) (tile : Fin 8) (e : Event),
      X.get (g, i) = some e ∧ l.cta = ctaOf L g ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)) ∧ d.site = .qLoad tile ∧
      x < 64 ∧ y < 64 ∧ b < 2 ∧ TensorSwizzle.offset .b128 0 l.addr =
        L.sharedBase + 8192 * tile.val + 128 * y + 2 * x + b := by
  obtain ⟨_, _, hIssue, hLoc⟩ := load_write_location hi ha
  obtain ⟨_, hCta, ⟨_, hMbar⟩ | ⟨hRaw, _⟩⟩ :=
    TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc
  · obtain ⟨_, he⟩ := hIssue
    obtain ⟨_, d, tile, hd, hSite, hSpec⟩ :=
      QueryTmaRecords.issue_source hpre hX (fun h hh => (hs h hh).machine) ht he rfl hMbar
    rw [hSpec] at hLoc
    exact ⟨d, tile, _, he, hCta, hd, hSite, TensorSharedBounds.query_linear_address hpre tile hLoc⟩
  · exact (query_raw_disjoint hQ hRaw).elim

/-- Pending query writes to one byte name the same async reference. -/
theorem query_write_unique {i j : EvId} {x y b x' y' b' : Nat} {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l)
    (hj : X.Intent (.async j (.write (.load x' y' b'))) f true) (hf : f.Covers l)
    (hQ : QueryWindow L l) :
    (.async i (.write (.load x y b)) : Ref) = .async j (.write (.load x' y' b')) := by
  obtain ⟨g, i⟩ := i
  obtain ⟨g', j⟩ := j
  obtain ⟨d, tile, _, he, hCta, hd, hSite, hx, hy, hb, hAddr⟩ :=
    query_write_fields hpre hX hs ht hi ha hQ
  obtain ⟨d', tile', _, he', hCta', hd', hSite', hx', hy', hb', hAddr'⟩ :=
    query_write_fields hpre hX hs ht hj hf hQ
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := l.cta) hpre hX
    (fun h hh => (hs h hh).machine)
  have hLane : g = g' :=
    (hLeader g i d hCta.symm hd (by simp [hSite])).trans
      (hLeader g' j d' hCta'.symm hd' (by simp [hSite'])).symm
  subst g'
  have hEq := hAddr.symm.trans hAddr'
  have hTile : tile = tile' := Fin.ext (by omega)
  subst tile'
  have hIndex := QueryTmaSites.load_site_unique he he' hd hd' hSite hSite'
  obtain rfl : x = x' := by omega
  obtain rfl : y = y' := by omega
  obtain rfl : b = b' := by omega
  rw [hIndex]

/-- Two different tensor loads that can write a common shared byte are ordered there. -/
theorem load_writes_ordered {i j : EvId} {x y b x' y' b' : Nat} {a f : Acc} {l : Loc}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l)
    (hj : X.Intent (.async j (.write (.load x' y' b'))) f true) (hf : f.Covers l)
    (hne : Ref.async i (.write (.load x y b)) ≠ .async j (.write (.load x' y' b'))) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.async j (.write (.load x' y' b'))) ∨
    ByteCausality L X l (.async j (.write (.load x' y' b'))) (.async i (.write (.load x y b))) := by
  rcases (load_write_window hpre hX hs ht hi ha).2.2 with hQ | hRaw
  · exact (hne (query_write_unique hpre hX hs ht hi ha hj hf hQ)).elim
  · exact RawGatherConflicts.writes_ordered hpre hX hs ht hi hj hne ha hf hRaw

/-- A tensor load and an ordinary access to a common destination byte are ordered there. -/
theorem load_write_thread_ordered {i j : EvId} {x y b : Nat} {a f : Acc} {l : Loc} {w : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.Intent (.async i (.write (.load x y b))) a true) (ha : a.Covers l)
    (hj : X.Intent (.thread j) f w) (hf : f.Covers l) :
    ByteCausality L X l (.async i (.write (.load x y b))) (.thread j) ∨
    ByteCausality L X l (.thread j) (.async i (.write (.load x y b))) := by
  have hNoRmw : ∀ tag access old bytes, X.get j ≠ some ⟨tag, .rmw access old bytes⟩ :=
    fun tag _ _ _ he => GlobalWrites.no_rmw hX ⟨tag, he⟩
  obtain ⟨hShared, _, hQ | hRaw⟩ := load_write_window hpre hX hs ht hi ha
  · rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hj with ⟨_, hRead, _⟩ | ⟨_, hWrite, _⟩
    · have hAbove := OrdinaryReadWindow.read_above_tiles hpre hX hs ht hRead hf
      exact (by have := hQ.2; omega : False).elim
    · have hBelow : l.addr < L.sharedBase + 131072 := by have := hQ.2; omega
      rcases (RawSharedWrites.tile_writer_role hpre hX hs ht hWrite hf hShared hBelow).2 with
        ⟨d, r, k, hd, hSite⟩ | ⟨hAbove, _⟩
      · obtain ⟨issuer, n, x', y', b', value, hSource, hOrder⟩ :=
          GemmRing.query_tma_before_store_byte hpre hX (fun g hg => (hs g hg).machine)
            hd hSite hWrite hf hQ.1 hQ.2
        have hCovers : ({ loc := l, size := 1 } : Acc).Covers l :=
          Acc.covers_at (k := 0) (show 0 < 1 by decide)
        have hEq := query_write_unique hpre hX hs ht hi ha hSource.intent hCovers hQ
        rw [hEq]
        exact .inl hOrder
      · exact (by have := hQ.2; omega : False).elim
  · cases w
    · exact RawGatherConflicts.ordinary_read_ordered hpre hX hs ht hj hi hf ha hRaw
    · rcases (Execution.access_iff_of_not_rmw hNoRmw).mp hj with ⟨_, _, hFalse⟩ | ⟨_, hWrite, _⟩
      · cases hFalse
      · exact (RawSharedWrites.no_ordinary hpre hX hs ht hWrite hf hShared hRaw.1 hRaw.2).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflicts
