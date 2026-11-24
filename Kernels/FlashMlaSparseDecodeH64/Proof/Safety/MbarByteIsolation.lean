-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsKinds
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.AsyncSharedConflictsOutput
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.MmaAccessWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingInitSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TensorSharedBounds

public section

/-! # Byte isolation of barrier objects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {a : Acc} {l : Loc}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem ordinary_before_mbar {i : EvId} {w : Bool} (hi : X.Access i a w) (hc : a.Covers l)
    (hSpace : l.space = .shared) :
    l.addr < L.sharedBase + 222768 := by
  by_contra! hLo
  have hTail : L.sharedBase + 222752 ≤ l.addr := by omega
  have hHi := hc.2.2.2
  rcases hi with ⟨bs, hRead, _⟩ | ⟨bs, hWrite, _⟩ | ⟨_, _, h⟩
  · obtain ⟨g, k⟩ := i
    have hSite := OrdinaryReadWindow.alloc_read_of_cover hpre hX hs ht hRead hc hTail
    obtain ⟨_, he⟩ := hRead
    obtain ⟨_, hk⟩ := PrologueAllocation.alloc_read hpre hX hs hSite he
    rw [(Kind.rd.inj hk).1] at hHi
    change l.addr < L.sharedBase + 222752 + 4 at hHi
    omega
  · have hSite := RawSharedWrites.alloc_store_of_cover hpre hX hs ht hWrite hc hSpace hTail
    obtain ⟨hLoc, hSize⟩ := PrologueAllocation.allocStore_footprint hpre hX hs hWrite hSite
    rw [hLoc, hSize] at hHi
    change l.addr < L.sharedBase + 222752 + 4 at hHi
    omega
  · exact GlobalWrites.no_rmw hX h

private theorem async_before_mbar {i : EvId} {p : Part} {w : Bool} (hi : X.Intent (.async i p) a w)
    (hc : a.Covers l) (hSpace : l.space = .shared) : l.addr < L.sharedBase + 222768 := by
  have hKind := AsyncSharedConflicts.shared_async_kind hX hi hc hSpace
  cases hKind with
  | load x y b =>
    obtain ⟨_, s, _, hIssue, hLoc, hSize⟩ := hi
    obtain ⟨g, k⟩ := i
    obtain ⟨_, _, hWindow⟩ := TensorSharedBounds.write_loc_windows hpre hX hs ht hIssue hLoc
    have hHi := hc.2.2.2
    rcases hWindow with ⟨hQuery, _⟩ | ⟨hRaw, _⟩
    · have hBound := hQuery.2
      omega
    · have hBound := hRaw.2
      omega
  | output x y b =>
    have hBound := (AsyncSharedConflicts.output_read_window hpre hX hs ht hi hc).2.2.2
    omega
  | operand isB index =>
    have hSize := hi.2.1
    obtain ⟨g, k⟩ := i
    have hBound := (MmaAccessWindow.operand_regions hpre hX hs ht hi.2.2).2.2.2.2
    have hHi := hc.2.2.2
    omega

/-- No ordinary or pending asynchronous access covers a byte of any actual barrier object. -/
theorem mbar_intent_disjoint {ref : Ref} {i : EvId} {m : Loc} {count : Nat} {w : Bool}
    (hi : X.Intent ref a w) (hm : X.MbInit i m count) (hc : a.Covers l)
    (hb : Acc.Covers { loc := m, size := 8 } l) : False := by
  obtain ⟨g, k⟩ := i
  obtain ⟨_, he⟩ := hm
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, _, rfl, _⟩ := RingInitSources.init_from_trace hpre hX (hs g hg).machine ht he rfl
  have hOff : ∀ j : Fin 23, 222768 ≤ initOff j := by decide +kernel
  have hLo := hb.2.2.1
  change L.sharedBase + initOff j ≤ l.addr at hLo
  have hSpace : l.space = .shared := hb.1
  have hHi : l.addr < L.sharedBase + 222768 := by
    cases ref with
    | thread i => exact ordinary_before_mbar hpre hX hs ht hi hc hSpace
    | async i p => exact async_before_mbar hpre hX hs ht hi hc hSpace
  have hBegin := hOff j
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
