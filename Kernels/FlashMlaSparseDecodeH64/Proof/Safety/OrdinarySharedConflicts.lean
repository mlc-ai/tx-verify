-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedTileWrites
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.IndexSharedConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.SharedSoftmaxConflicts
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.AllocReadbackSources
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.OrdinaryReadWindow
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RawSharedWrites

public section

/-! # Byte order for ordinary shared-memory conflicts -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.OrdinarySharedConflicts

open PTX PTX.AsyncCopy PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {e f : EvId} {a b : Acc} {l : Loc}

private theorem plain (hX : Consistent L kernel Assumptions.all mem0 X) {w : Bool}
    (h : X.Access e a w) :
    (∃ bytes, X.Reads e a bytes ∧ w = false) ∨ ∃ bytes, X.Writes e a bytes ∧ w = true :=
  (Execution.access_iff_of_not_rmw (fun tag _ _ _ he =>
    GlobalWrites.no_rmw hX ⟨tag, he⟩)).mp h

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem alloc_write_byte {bytes : List Byte} (h : X.Writes e a bytes) (hc : a.Covers l)
    (hShared : l.space = .shared) (hLo : L.sharedBase + 222752 ≤ l.addr) :
    Frame.stateAt (Machine.code P L) X e.1 e.2 = some (some (.prologue .allocStore)) ∧
      l.cta = ctaOf L e.1 := by
  have hSite := RawSharedWrites.alloc_store_of_cover hpre hX hs ht h hc hShared hLo
  have hLoc := (PrologueAllocation.allocStore_footprint hpre hX hs h hSite).1
  exact ⟨hSite, hc.2.1.trans (congrArg Loc.cta hLoc)⟩

private theorem alloc_write_read (hResource : ¬ Tmem.Pair.ResourceUnsafe L X) {out : List Byte}
    {bytes : List (Option Byte)} (hWrite : X.Writes e a out) (hRead : X.Reads f b bytes)
    (ha : a.Covers l) (hb : b.Covers l) (hShared : l.space = .shared)
    (hLo : L.sharedBase + 222752 ≤ l.addr) :
    ByteCausality L X l (.thread e) (.thread f) := by
  obtain ⟨g, j⟩ := f
  obtain ⟨hSite, hCta⟩ := alloc_write_byte hpre hX hs ht hWrite ha hShared hLo
  have hReadSite := OrdinaryReadWindow.alloc_read_of_cover hpre hX hs ht hRead hb hLo
  obtain ⟨_, hKind⟩ := PrologueAllocation.alloc_read hpre hX hs hReadSite hRead.choose_spec
  obtain rfl := (Kind.rd.inj hKind).1
  obtain ⟨store, _, hStore, hOrder⟩ :=
    PrologueAllocation.readback_ordered hpre hX hs hResource hRead.choose_spec hReadSite
  obtain ⟨hPubSite, hPubCta⟩ := alloc_write_byte hpre hX hs ht hStore hb hShared hLo
  have hSame := PrologueAllocation.prologue_store_unique hpre (hCta.symm.trans hPubCta)
    hWrite.choose_spec hStore.choose_spec hSite hPubSite
  obtain ⟨hSpace, hCta', hStart, hEnd⟩ := hb
  change (PrologueAllocation.allocAddress L g).addr ≤ l.addr at hStart
  change l.addr < (PrologueAllocation.allocAddress L g).addr + 4 at hEnd
  let pos := l.addr - (PrologueAllocation.allocAddress L g).addr
  have hPos : pos < 4 := by
    dsimp only [pos]
    omega
  have hLoc : l = (PrologueAllocation.allocAddress L g).at pos := by
    have hAddr : l.addr = (PrologueAllocation.allocAddress L g).addr + pos := by
      unfold pos
      omega
    cases l
    rw [Loc.mk.injEq]
    exact ⟨hSpace, hCta', hAddr⟩
  rw [hSame, hLoc]
  exact .direct (hOrder pos hPos)

/-- Every conflicting pair of ordinary shared-memory accesses is ordered on its shared byte. -/
theorem ordinary_conflict_ordered (hResource : ¬ Tmem.Pair.ResourceUnsafe L X)
    (hConflict : Conflict X (.thread e) (.thread f) a b) (ha : a.Covers l) (hb : b.Covers l)
    (hShared : l.space = .shared) :
    ByteCausality L X l (.thread e) (.thread f) ∨
      ByteCausality L X l (.thread f) (.thread e) := by
  by_cases hTile : l.addr < L.sharedBase + 131072
  · exact SharedTileWrites.ordinary_conflict_ordered hpre hX hs ht hConflict ha hb hShared hTile
  by_cases hRaw : l.addr < L.sharedBase + 204800
  · obtain ⟨_, u, v, hU, hV, hWrite, _⟩ := hConflict
    have noWrite {i : EvId} {fp : Acc} (h : X.Access i fp true) (hCover : fp.Covers l) : False := by
      rcases plain hX h with ⟨_, _, hFalse⟩ | ⟨_, hw, _⟩
      · cases hFalse
      · exact RawSharedWrites.no_ordinary hpre hX hs ht hw hCover hShared
          (Nat.le_of_not_gt hTile) hRaw
    rcases hWrite with rfl | rfl
    · exact (noWrite hU ha).elim
    · exact (noWrite hV hb).elim
  by_cases hSoftmax : l.addr < L.sharedBase + 221696
  · exact SharedSoftmaxConflicts.ordinary_conflict_ordered hpre hX hs ht hConflict ha hb
      ⟨hShared, Nat.le_of_not_gt hRaw, hSoftmax⟩
  by_cases hIndex : l.addr < L.sharedBase + 222752
  · exact IndexSharedConflicts.ordinary_conflict_ordered hpre hX hs ht hConflict ha hb
      ⟨hShared, Nat.le_of_not_gt hSoftmax, hIndex⟩
  have hAlloc := Nat.le_of_not_gt hIndex
  obtain ⟨hne, u, v, hU, hV, hWrite, _⟩ := hConflict
  rcases plain hX hU with ⟨_, hRead, rfl⟩ | ⟨_, hWriteE, rfl⟩ <;>
    rcases plain hX hV with ⟨_, hRead', rfl⟩ | ⟨_, hWriteF, rfl⟩
  · simp at hWrite
  · exact .inr (alloc_write_read hpre hX hs ht hResource hWriteF hRead hb ha hShared hAlloc)
  · exact .inl (alloc_write_read hpre hX hs ht hResource hWriteE hRead' ha hb hShared hAlloc)
  · obtain ⟨hSite, hCta⟩ := alloc_write_byte hpre hX hs ht hWriteE ha hShared hAlloc
    obtain ⟨hSite', hCta'⟩ := alloc_write_byte hpre hX hs ht hWriteF hb hShared hAlloc
    have hEq := PrologueAllocation.prologue_store_unique hpre (hCta.symm.trans hCta')
      hWriteE.choose_spec hWriteF.choose_spec hSite hSite'
    exact (hne (congrArg Ref.thread hEq)).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety.OrdinarySharedConflicts
