-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TensorShared
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess
import Kernels.TmlFa4Fwd.Proof.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
import Kernels.TmlFa4Fwd.Proof.Thread.SharedReadSites
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Lemmas.Tensor.TensorCopy

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof

private theorem sharedByteAllocated {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {loc : Loc}
    (hSpace : loc.space = .shared) (hCta : loc.cta = g / l.block)
    (hLower : l.sharedBase ≤ loc.addr) (hUpper : loc.addr < l.sharedBase + 232448) :
    m loc ≠ none := by
  have hOwner : g / l.block < l.grid := by
    change g < l.grid * l.block at hg
    rw [hp.block] at hg ⊢
    omega
  obtain ⟨space, cta, addr⟩ := loc
  change l.sharedBase ≤ addr at hLower
  have hLoc : (⟨space, cta, addr⟩ : Loc) =
      ⟨.shared, g / l.block, l.sharedBase + (addr - l.sharedBase)⟩ := by
    simp only [Loc.mk.injEq]
    exact ⟨hSpace, hCta, (Nat.add_sub_of_le hLower).symm⟩
  rw [hLoc]
  exact hp.shared.2.2 _ hOwner _ (by change addr < _ at hUpper; omega)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The actual eight-byte object used by each barrier operand is allocated. -/
theorem mbarOperandAllocated {i : EvId} {object loc : Loc} (hUse : X.UsesMbar i object)
    (hCover : Acc.Covers {loc := object, size := 8} loc) : m loc ≠ none := by
  have hg : i.1 < l.threads := by
    rcases hUse with ⟨_, _, _, _, _, he⟩ | ⟨_, ⟨_, he⟩, _⟩ | ⟨_, _, he⟩ |
      ⟨_, _, ⟨_, he⟩, _⟩ | ⟨_, _, _, _, _, he⟩ | ⟨_, he⟩ | ⟨_, _, ⟨_, he⟩, _⟩ |
      ⟨_, _, _, ⟨_, he⟩, _, _⟩ | ⟨_, _, he⟩ <;> exact event_thread_lt hX he
  have hBound := actualMbarAddressBound hp hX hUse
  obtain ⟨site, hObj⟩ := actualMbarAddresses hp hX i object hUse
  obtain ⟨hs, hc, hLo, hHi⟩ := hCover
  change loc.space = object.space at hs
  change loc.cta = object.cta at hc
  change object.addr ≤ loc.addr at hLo
  change loc.addr < object.addr + 8 at hHi
  rw [hObj] at hs hc hLo
  exact sharedByteAllocated hp hg hs hc
    (by dsimp [Prologue.initObject] at hLo; omega) (by omega)

/-- Each actual shared store touches only bytes allocated to the issuing CTA. -/
theorem ordinarySharedWriteAllocated {i : EvId} {a : Acc} {loc : Loc} {data : List Byte}
    (hWrite : X.Writes i a data) (hCover : a.Covers loc) (hSpace : loc.space = .shared) :
    m loc ≠ none := by
  have hg := access_thread_lt hX hWrite.access
  have hCta := hCover.2.1.trans (sharedWriteOwned hX hWrite (hCover.1.symm.trans hSpace))
  obtain ⟨hLo, hHi⟩ := Thread.ordinarySharedWriteBounds hp hX hWrite hCover hSpace
  exact sharedByteAllocated hp hg hSpace hCta hLo hHi

/-- The allocator result, statistics and Bias cover every actual ordinary shared load. -/
theorem ordinarySharedReadAllocated {i : EvId} {a : Acc} {loc : Loc} {data : List (Option Byte)}
    (hRead : X.Reads i a data) (hCover : a.Covers loc) (hSpace : loc.space = .shared) :
    m loc ≠ none := by
  have hg := access_thread_lt hX hRead.access
  have hShared := hCover.1.symm.trans hSpace
  have hCta := hCover.2.1.trans (Thread.Loader.sharedReadOwned hX hRead hShared)
  suffices hRange : l.sharedBase ≤ loc.addr ∧ loc.addr < l.sharedBase + 232448 from
    sharedByteAllocated hp hg hSpace hCta hRange.1 hRange.2
  have hLo : a.loc.addr ≤ loc.addr := hCover.2.2.1
  have hHi : loc.addr < a.loc.addr + a.size := hCover.2.2.2
  rcases Thread.sharedReadObservation hX hRead hShared with
    hAlloc | ⟨_, _, hBias⟩ | ⟨_, _, hStats⟩
  · obtain ⟨g, j⟩ := i
    have hExact : a = {loc := Mma.allocationSlot l g, size := 4} :=
      Mma.allocationReadFootprint hp hX hAlloc
    rw [hExact] at hLo hHi
    change l.sharedBase + 312 ≤ loc.addr at hLo
    change loc.addr < l.sharedBase + 312 + 4 at hHi
    exact ⟨by omega, by omega⟩
  · obtain ⟨hStart, _, hEnd⟩ := Thread.Scores.biasVectorReadRange hp hX hBias
    exact ⟨by omega, by omega⟩
  · obtain ⟨hStart, _, hEnd⟩ := Thread.Correction.statisticsReadRange hp hX hStats
    exact ⟨by omega, by omega⟩

/-- Every byte of a thread's actual local load or store is allocated in its own stack. -/
theorem localAccessAllocated {i : EvId} {a : Acc} {write : Bool} (hAccess : X.Access i a write)
    (hLocal : a.loc.space = .local) {loc : Loc} (hCovers : a.Covers loc) :
    m loc ≠ none := by
  have hStack : Thread.Loader.StackAccess l m i.1 a := by
    rcases hAccess with ⟨_, hRead, _⟩ | ⟨_, hWrite, _⟩ | ⟨_, _, hRmw⟩
    · exact (Thread.Loader.localReadStack hp hX hRead hLocal).1
    · exact (Thread.Loader.localWriteStack hp hX hWrite hLocal).1
    · exact (noActualRmw hX hRmw).elim
  obtain ⟨hs, hc, hLo, hHi⟩ := hCovers
  let byte := loc.addr - a.loc.addr
  have hByte : byte < a.size := by dsimp [byte]; omega
  have hLoc : loc = a.loc.at byte := by
    rcases loc with ⟨space, cta, address⟩
    rcases a with ⟨⟨baseSpace, baseCta, baseAddress⟩, _, _, _, _, _, _⟩
    simp only [Loc.at, Loc.mk.injEq]
    exact ⟨hs, hc, by
      change address = baseAddress + (address - baseAddress)
      exact (Nat.add_sub_of_le hLo).symm⟩
  rw [hLoc]
  exact (hStack.2.2 byte hByte).2.2

/-- Every byte of an ordinary copy's actual shared destination is allocated,
even if the thread has yet to commit the copy group. -/
theorem ordinaryCopyDestinationAllocated {i : EvId} {spec : AsyncCopy.Spec} (hCopy : X.Copy i spec)
    {loc : Loc} (hCover : spec.dst.Covers loc) : m loc ≠ none := by
  obtain ⟨hi, slot, pair, upper, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  rw [hDst] at hCover
  let base := kvCopyAddress l.sharedBase slot (i.1 % l.block) pair upper
  obtain ⟨hSpace, hCta, hLo, hHi⟩ := hCover
  change base ≤ loc.addr at hLo
  change loc.addr < base + 16 at hHi
  have hc : i.1 / l.block < l.grid := by
    change i.1 < l.grid * l.block at hi
    rw [hp.block] at hi ⊢
    omega
  have hLoc : loc = ⟨.shared, i.1 / l.block, base + (loc.addr - base)⟩ := by
    obtain ⟨space, cta, addr⟩ := loc
    change base ≤ addr at hLo
    simp only [Loc.mk.injEq]
    exact ⟨hSpace, hCta, Nat.add_sub_of_le hLo |>.symm⟩
  rw [hLoc]
  exact hp.kv_destination_allocated (lane := i.1 % l.block) (upper := upper)
    hc slot.isLt pair.isLt (by omega)


/-- An actual input load has a launch-provided byte for every in-bounds global read. -/
theorem actualTensorInputReadAllocated {i : EvId} {addr x y k : Nat} {s : TensorCopy.Spec}
    (hi : X.TensorIssue i addr s) {loc : Loc} (hRead : TensorCopy.readLoc s x y k = some loc)
    : m loc ≠ none := by
  rw [TensorCopy.readLoc_source] at hRead
  rcases hSlot : TensorTransfer.slotAt s.descriptor x y k with _ | slot
  · simp [hSlot] at hRead
  · simp only [hSlot, Option.bind_some] at hRead
    cases hSource : TensorCopy.source s slot with
    | global address =>
      simp only [hSource, Option.some.injEq] at hRead
      obtain ⟨_, _, _, byte, hByte⟩ := (actualTensorInputSource hp hX hi).2.2.2 _ _ hSource
      rw [← hRead]
      change m (globalLoc address) ≠ none
      rw [hByte]
      simp
    | fill => simp [hSource] at hRead

omit hp hX in
/-- The abstract output footprint ensures backing for every intended global output byte. -/
theorem globalOutputAllocated {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hFrame : OutputIntentFootprint p X)
    {w : AsyncCopy.Ref} {a : Acc} {loc : Loc} (hWrite : X.Intent w a true)
    (hCover : a.Covers loc) (hGlobal : loc.space = .global) : m loc ≠ none := by
  apply hp.outputs
  rcases hFrame w a loc hWrite hCover hGlobal with hO | ⟨row, hr, head, hh, byte, hb, rfl⟩
  · exact .inl hO
  · exact .inr (lseByte_in hr hh hb)

/-- Given the output footprint, only metadata loads and paged copy sources can be unallocated.
The footprint checks include pending asynchronous effects. -/
theorem unallocatedReadSource (hOutput : OutputIntentFootprint p X) (hBad : Unalloc m X) :
    (∃ i a bytes loc, X.Reads i a bytes ∧ a.Covers loc ∧ loc.space = .global ∧ m loc = none) ∨
    ∃ i spec loc, X.Copy i spec ∧ spec.src.Covers loc ∧ m loc = none := by
  rcases hBad with ⟨issue, a, loc, hTouches, hCover, hNone⟩ | ⟨_, _, _, hUse, hCover, hNone⟩
  · rcases hTouches with ⟨_, hIntent⟩ | ⟨_, _, rfl, hRead⟩
    swap
    · exact (Thread.noNoncoherentRead hX hRead).elim
    cases issue with
    | thread i =>
      rcases hIntent with ⟨_, hRead, _⟩ | ⟨_, hWrite, _⟩ | ⟨_, _, hRmw⟩
      · cases hSpace : loc.space with
        | global => exact .inl ⟨_, _, _, _, hRead, hCover, hSpace, hNone⟩
        | «local» =>
          have hLocal := hCover.1.symm.trans hSpace
          exact (localAccessAllocated hp hX hRead.access hLocal hCover hNone).elim
        | shared => exact (ordinarySharedReadAllocated hp hX hRead hCover hSpace hNone).elim
        | const => exact (Thread.Loader.noConstantRead hX hRead (hCover.1.symm.trans hSpace)).elim
      · cases hSpace : loc.space with
        | global =>
          have hIntent : X.Intent (.thread i) a true := hWrite.access
          exact (globalOutputAllocated hp hOutput hIntent hCover hSpace hNone).elim
        | «local» =>
          have hLocal := hCover.1.symm.trans hSpace
          exact (localAccessAllocated hp hX hWrite.access hLocal hCover hNone).elim
        | shared => exact (ordinarySharedWriteAllocated hp hX hWrite hCover hSpace hNone).elim
        | const => exact (noConstantWrite hX hWrite (hCover.1.symm.trans hSpace)).elim
      · exact (noActualRmw hX hRmw).elim
    | async i part =>
      obtain ⟨hMode, hFoot⟩ := hIntent
      clear hMode
      cases part <;> try (exact False.elim hFoot)
      case mmaRead isB index =>
        rw [← Acc.loc_of_one hCover hFoot.1] at hNone
        have hRange := Thread.mmaSharedByteRange hp hX hFoot.2
        obtain ⟨_, _, _, _, _, hIssue, _⟩ := Thread.mmaSharedFootprintIssue hX hFoot.2
        obtain ⟨_, he⟩ := hIssue
        exact (hRange.allocated hp (event_thread_lt hX he) hNone).elim
      case readCopy =>
        rcases hFoot with ⟨s, hCopy, rfl⟩ | hPrefetch
        · exact .inr ⟨_, _, _, hCopy, hCover, hNone⟩
        · exact (Thread.noBulkPrefetch hX hPrefetch).elim
      case readStore x y k =>
        obtain ⟨s, _, hIssue, hRead, hSize⟩ := hFoot
        obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hRead
        rw [← Acc.loc_of_one hCover hSize, ← hLoc] at hNone
        exact (actualTensorOutputSharedAllocated hp hX hIssue slot hNone).elim
      case readLoad =>
        obtain ⟨_, _, hIssue, hRead, hSize⟩ := hFoot
        rw [← Acc.loc_of_one hCover hSize] at hNone
        exact (actualTensorInputReadAllocated hp hX hIssue hRead hNone).elim
      case readPrefetch =>
        obtain ⟨_, _, hIssue, _, _⟩ := hFoot
        exact (Thread.noTensorPrefetch hX hIssue).elim
      case writeCopy =>
        obtain ⟨_, hIssue, _, rfl⟩ := hFoot
        exact (ordinaryCopyDestinationAllocated hp hX hIssue hCover hNone).elim
      case writeElem =>
        obtain ⟨s, hIssue, hElem⟩ := hFoot
        have hWhole := (actualCopyShape hX hIssue).whole
        simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, hWhole] at hElem
      case writeStore x y k =>
        have hIntent : X.Intent (.async i (.write (.store x y k))) a true := ⟨rfl, hFoot⟩
        obtain ⟨_, _, _, hByte, _⟩ := hFoot
        have hGlobal := hCover.1.trans (Execution.store_writeLoc_global hByte)
        exact (globalOutputAllocated hp hOutput hIntent hCover hGlobal hNone).elim
      case writeLoad x y k =>
        obtain ⟨_, _, hIssue, hByte, hSize⟩ := hFoot
        obtain ⟨slot, _, hLoc⟩ := Option.map_eq_some_iff.mp hByte
        rw [← Acc.loc_of_one hCover hSize, ← hLoc] at hNone
        exact (actualTensorInputSharedAllocated hp hX hIssue slot hNone).elim
      case writeCta =>
        obtain ⟨_, _, hIssue, _, _⟩ := hFoot
        exact (noClcIssue hX hIssue).elim
      case oldElem =>
        obtain ⟨_, _, hIssue, hReduce, _⟩ := hFoot
        rw [(actualCopyShape hX hIssue).whole] at hReduce
        cases hReduce
      case oldStore =>
        obtain ⟨_, _, hIssue, hReduce, _, _⟩ := hFoot
        rw [(Thread.actualTensorStoreForm hX hIssue).2.2] at hReduce
        cases hReduce
  · exact (mbarOperandAllocated hp hX hUse hCover hNone).elim

end PTX.Kernels.TmlFa4Fwd.Safety
