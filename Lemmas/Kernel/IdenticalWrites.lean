-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Memory
public import Core.Assembly.Safety

@[expose] public section

/-! # The memory after identical-value writes

A proof tool. Two writes of the same bytes with the same value (`SameValueWrites`, the pairs
ERR-DATA-RACE does not count as a race) write the same byte at every byte they cover
(`SameValueWrites.wbyte_eq`). When every write of a byte is one write `w0` or such a partner of
it, and the writes are among finitely many (`ws`), the memory after the execution holds `w0`'s
byte (`IsFinal.of_identical_writers`): all co-maximal writes agree (CORRECT-FINAL), whatever the
coherence order leaves unordered. The tensor-store slot writes of one slot by the launch's
threads are such a finite list (`storeWrites`). -/

namespace PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Two writes of the same bytes with the same value write the same byte at every location. -/
theorem SameValueWrites.wbyte_eq {e f : AsyncCopy.Ref} {a b : Acc} {bs bs' : List Byte}
    (h : SameValueWrites X e f a b) (he : X.MemWrites e a bs) (hf : X.MemWrites f b bs')
    (l : Loc) : wbyte a bs l = wbyte b bs' l := by
  obtain ⟨-, -, ⟨hl, -⟩, hv⟩ := h
  rw [hv bs bs' he hf]
  simp only [wbyte, hl]

/-- **Identical-value writes leave their byte.** If the writes of `l` are among `ws`, and each is
`w0` or writes the same bytes with the same value as `w0`, the memory after the execution holds
`w0`'s byte at `l`. -/
theorem IsFinal.of_identical_writers {m : FinalMem} (hf : IsFinal L mem0 X m) {l : Loc}
    {ws : List AsyncCopy.Ref} (hws : ∀ w a bs, X.MemWrites w a bs → a.Covers l → w ∈ ws)
    {w0 : AsyncCopy.Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w0 a bs) (hc : a.Covers l)
    (hall : ∀ w a' bs', X.MemWrites w a' bs' → a'.Covers l → w = w0 ∨ SameValueWrites X w0 w a a') :
    m l = some (wbyte a bs l) := by
  refine IsFinal.of_agree hf hws hw hc fun w a' bs' hw' hc' => ?_
  rcases hall w a' bs' hw' hc' with rfl | hd
  · obtain ⟨hfp, rfl⟩ := hw'.unique hw
    simp only [wbyte, hfp.1]
  · exact (hd.wbyte_eq hw hw' l).symm

/-- The tensor-store write of byte `k` of element `(x, y)` by issue `i`. -/
abbrev storeWrite (i : EvId) (x y k : Nat) : AsyncCopy.Ref := .async i (.write (.store x y k))

/-- The tensor-store writes of slot `(x, y, k)` by every event of the launch's threads. -/
def storeWrites (L : Launch) (X : Execution) (x y k : Nat) : List AsyncCopy.Ref :=
  (List.range L.threads).flatMap fun g =>
    (List.range (X.tr g).length).map fun n => storeWrite (g, n) x y k

/-- The slot write of an event of a thread of the launch is one of `storeWrites`. -/
theorem mem_storeWrites {j : EvId} {x y k : Nat} (hj : j.1 < L.threads)
    (hlen : j.2 < (X.tr j.1).length) : storeWrite j x y k ∈ storeWrites L X x y k :=
  List.mem_flatMap.mpr ⟨j.1, List.mem_range.mpr hj,
    List.mem_map.mpr ⟨j.2, List.mem_range.mpr hlen, rfl⟩⟩

end PTX
