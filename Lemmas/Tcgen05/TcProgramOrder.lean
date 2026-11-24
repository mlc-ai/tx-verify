-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TmemWriters
public import Lemmas.Order.OrderWaits
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # Tensor Core orders of one thread's program order

A tcgen05 event performs no memory access, so program order from it is causality
(`baseCausality_of_tc_po`). Within one thread, in program order:

* two MMAs with the same accumulator are the pipelined D/D pair of §9.7.18.6.2
  (`Before.of_mma_po`);
* an MMA reading A from Tensor Memory and a later MMA are the pipelined A-read/D-write pair
  (`Pipelined.of_aRead_po`);
* a store and a later store are the pipelined st→st pair (`StoreDoneBefore.of_po`). -/

namespace PTX.TcMma
open PTX
noncomputable section

variable {L : Launch} {X : Execution}

/-- **Program order from a tcgen05 event is causality.** -/
theorem baseCausality_of_tc_po {e f : EvId} {pc : Nat} {k : TcKind}
    (he : X.get e = some ⟨pc, .tc k⟩)
    (hs : e.1 = f.1) (hlt : e.2 < f.2) (hf : f.2 < (X.tr f.1).length) : baseCausality L X e f :=
  .single (.inl (po_of_source_not_access hs hlt hf (by rw [he]; rfl)))

/-- A thread is in its own warp. -/
theorem sameWarp_self {g : Nat} (hg : g < L.threads) : SameWarp L g g := ⟨⟨hg, hg, rfl⟩, rfl⟩

/-- **Two MMAs of one thread with the same accumulator, in program order, are pipelined.** -/
theorem Before.of_mma_po {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (hy : X.MmaIssue y d' s' acc' mask')
    (hg : x.1 < L.threads) (hthr : x.1 = y.1) (hlt : x.2 < y.2)
    (hacc : SameAccumulator d s d' s') : Before L X x y := by
  obtain ⟨pc, hxg⟩ := hx
  obtain ⟨pc', hyg⟩ := id hy
  refine .inr ⟨hthr ▸ sameWarp_self hg, .inl (baseCausality_of_tc_po hxg hthr hlt (len_of_get hyg)),
    d, s, acc, mask, d', s', acc', mask', ⟨pc, hxg⟩, hy, hacc⟩

/-- **An MMA reading A from Tensor Memory and a later MMA of its thread are pipelined.** -/
theorem Pipelined.of_aRead_po {x y : EvId} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
    {mask mask' : List Nat} (hx : X.MmaIssue x d s acc mask) (ha : s.aTmem.isSome)
    (hy : X.MmaIssue y d' s' acc' mask') (hg : x.1 < L.threads) (hthr : x.1 = y.1)
    (hlt : x.2 < y.2) : Pipelined L X .aRead x .dWrite y := by
  obtain ⟨pc, hxg⟩ := hx
  obtain ⟨pc', hyg⟩ := id hy
  exact ⟨hthr ▸ sameWarp_self hg, .inl (baseCausality_of_tc_po hxg hthr hlt (len_of_get hyg)),
    ⟨d, s, acc, mask, ⟨pc, hxg⟩, ha⟩, d', s', acc', mask', hy⟩

/-- **A store and a later store of its thread are pipelined.** -/
theorem StoreDoneBefore.of_po {x y : EvId} {a a' : Nat} {vals vals' : List Value}
    {sh sh' : TcShape} (hx : X.TSt x a vals sh) (hy : X.TSt y a' vals' sh') (hg : x.1 < L.threads)
    (hthr : x.1 = y.1) (hlt : x.2 < y.2) : StoreDoneBefore L X x y := by
  obtain ⟨pc, hxg⟩ := id hx
  obtain ⟨pc', hyg⟩ := id hy
  exact ⟨⟨a, vals, sh, hx⟩, .inr (.inr ⟨hthr ▸ sameWarp_self hg,
    .inl (baseCausality_of_tc_po hxg hthr hlt (len_of_get hyg)), ⟨a, vals, sh, hx⟩,
    ⟨a', vals', sh', hy⟩⟩)⟩

end
end PTX.TcMma
