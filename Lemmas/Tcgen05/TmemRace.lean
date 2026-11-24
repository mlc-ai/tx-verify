-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TmemWriters
public import Lemmas.Tcgen05.TcProgramOrder

@[expose] public section

/-! # ERR-TMEM-RACE by writer kinds

A proof tool, generic over the kernel (the kernel-free part of FA4's `Safety/TcMmaWrites.lean` and
`TcMmaReads.lean`). For a kernel without `tcgen05.cp` and `tcgen05.shift`, every Tensor Memory
write is an MMA result or a store (`tmemWrite_of_no_copy`), so the race check splits by the kinds
of the two accesses:

* **writes** (`writesSafe_of`): two MMAs of a cell, an MMA and a store of a cell, two stores of a
  cell;
* **reads** (`readsSafe_of`): an MMA's accumulator read or A read against an MMA or a store of
  its cell (no shift reads);
* the cases with one issuing thread in program order (`mm_of_po`: one thread issues every MMA of
  a cell, with one accumulator; `ss_of_po`: one thread issues every store of a cell), by the
  `tcgen05.mma` and `tcgen05.st` pipelines (`Before.of_mma_po`, `StoreDoneBefore.of_po`).

What remains for a kernel is the cross-role orders: an MMA and a store of one cell (completion
observed through a hand-off, or the store's `wait::st` before the MMA's issue), and the reads. -/

namespace PTX.TcMma
open PTX
noncomputable section

variable {L : Launch} {X : Execution}

/-- **No two Tensor Memory writes of a cell are unordered**, by writer kinds. -/
theorem writesSafe_of (hc : ∀ e c, ¬ X.CpIssue e c) (hs : ∀ e s, ¬ X.ShiftIssue e s)
    (hmm : ∀ {x y : EvId} {cell : Cell}, X.MmaCell x cell → X.MmaCell y cell →
      x = y ∨ Before L X x y ∨ Before L X y x)
    (hms : ∀ {x y : EvId} {cell : Cell}, X.MmaCell x cell → StoreCell L X y cell →
      Before L X x y ∨ StoreDoneBefore L X y x)
    (hss : ∀ {x y : EvId} {cell : Cell}, StoreCell L X x cell → StoreCell L X y cell →
      x = y ∨ StoreDoneBefore L X x y ∨ StoreDoneBefore L X y x) :
    ¬ WritesUnsafe L X := by
  refine fun hn => hn fun x y cell hx hy => ?_
  rcases tmemWrite_of_no_copy hc hs hx with hxm | hxs <;>
    rcases tmemWrite_of_no_copy hc hs hy with hym | hys
  · rcases hmm hxm hym with h | h | h
    · exact .inl h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr (.inl h))
  · rcases hms hxm hys with h | h
    · exact .inr (.inl (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
  · rcases hms hym hxs with h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inl (.inr (.inl h)))
  · rcases hss hxs hys with h | h | h
    · exact .inl h
    · exact .inr (.inl (.inr (.inl h)))
    · exact .inr (.inr (.inr (.inl h)))

/-- **Every MMA read of a cell is ordered with every write of it**, by reader and writer kinds,
for a kernel without copies and shifts. -/
theorem readsSafe_of (hc : ∀ e c, ¬ X.CpIssue e c) (hs : ∀ e s, ¬ X.ShiftIssue e s)
    (haccM : ∀ {r w : EvId} {cell : Cell}, X.MmaReadCell r cell → X.MmaCell w cell →
      r = w ∨ WriteBefore L X w r ∨ ReadBefore L X .acc r w)
    (haccS : ∀ {r w : EvId} {cell : Cell}, X.MmaReadCell r cell → StoreCell L X w cell →
      WriteBefore L X w r ∨ ReadBefore L X .acc r w)
    (haM : ∀ {r w : EvId} {cell : Cell}, X.MmaACell r cell → X.MmaCell w cell →
      r = w ∨ WriteBefore L X w r ∨ ReadBefore L X .a r w)
    (haS : ∀ {r w : EvId} {cell : Cell}, X.MmaACell r cell → StoreCell L X w cell →
      WriteBefore L X w r ∨ ReadBefore L X .a r w) :
    ¬ ReadsUnsafe L X := by
  refine fun hn => hn (readsSafe_iff.mpr ⟨fun r w cell hr hw => ?_, fun r w cell hr hw => ?_,
    fun r w cell hr _ => ?_⟩)
  · rcases tmemWrite_of_no_copy hc hs hw with hm | hst
    · exact haccM hr hm
    · exact .inr (haccS hr hst)
  · rcases tmemWrite_of_no_copy hc hs hw with hm | hst
    · exact haM hr hm
    · exact .inr (haS hr hst)
  · obtain ⟨sp, hp, -⟩ := hr
    exact (hs _ _ hp).elim

/-- **Two MMAs of a cell issued by one thread with one accumulator are one, or pipelined in
program order.** -/
theorem mm_of_po
    (hone : ∀ {x y : EvId} {cell : Cell} {d d' : Nat} {s s' : OperandSpec} {acc acc' : Bool}
      {mask mask' : List Nat}, X.MmaCell x cell → X.MmaCell y cell →
      X.MmaIssue x d s acc mask → X.MmaIssue y d' s' acc' mask' →
      x.1 < L.threads ∧ x.1 = y.1 ∧ SameAccumulator d s d' s')
    {x y : EvId} {cell : Cell} (hx : X.MmaCell x cell) (hy : X.MmaCell y cell) :
    x = y ∨ Before L X x y ∨ Before L X y x := by
  obtain ⟨dx, sx, ax, mx, -, -, hxi, -⟩ := id hx
  obtain ⟨dy, sy, ay, my, -, -, hyi, -⟩ := id hy
  obtain ⟨hg, hthr, hacc⟩ := hone hx hy hxi hyi
  obtain ⟨hg', -, hacc'⟩ := hone hy hx hyi hxi
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact .inr (.inl (Before.of_mma_po hxi hyi hg hthr hlt hacc))
  · exact .inl (Prod.ext hthr heq)
  · exact .inr (.inr (Before.of_mma_po hyi hxi hg' hthr.symm hgt hacc'))

/-- **Two stores of a cell issued by one thread are one, or ordered by the store pipeline.** -/
theorem ss_of_po
    (hone : ∀ {x y : EvId} {cell : Cell}, StoreCell L X x cell → StoreCell L X y cell →
      x.1 < L.threads ∧ x.1 = y.1)
    {x y : EvId} {cell : Cell} (hx : StoreCell L X x cell) (hy : StoreCell L X y cell) :
    x = y ∨ StoreDoneBefore L X x y ∨ StoreDoneBefore L X y x := by
  obtain ⟨a, vals, sh, j, hsx, -, -⟩ := id hx
  obtain ⟨a', vals', sh', j', hsy, -, -⟩ := id hy
  obtain ⟨hg, hthr⟩ := hone hx hy
  obtain ⟨hg', -⟩ := hone hy hx
  rcases Nat.lt_trichotomy x.2 y.2 with hlt | heq | hgt
  · exact .inr (.inl (StoreDoneBefore.of_po hsx hsy hg hthr hlt))
  · exact .inl (Prod.ext hthr heq)
  · exact .inr (.inr (StoreDoneBefore.of_po hsy hsx hg' hthr.symm hgt))

end
end PTX.TcMma
