-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiSteps0
public import Kernels.InklingRelDecode.Proof.Thread.EpiPoll
public import Lemmas.Flow.Compose

@[expose] public section

/-! # The epilogue's successors, its entry and its exit

`next_pr` and `next_pr_ne` say what the successor keeps of the state's registers, and `exit` what
holds when the thread returns: it has reached the `ret` at pc 2855 (after the `tcgen05.dealloc`
for a thread of warp 0, directly for the others). The obligations of the sites are `EpiAll`'s.

`entryFacts` is the fact list at the region's first event (the `o_final` poll, pc 2565) that the
previous region (the softmax loop, through the bridge's first part) must produce, and `Premises`
what the thread must have to use it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- **The epilogue's successor keeps its registers**; the broadcast records the lane bits
(`Prm.bw`). -/
theorem next_pr {d d' : D} {e : Event} (h : next d e = some (some d')) :
    d'.pr = { d.pr with bw := d'.pr.bw } := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; unfold stNext; split <;> rfl)

/-- **Away from the broadcast the epilogue's successor keeps its registers.** -/
theorem next_pr_ne {d d' : D} {e : Event} (h : next d e = some (some d')) (hs : d.site ≠ .shfl) :
    d'.pr = d.pr := by
  unfold next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (simp only [Option.some.injEq] at h; subst h; unfold stNext; split <;> rfl)
    | (exfalso; apply hs; assumption)

/-! ### The exit -/

/-- **What holds when the thread returns**: it is at the `ret` of pc 2855 with the facts of the
exit site, after the `tcgen05.dealloc` of pc 2851 by this warp. The stores of `LsePart` and
`OPart` (pcs 2682-2845) are the region the machine does not follow; `D.word` and
`D.lseWord` state the words they write. -/
theorem exit (pr : Prm) (o : List Value) (sk : Bool) (_hi : Inv ⟨.exit, pr, o, sk⟩)
    (h : At t (Site.exit).pc (facts ⟨.exit, pr, o, sk⟩)) :
    t.pc = 2855 ∧ t.sub = 0 ∧ t.acc = [] ∧ t.fault = none :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-! ### The entry -/

/-- **The facts the region's first event needs.** At pc 2565 (the `o_final` poll) the registers
live there, valued as the epilogue's table values them. The previous region must provide each:
the softmax loop leaves `%rd8` (the thread's first output column), `%rd75` and `%rd76` (the bases
of `OPart` and `LsePart`), the row index factors `%r72`, `%r17`, `%r35`, `%r36`, `%r149`, the row
sum `%r1454`, the row-valid predicate `%p175`, the guarded-row predicate `%p3`, the thread
index `%r1`, the Tensor Memory base `%r2`, the warp index `%r3`, the column base `%r30` and the
`o_final` barrier address `%r163`; the bridge's first part adds `%r63` (the log-sum-exp),
`%p173` (`num_iters < 1`, the flag `sk`) and `%r1299` (the poll's parity word). -/
def entryFacts (pr : Prm) (sk : Bool) : List (Nat × Value) :=
  factsAt 2565 (D.entry pr sk)

/-- **The epilogue's invariant at an entry state**: the registers are numbers of their widths. -/
theorem entry_inv (pr : Prm) (hok : pr.Ok) (hla : pr.bw = 0 ∨ pr.bw = pr.w) (sk : Bool) :
    Inv (D.entry pr sk) :=
  ⟨hok, (fun h' _ => absurd h' (by simp [D.entry, LoadedSite])), (fun _ => rfl),
    (fun h' => by rcases h' with h' | h' | h' <;> simp [D.entry] at h'),
    (fun h' => absurd h' (by simp [D.entry, StoreSite])),
    (fun h' => absurd h' (by simp [D.entry])), (fun h' => by simp [D.entry] at h'),
    hla⟩

/-- **What the thread must have for the entry state to be the machine's first state**: it is at
the poll with the entry facts, the registers are the numbers the table gives them. The thread
polls at pc 2565 also for `num_iters < 1`; the zero test and the reciprocal are in `next`. -/
structure Premises (pr : Prm) (sk : Bool) (s : TState) : Prop where
  hAt : At s 2565 (entryFacts pr sk)
  /-- The registers of the table are the ones the softmax loop leaves: the thread's position and
  the launch's pointers are fixed. -/
  ok : pr.Ok
  /-- The lane bits are 0 or the warp index (the bridge leaves 0). -/
  lane : pr.bw = 0 ∨ pr.bw = pr.w

/-- The premises give the machine's first state and its invariant. -/
theorem start (pr : Prm) (sk : Bool) (s : TState) (h : Premises pr sk s) :
    At s (Site.wait).pc (facts (D.entry pr sk)) ∧ Inv (D.entry pr sk) :=
  ⟨h.hAt, entry_inv pr h.ok h.lane sk⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
