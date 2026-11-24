-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.DStart
public import Kernels.InklingRelDecode.Proof.Bound.ProA
public import Kernels.InklingRelDecode.Proof.Bound.Sm
public import Kernels.InklingRelDecode.Proof.Bound.Epi
public import Kernels.InklingRelDecode.Proof.Interface.BoundThreads

@[expose] public section

/-!
# The rank of the default-partition thread's machine

A default-partition thread (`DComp.code`, warps 0 to 3) runs four regions in order: the common
start, the prologue, the softmax loop and the epilogue (the bridge between the loop and the
epilogue is part of the transition). The rank of a state is its region's rank shifted above the
ranks of the regions after it:

* the epilogue's own (`Bound/Epi.lean`, at most `Epi.top = 75`);
* the softmax region's, plus `Epi.top + 2`: the epilogue's first state, entered through the bridge,
  ranks below any softmax state;
* the prologue's, plus `Sm.top + Epi.top + 3`: the softmax region's first state ranks below the
  prologue's last;
* the common start's, plus the prologue's top: the prologue's first state ranks below the common
  start's last.

Every step of the machine lowers the rank by its count, with no budget. The bounds on the
softmax region's first state (`Sm.rank_le`) come from its invariant at the successor state, which
the machine's soundness gives (`Bound/Generic.lean`).

The bound does not depend on which sites of the softmax region have step lemmas: `Sm.rank` is a
function of the site's constructor and the loop counters (`Bound/Sm.lean`). The machine's
soundness, which the bound needs to follow a thread, depends on `DComp.SmObligations`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bound.DComp
open PTX PTX.Kernels.InklingRelDecode.Proof

noncomputable section
set_option maxRecDepth 100000

/-- The offset of a prologue state's rank: above the softmax region's first state. -/
def proOff : Nat := Sm.top + Epi.top + 3

/-- The offset of a common-start state's rank: above the prologue's first state. -/
def startOff : Nat := ProA.top + proOff

/-- The rank of a default-partition thread's state. -/
def rank : DComp.St → Nat
  | .dstart d => DStart.rank d + startOff
  | .pro d => ProA.rank d + proOff
  | .sm d => Sm.rank d + (Epi.top + 2)
  | .epi d => Epi.rank d

/-- The uniform bound on the initial rank. -/
def top : Nat := DStart.top + startOff

theorem rank_init (L : Launch) (g : Nat) (Q : Params) :
    rank (DComp.code L g Q).init ≤ top := by
  have := DStart.rank_le (DStart.D.start L g)
  show rank (.dstart (DStart.D.start L g)) ≤ top
  simp only [rank, top]
  omega

/-- **Every step of the default-partition thread's machine lowers the rank by its count.** The
invariants of both states are used: the softmax region's first state is bounded by its
invariant (`Sm.Inv`), and the region's own steps use theirs. -/
theorem rank_step {L : Launch} {g : Nat} {Q : Params} {d d' : DComp.St} {e : Event}
    (hI : DComp.Inv L g Q d) (hI' : DComp.Inv L g Q d')
    (h : DComp.next L g Q d e = some (some d')) :
    rank d' + (if e.counts then 1 else 0) ≤ rank d := by
  have hc := counts_le e
  cases d with
  | dstart d =>
    simp only [DComp.next, DComp.dstartNext] at h
    obtain ⟨a, ha, hf⟩ := map_inv h
    have h1 := DStart.rank_step ha
    have h2 := ProA.rank_le (ProA.D.start (DStart.inh L g Q (ProA.shW a.w)) a.w)
    split at hf
    · rename_i hs
      subst hf
      have h3 : DStart.rank a = 0 := by
        obtain ⟨s, tm⟩ := a
        simp only at hs
        subst hs
        rfl
      simp only [rank, startOff]
      omega
    · subst hf
      simp only [rank]
      omega
  | pro d =>
    obtain ⟨s, dt⟩ := d
    by_cases hs : s = .bar18
    · subst hs
      simp only [DComp.next, DComp.proNext, ite_true] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        have := Sm.rank_le hI'
        simp only [rank, ProA.rank_bar18, proOff]
        omega
      · simp at h
    · simp only [DComp.next, DComp.proNext, hs, ite_false] at h
      obtain ⟨a, ha, rfl⟩ := map_inv h
      have := ProA.rank_step ha
      simp only [rank]
      omega
  | sm d =>
    simp only [DComp.next, DComp.smNext] at h
    split at h
    · simp only [DComp.exitNext] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        have h1 := Epi.rank_le (Epi.D.startSk (Br.prm (DComp.exitIn L g d)))
        have h2 := Epi.rank_le (Epi.D.start (Br.prm (DComp.exitIn L g d)))
        simp only [rank]
        split_ifs <;> omega
      · simp at h
    · obtain ⟨a, ha, rfl⟩ := map_inv h
      have := Sm.rank_step hI ha
      simp only [rank]
      omega
  | epi d =>
    simp only [DComp.next] at h
    obtain ⟨a, ha, rfl⟩ := map_inv h
    have := Epi.rank_step ha
    simp only [rank]
    omega

end

end PTX.Kernels.InklingRelDecode.Proof.Bound.DComp
