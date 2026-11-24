-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Softmax.Ledger
public import Lemmas.Flow.Counter32
public import Lemmas.Flow.Step.ShapeRegs
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' counts in closed form

The ledger's counts at every state of the softmax machine are closed forms in the state's site,
the number `rb` of biased rounds done and the number `rp` of plain rounds done (`RefQ`), and the
poll parities are closed forms in the rounds done. This file states them and proves the facts
about places that the steps use (as the correction warps' `Ref.lean`).

* **Places.** A state's position is twice its program counter, plus one at the implicit wait of
  a plain round's score load (which sits at the load's instruction after the load). A class has
  its signal points, the positions of the sites that fire its events (`ptsOf`, computed from the
  site list and `sig`). The points of a biased round (pcs 5032 to 6653) are passed once per
  biased round, those of a plain round (pcs 6661 to 7604) once per plain round. A lane without a
  tile passes no point between the request's reads and the final poll. The arrival at the stage's
  barrier freeing the bias slot (offset 336) is made by lane 0 of each warp only, so its points are
  those of that lane (`lz`). The elected lane's P-ready arrival (offset 112) is counted by the
  lane's won elections (`elect`), not by places.
* **Parities.** The first round's polls use immediates; it leaves the score, statistics and bias
  parities at 1, and every round flips them: `(1 + rb) mod 2` in a biased round, `(1 + rb + rp)
  mod 2` in a plain round and after the rounds; a lane without a tile polls with parity 1. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi sub32 xor32 andi scmpi Scan)

noncomputable section

/-! ### Places -/

/-- **The count and parity conjuncts** at state `d` with counts `n`, `rb` biased and `rp` plain
rounds done. -/
structure RefQ (p : Params) (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) (rb rp : Nat) :
    Prop where
  cnt : ∀ c, c.pointed = true → n c = passed (ptsOf (lz L g) c) d.site rb rp
  /-- The P-ready arrivals of the elected lane are its won elections. -/
  elect : n (.arrive 112) + (if d.site.isParr2 then 1 else 0) =
    n (.won 4859) + n (.won 6544) + n (.won 7449)
  barr : d.site.isBarr = true → lz L g = true
  pre : preR d.site = true → rb = 0 ∧ rp = 0
  /-- In a biased round: no plain round done, the parities, the bound and the counter
  `%r6188 = rb - nB - 1`. -/
  bias : inBias d.site.pos = true → rp = 0 ∧ parB (1 + rb) d.v ∧ (rb : Int) < nB p L g d.v ∧
    d.v.nb = i32 (rb - nB p L g d.v - 1)
  /-- In a plain round: the parities, the bound, the counter `%r6194 = rp - nP`, and all biased
  rounds done. -/
  plain : inPlain d.site.pos = true → parP (1 + rb + rp) d.v ∧ (rp : Int) < nP p L g d.v ∧
    d.v.pl = i32 (rp - nP p L g d.v) ∧ Done rb (nB p L g d.v)
  after : afterR d.site = true → d.v.ppar = i32 (((1 + rb + rp) % 2 : Nat) : Int)
  /-- At the final stores: all rounds done. -/
  fin : finR d.site = true → Done rb (nB p L g d.v) ∧ Done rp (nP p L g d.v)
  noTile : d.site.noTile = true → d.v.ppar = i32 1
  /-- A plain load's implicit wait is at sub-step 1. -/
  wait : ∀ c, d.site = .sldw c → d.k = 1

/-- **The count conjuncts of the softmax warps' reference invariant** at a counted state. -/
def RefCounts (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∃ rb rp, RefQ p L g dn.1 dn.2 rb rp

theorem setmax_first : (allPts true).all (fun q => !before .setmax q) = true := by decide +kernel

/-- The first state satisfies the count conjuncts. -/
theorem refCounts_init (p : Params) (L : Launch) (g : Nat) :
    RefCounts p L g (D.mk' .setmax {}, fun _ => 0) := by
  refine ⟨0, 0, ⟨fun c _ => ?_, rfl, fun h => absurd h (by decide), fun _ => ⟨rfl, rfl⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun c h => absurd h (by simp)⟩⟩
  show 0 = passed (ptsOf (lz L g) c) .setmax 0 0
  unfold passed
  have : (ptsOf (lz L g) c).countP (before .setmax) = 0 := by
    rw [List.countP_eq_zero]
    intro q hq
    have hq' := ptsOf_sub _ c q hq
    have hsub : allPts (lz L g) ⊆ allPts true := by
      intro x hx
      simp only [allPts, List.mem_map, List.mem_filter, Bool.and_eq_true] at hx ⊢
      obtain ⟨s, ⟨hs, h1, -⟩, rfl⟩ := hx
      exact ⟨s, ⟨hs, h1, by simp⟩, rfl⟩
    have := List.all_eq_true.mp setmax_first q (hsub hq')
    simpa using this
  rw [this]; simp

/-! ### The softmax side's obligation for the correction warps -/

/-- **The row sums passed to the correction warps are positive**: every event a lane fires at its
row-sum store (`fin 0`, `st.shared.b32 [statA + 368]`, which the correction warps read at pcs 8466
and 8762) writes the bytes of a positive `f32` real. The correction warps' reference invariant
asks this of their row-sum reads (their `Expect` at `fsum`). It is the softmax fragment's named
obligation: its proof needs the data plane in the machine's facts (the row sum of a row with a
finite maximum is at least 1, the term of its maximum element), which the numeric steps add. -/
def RowSumPos (p : Params) (L : Launch) (g : Nat) : Prop :=
  ∀ (v : V) (t : TState) (ins : Instr) (e : Event) (u : TState),
    (codeD p L g).AtD (D.mk' (.fin 0) v) t → kernel.code[(Site.fin 0).pc]? = some ins →
    Fires (Site.fin 0).pc (eventTmpl Assumptions.all L g t ins.op) e (some u) →
    ∃ a bs x, e.kind = .wr a bs ∧ rebuild 3 bs = .ok (.float .f32 x) ∧ 0 < x

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
