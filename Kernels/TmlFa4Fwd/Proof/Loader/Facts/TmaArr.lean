-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact

@[expose] public section

/-! # The loader's expect-tx arrivals on the Q and Bias stages' full barriers

Standalone fact (following does not read it). Each arrival of warp 14's TMA groups and of the
drain is issued by the lane its group's election elected, so a lane's arrivals on the barrier at
offset `o` are its won elections at the groups' election points (`tmaArrPts o`), less the one
pending at an arrival site (`pendingArr`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The groups whose election `e` precedes an expect-tx arrival on the barrier at offset `o`
(`e = 0`), and the drain's election before its arrival on the second Q stage. -/
def tmaArrPts (o : Nat) : List Nat :=
  match o with
  | 0 => [tePc 0 0]
  | 8 => [tePc 2 0, 1896]
  | 320 => [tePc 1 0, tePc 4 0, tePc 6 0]
  | 328 => [tePc 3 0, tePc 5 0]
  | _ => []

/-- The arrival pending at a state (its election won, its event not yet fired). -/
def pendingArr (s : Site) : Option Nat :=
  match s with
  | .ta t => some (taOff t)
  | .da => some 8
  | _ => none

/-- One for a pending arrival on the barrier at offset `o`. -/
def pendAt (s : Site) (o : Nat) : Nat := if pendingArr s = some o then 1 else 0

/-- The edge check, for each of the four barriers: a won election makes its arrivals pending,
the arrival fires the pending one, and no other edge changes what is pending. -/
def tmaChk (_ : Bool) (s s' : Site) : Bool :=
  [0, 8, 320, 328].all fun o =>
    match tag s s' with
    | .won pc => pendAt s' o == pendAt s o + (tmaArrPts o).count pc
    | .arr o' => if o' = o then pendAt s o == 1 && pendAt s' o == 0 else pendAt s' o == pendAt s o
    | _ => pendAt s' o == pendAt s o

theorem tma_edges : Edges tmaChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def TmaArr (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ o ∈ [0, 8, 320, 328], dn.2 (.arrive (bl L g o)) + pendAt dn.1.site o =
    ((tmaArrPts o).map fun pc => dn.2 (.won pc)).sum

/-- The won elections at the program counters of `l` after a won election at `q`. -/
theorem sum_map_add (l : List Nat) (f : Nat → Nat) (q : Nat) :
    (l.map fun pc => f pc + if q = pc then 1 else 0).sum = (l.map f).sum + l.count q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.count_cons, ih, beq_iff_eq]
    by_cases h : q = a
    · subst h; simp only [↓reduceIte]; omega
    · simp only [h, ↓reduceIte, Ne.symm h]; omega

variable {L : Launch} {g w : Nat}

theorem tma_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g w dn e d')
    (h : TmaArr L g dn) : TmaArr L g (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  have hc : tmaChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · simp [tmaChk, h', tag_self]
    · exact tma_edges.ok h'
  intro o ho
  have hco := List.all_eq_true.mp hc o ho
  have h0 := h o ho
  simp only [bump_tag hm] at h0 ⊢
  revert hco h0
  cases tag d.site d'.site <;>
    simp only [Tag.cnt, beq_iff_eq, reduceCtorEq, Option.some.injEq,
      Cnt.arrive.injEq, Cnt.won.injEq, bl, Loc.mk.injEq, true_and, ↓reduceIte, Nat.add_zero,
      Nat.add_left_cancel_iff] <;> intro hco h0
  case won pc =>
    rw [sum_map_add, ← h0, hco]; omega
  case arr o' =>
    by_cases hx : o' = o
    · subst hx; simp only [↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hco ⊢; omega
    · simp only [hx, ↓reduceIte, beq_iff_eq] at hco ⊢; omega
  all_goals omega

/-- **The expect-tx arrivals of a loader lane** at every state. -/
theorem tma_arr {p : Params} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : TmaArr L g (d, LdWarp.lcn n) :=
  LdWarp.fact_at (I := fun _ => TmaArr L g)
    (fun _ o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> rfl)
    (fun _ _ _ _ _ _ hm h => tma_step hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
