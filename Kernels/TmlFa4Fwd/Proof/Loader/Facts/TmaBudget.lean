-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TmaArr
import Kernels.TmlFa4Fwd.Proof.LdWarp.Fact
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's TMA arrivals and copies within its polls of the empty barrier

Standalone fact. The elections a lane won before an expect-tx arrival on the full barrier at `o`,
and the one it may still win, are at most its successful polls of the empty barrier `o + 16`; those
before a copy on it at most twice as many (`TmaBudget`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The arrival election still to come at a site. -/
def budArr (s : Site) (o : Nat) : Nat :=
  match s with
  | .te t e => if taOff t = o ∧ e.val = 0 then 1 else 0
  | .de => if o = 8 then 1 else 0
  | _ => 0

/-- The copy elections still to come at a site. -/
def budCp (s : Site) (o : Nat) : Nat :=
  match s with
  | .te t e => if taOff t = o then (if e.val = 2 then 1 else 2) else 0
  | .ta t => if taOff t = o then 2 else 0
  | .tc t c => if taOff t = o ∧ c.val = 0 then 1 else 0
  | _ => 0

/-- The edge check, for each of the four barriers. -/
def budChk (_ : Bool) (s s' : Site) : Bool :=
  [0, 8, 320, 328].all fun o =>
    match tag s s' with
    | .won pc => decide (budArr s' o + (tmaArrPts o).count pc ≤ budArr s o) &&
        decide (budCp s' o + (tcPts o).count pc ≤ budCp s o)
    | .acq o' => if o' = o + 16 then decide (budArr s' o ≤ budArr s o + 1) &&
        decide (budCp s' o ≤ budCp s o + 2) else
        decide (budArr s' o ≤ budArr s o) && decide (budCp s' o ≤ budCp s o)
    | _ => decide (budArr s' o ≤ budArr s o) && decide (budCp s' o ≤ budCp s o)

theorem bud_edges : Edges budChk := by unfold Edges AllSites; decide +kernel

/-- The fact at a counted state. -/
def TmaBudget (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∀ o ∈ [0, 8, 320, 328],
    ((tmaArrPts o).map fun pc => dn.2 (.won pc)).sum + budArr dn.1.site o ≤
      dn.2 (.acquire (bl L g (o + 16))) ∧
    ((tcPts o).map fun pc => dn.2 (.won pc)).sum + budCp dn.1.site o ≤
      2 * dn.2 (.acquire (bl L g (o + 16)))

variable {L : Launch} {g w : Nat}

theorem bud_step {dn : D × (Cnt → Nat)} {e : Event} {d' : D} (hm : Move L g w dn e d')
    (h : TmaBudget L g dn) : TmaBudget L g (d', Code.bump (cls L g) dn.2 e) := by
  obtain ⟨d, n⟩ := dn
  have hc : budChk (not14 w) d.site d'.site = true := by
    rcases hm.edge with h' | h'
    · simp [budChk, h', tag_self]
    · exact bud_edges.ok h'
  intro o ho
  have hco := List.all_eq_true.mp hc o ho
  have h0 := h o ho
  simp only [bump_tag hm] at h0 ⊢
  obtain ⟨h1, h2⟩ := h0
  revert hco
  cases tag d.site d'.site
  case won pc =>
    simp only [Tag.cnt, Option.some.injEq, Cnt.won.injEq, reduceCtorEq, ↓reduceIte, Nat.add_zero,
      Bool.and_eq_true, decide_eq_true_eq]
    intro hco
    rw [sum_map_add, sum_map_add]
    omega
  case acq o' =>
    simp only [bl] at h1 h2
    simp only [Tag.cnt, Option.some.injEq, Cnt.acquire.injEq, reduceCtorEq, ↓reduceIte,
      Nat.add_zero, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    intro hco
    by_cases hx : o' = o + 16
    · simp only [hx, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hco ⊢; omega
    · simp only [hx, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hco ⊢; omega
  all_goals
    simp only [Tag.cnt, Option.some.injEq, reduceCtorEq, ↓reduceIte, Nat.add_zero,
      Bool.and_eq_true, decide_eq_true_eq]
    intro hco
    omega

/-- **The arrivals' and copies' budgets** at every state of a loader lane. -/
theorem tma_budget {p : Params} {m : Mem0} {X : Execution} (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) : TmaBudget L g (d, LdWarp.lcn n) :=
  LdWarp.fact_at (I := fun _ => TmaBudget L g)
    (fun _ o ho => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl <;> simp [budArr, budCp])
    (fun _ _ _ _ _ _ hm h => bud_step hm h) hp hX hg hw k b d n hσ hub

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
