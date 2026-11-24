-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.TcAlt
public import Kernels.TmlFa4Fwd.Proof.LdWarp.StepAt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The electing lane's arrivals

Standalone fact. On a lane that wins every election it takes part in, the expect-tx arrivals on a
full barrier, with the one still to come in the current group, are one per successful poll of the
barrier's empty one (`arr_alt`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The arrival still to come at a site of a TMA group. -/
def arrRem (s : Site) (o : Nat) : Nat :=
  match s with
  | .te t e => if taOff t = o ∧ e.val = 0 then 1 else 0
  | .ta t => if taOff t = o then 1 else 0
  | _ => 0

/-- The edge check at sites other than elections. -/
def arrAltChk (_ : Bool) (s s' : Site) : Bool :=
  s.isTe || [0, 320, 328].all fun o =>
    arrRem s' o + (if tag s s' = .arr o then 1 else 0) ==
      arrRem s o + (if tag s s' = .acq (o + 16) then 1 else 0)

theorem arrAlt_edges : Edges arrAltChk := by unfold Edges AllSites; decide +kernel

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The electing lane's arrivals** at every state. -/
theorem arr_alt {o : Nat} (ho : o ∈ [0, 320, 328]) (hp : Pre p L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    (hwon : ∀ k pc mask inst ld, X.get (g, k) = some ⟨pc, .elect mask inst ld⟩ →
      ld = laneOf L g)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat} {b : Bool} {d : D}
    {n : Cls → Nat} (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub : n .ub = 0) :
    n (.load (.arrive (bl L g o))) + arrRem d.site o = n (.load (.acquire (bl L g (o + 16)))) := by
  refine LdWarp.step_at (w := Prologue.warpIndex L g) (I := fun _ dn =>
    dn.2 (.arrive (bl L g o)) + arrRem dn.1.site o = dn.2 (.acquire (bl L g (o + 16))))
    ?_ ?_ ?_ hp hX hg hw rfl k b d n hσ hub
  · intro _ _ _ _ _ _; rfl
  · intro k b n d e d' he hst0 hub0 hJ hF hF' hev hnu hn hm h
    simp only at h ⊢
    have hb : Code.bump (cls L g) (LdWarp.lcn n) e (.acquire (bl L g (o + 16))) =
        LdWarp.lcn n (.acquire (bl L g (o + 16))) +
          if tag d.site d'.site = .acq (o + 16) then 1 else 0 := by
      rw [bump_tag hm]
      cases tag d.site d'.site <;>
        simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.acquire.injEq, ↓reduceIte,
          Tag.acq.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
      case acqRing δ =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        have := Nat.mod_lt (LdWarp.lcn n .commit + δ) (show 0 < 3 by decide)
        have hne : ¬ 56 + 8 * ((LdWarp.lcn n .commit + δ) % 3) = o + 16 := by omega
        simp [hne]
    have ha : Code.bump (cls L g) (LdWarp.lcn n) e (.arrive (bl L g o)) =
        LdWarp.lcn n (.arrive (bl L g o)) + if tag d.site d'.site = .arr o then 1 else 0 := by
      rw [bump_tag hm]
      cases tag d.site d'.site <;>
        simp only [Tag.cnt, reduceCtorEq, Option.some.injEq, Cnt.arrive.injEq, ↓reduceIte,
          Tag.arr.injEq, bl, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff]
    rw [ha, hb]
    by_cases hte : d.site.isTe = true
    · obtain ⟨site, v, kk⟩ := d
      cases site <;> simp only [Site.isTe, Bool.false_eq_true] at hte
      rename_i t i
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp only [succ, reduceCtorEq, Option.some.injEq] at hn
      rename_i mask inst ld
      obtain rfl := hwon k pc mask inst ld he
      simp only [↓reduceIte] at hn
      subst hn
      have ht : tag (Site.te t i) (teElected ⟨.te t i, v, kk⟩ t i).site ≠ .acq (o + 16) := by
        fin_cases i <;> simp [teElected, tag]
      have ht' : tag (Site.te t i) (teElected ⟨.te t i, v, kk⟩ t i).site ≠ .arr o := by
        fin_cases i <;> simp [teElected, tag]
      have hrem : arrRem (teElected ⟨.te t i, v, kk⟩ t i).site o = arrRem (.te t i) o := by
        fin_cases i <;> simp [teElected, arrRem]
      rw [hrem]
      simp only [ht, ht', ↓reduceIte, Nat.add_zero]
      exact h
    · rcases hm.edge with hs | hs
      · simp only at hs
        rw [hs, tag_self]
        simpa using h
      · have hc := arrAlt_edges.ok hs
        simp only [arrAltChk, Bool.or_eq_true] at hc
        have hc := beq_iff_eq.mp (List.all_eq_true.mp (hc.resolve_left hte) o ho)
        omega
  · intro _ _ _ h; exact h

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
