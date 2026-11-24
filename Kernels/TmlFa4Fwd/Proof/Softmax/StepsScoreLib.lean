-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.LdWait
public import Kernels.TmlFa4Fwd.Gen.StepSoftmax
public import Kernels.TmlFa4Fwd.Proof.Softmax.Base
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Kernels.TmlFa4Fwd.Flow.Code
import Lemmas.Flow.Step.TcSteps
import Tactics.KernelRfl

@[expose] public section

/-! # The score loads: the shared reading lemma

The reading lemma of the first and the biased rounds' score loads (`sld_ok`) and the role's
override `soft_sld`; the loads themselves are one file per site (`StepsScoreFirst0.lean` and
friends), the implicit waits of a plain round in `StepsScore.lean`

Numeric states (`D.numeric`) whose local code packs the loaded scores: a score load of the first
or a biased round (no assumption makes it wait) writes its 32 destinations; the machine records
the reals they hold (`flAll`) and the code packs them into 16 pairs before the next event, which
the data table names (`valuesPairs`). A plain round's implicit wait at sub-step 1 continues into
the same packs from the loaded registers its facts name (`valuesLoaded`); after the fourth load
the code goes on to the round's maximum (`StepsPlainMax.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The facts after a score load into the registers `base` to `base + 31`: each destination
holds its loaded real, the other registers their values at the load. -/
def valueAfterLd (p : Params) (L : Launch) (g : Nat) (base : Nat) (xs : Nat → ℝ) (d : D)
    (r : Nat) : Value :=
  (((List.range 32).map fun i => (base + i, Value.float .f32 (xs i))).lookup r).getD
    (valueOfD p L g d r)

/-- A score load of the first or a biased round: the successor's facts hold after the packs
(`hl`) from the facts after the load. -/
theorem sld_ok {r : Rd} {c : Fin 4} {v : V} {gd : Option (Nat × Bool)} {ds : List Nat}
    {ta : Nat} {sh : TcShape} {base : Nat}
    (hc : kernel.code[(Site.sld r c).pc]? = some ⟨gd, .tcLd ds ta sh none⟩)
    (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : Assumptions.all.any (·.tcLdWait (Site.sld r c).pc) = false)
    (hr : r ≠ .plain)
    (hds : ds = (List.range 32).map (base + ·))
    (hlive : (liveF ((Site.sld r c).pc + 1)).all (fun q =>
      ds.contains q || (liveD (Site.sld r c).pc).contains q) = true)
    (hl : ∀ xs : Nat → ℝ, (codeD p L g).Lands (D.mk' (.sld r c) v) ((Site.sld r c).pc + 1)
      (Flow.factsFrom (liveF ((Site.sld r c).pc + 1))
        (valueAfterLd p L g base xs (D.mk' (.sld r c) v)))
      (D.mk' (if c.val = 3 then afterLoads r else .sld r (c + 1))
        { v with sv := Function.update v.sv c xs })) :
    (codeD p L g).StepOk (D.mk' (.sld r c) v) := by
  have hsucc : ∀ a vals, succ p L g (D.mk' (.sld r c) v) ⟨(Site.sld r c).pc, .tc (.ld a vals sh)⟩ =
      match flAll vals with
      | some xs => some (some (D.mk' (if c.val = 3 then afterLoads r else .sld r (c + 1))
          { v with sv := Function.update v.sv c xs }))
      | none => some none := by
    intro a vals
    cases r
    · rfl
    · rfl
    · exact absurd rfl hr
  refine PTX.Flow.Code.step_tcLd (F' := fun vals => Flow.factsFrom
      (liveF ((Site.sld r c).pc + 1))
      (valueAfterLd p L g base ((flAll vals).getD fun _ => 0) (D.mk' (.sld r c) v)))
    hc hsh hw (fun a vals => hsucc a vals) rfl rfl ?_ ?_ ?_
  · intro t vals d' hv hlen hF
    cases hx : flAll vals with
    | none => rw [hx] at hv; cases hv
    | some xs =>
      simp only [Option.getD_some]
      subst hds
      refine PTX.Flow.holds_setRegs_live hF ?_ hlen ?_ ?_
      · exact (List.nodup_map_iff (fun a b h => by omega)).mpr List.nodup_range
      · intro q hq
        simp only [List.length_map, List.length_range] at hq
        rw [flAll_get hx (by simp [hlen, hq])]
        simp only [valueAfterLd, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range hq, Option.map_some, Option.getD_some]
        rw [lookup_shift base _ (List.mem_range.mpr hq)]
        rfl
      · intro q hq hnd
        have h := List.all_eq_true.mp hlive q hq
        simp only [Bool.or_eq_true, List.contains_iff_mem] at h
        refine ⟨h.resolve_left hnd, ?_⟩
        have hn : ((List.range 32).map fun i => (base + i, Value.float .f32 (xs i))).lookup q =
            none := lookup_shift_none _ _ fun i hi e => hnd (List.mem_map.mpr ⟨i, hi, e⟩)
        simp only [valueAfterLd, hn, Option.getD_none]
  · intro vals; split <;> simp
  · intro vals d' hv
    cases hx : flAll vals with
    | none => rw [hx] at hv; cases hv
    | some xs =>
      rw [hx] at hv
      obtain rfl := Option.some.inj (Option.some.inj hv)
      simp only [Option.getD_some]
      exact hl xs

/-- A score load of the first or a biased round (an override of `soft_sites`). -/
syntax "soft_sld" : tactic
macro_rules
  | `(tactic| soft_sld) => `(tactic| (
      refine' PTX.Kernels.TmlFa4Fwd.Proof.Softmax.sld_ok ?hc ?hsh ?hw (by decide) ?hds ?hlive ?hl
      case hc => code_lookup
      case hsh => intro s hs; cases hs
      case hw => ld_wait
      case hds => rfl
      case hlive => kernel_rfl
      case hl => intro xs; lands_auto (soft_seg) (soft_inv)))

/-- The implicit wait of a plain round's score load `c` (sub-step 1): the packs of the loaded
registers, to the next load. -/
syntax "soft_sldw" : tactic
macro_rules
  | `(tactic| soft_sldw) => `(tactic| (
      refine PTX.Flow.Code.StepAt.of (fun _ => ⟨_, by code_lookup, by rfl, by trivial⟩) ?_
      refine PTX.Flow.Code.step_tcLdWait (by code_lookup)
        (by ld_wait) (fun _ => rfl)
        rfl rfl ?_
      lands_auto (soft_seg) (soft_inv)))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
