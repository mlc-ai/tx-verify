-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Ref
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorWait
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld1
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorFld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorFld1
import Kernels.TmlFa4Fwd.Proof.Correction.Control.VectorStore
import Kernels.TmlFa4Fwd.Proof.Correction.Control.RescaleStore
import Lemmas.Flow.LoadFrameU
import Lemmas.Flow.Step.ShapeTc

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {g : Nat} (v : V) (k : Fin 4)

theorem shape_fld (st : Fin 2) (j : Fin 16) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fld st j, v, k⟩ := by
  have h : loadOk (.fld st j) (.fwl st j) false = true := by
    fin_cases st
    · exact fld_table0 j
    · exact fld_table1 j
  obtain ⟨_, _, hc, hw, _⟩ := load_of_ok h
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  exact shape_tcLd hf (fun _ h => by cases h) (hat.1 ▸ hw)
    (fun _ _ => .inl ⟨_, _, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

private theorem rld_instr (st : Fin 2) (c : Fin 8) :
    ∃ ds ta, kernel.code[(Site.rld st c).pc]? = some ⟨none, .tcLd ds ta .s32x32b none⟩ ∧
      Assumptions.all.any (·.tcLdWait (Site.rld st c).pc) = true := by
  have h : loadOk (.rld st c) (.rldw st c) true = true := by
    fin_cases st
    · exact rld_table0 c
    · exact rld_table1 c
  obtain ⟨ds, ta, hc, hw, _⟩ := load_of_ok h
  exact ⟨ds, ta, hc, hw⟩

theorem shape_rld (st : Fin 2) (c : Fin 8) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rld st c, v, k⟩ := by
  obtain ⟨_, _, hc, hw⟩ := rld_instr st c
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hk : k = 0 := hi.elim id False.elim
  subst k
  refine shape_cont hf ⟨nofun, nofun⟩ (fun u h => ?_) (fun _ => .inr ⟨_, rfl⟩)
  obtain ⟨_, _, rfl, _⟩ := fires_tcLd_loadU (fun _ h => by cases h) (hat.1 ▸ hw) hat.2.1 h
  exact .inl ⟨_, _, _, rfl⟩

theorem shape_rldw (st : Fin 2) (c : Fin 8) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rldw st c, v, k⟩ := by
  obtain ⟨_, _, hc, hw⟩ := rld_instr st c
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  by_cases hz : t.sub = 0
  · refine shape_cont hf ⟨nofun, nofun⟩ (fun u h => ?_) (fun _ => .inr (.inr ⟨_, rfl⟩))
    obtain ⟨_, _, rfl, _⟩ := fires_tcLd_loadU (fun _ h => by cases h) (hat.1 ▸ hw) hz h
    exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact shape_tcLdWait hf (hat.1 ▸ hw) hz (.inl rfl) (fun _ => .inr (.inr ⟨_, rfl⟩))

theorem shape_fwl {m} (hp : Pre p L m) (st : Fin 2) (j : Fin 16) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fwl st j, v, k⟩ := by
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans (wait_code st j))
  exact shape_tcWaitLd hf (by rw [hp.block]) rfl

theorem shape_fst (st : Fin 2) (j : Fin 16) (h : Fin 2) :
    (code p L g).ShapeAt (Ev p L g) ⟨.fst st j h, v, k⟩ := by
  obtain ⟨a, hc, hs, _⟩ := vector_store st j h
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  exact shape_store hf hs (fun _ _ => .inl ⟨_, _, rfl⟩) (fun _ => .inr ⟨_, rfl⟩)

private theorem store_exec {r : Exec Tmpl}
    (h : ∀ m, r = .ok m → ∃ a vs u, m = .tc (.st a vs .s32x32b) u) :
    (∃ f, ofExec r = .ub f) ∨ ∃ a vs u, ofExec r = .tc (.st a vs .s32x32b) u := by
  cases r with
  | error f => exact .inl ⟨f, rfl⟩
  | ok m => exact .inr (h m rfl)

private theorem store_tmpl {t : TState} {ta : Nat} {ss : List Opnd} :
    (∃ f, tcTmpl L g t (.tcSt ta ss .s32x32b) = .ub f) ∨
    ∃ a vs u, tcTmpl L g t (.tcSt ta ss .s32x32b) = .tc (.st a vs .s32x32b) u := by
  rw [tcTmpl_tcSt_plain (fun _ h => by cases h)]
  apply store_exec
  intro m hr
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
  repeat' split at hr
  all_goals cases hr
  exact ⟨_, _, _, rfl⟩

theorem shape_rst (st : Fin 2) (c : Fin 8) :
    (code p L g).ShapeAt (Ev p L g) ⟨.rst st c, v, k⟩ := by
  obtain ⟨ta, ss, hc, hw⟩ := store_code st c
  intro t ins e o hat hi hins hf
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hw' : Assumptions.all.any (·.tcStWaitLd t.pc) = false := hat.1 ▸ hw
  simp only [eventTmpl, tcStTmpl, hw', Bool.false_eq_true, ↓reduceIte] at hf
  rcases store_tmpl (L := L) (g := g) (t := t) (ta := ta) (ss := ss) with
    ⟨f, h⟩ | ⟨a, vs, u, h⟩
  · rw [h] at hf
    exact .inr ⟨f, congrArg Event.kind hf.1⟩
  · rw [h] at hf
    exact .inl ⟨a, vs, _, congrArg Event.kind hf.1⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
