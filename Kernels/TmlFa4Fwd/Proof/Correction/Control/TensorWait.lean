-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Control.Machine
import Kernels.TmlFa4Fwd.Proof.Correction.Control.SpanTable
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorRld1
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorFld0
import Kernels.TmlFa4Fwd.Proof.Correction.Control.TensorFld1
import Lemmas.Flow.LoadFrameU

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
open PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {g : Nat}

theorem stepAt_fldU (st : Fin 2) (j : Fin 16) (v : V) :
    (code p L g).StepAtU ⟨.fld st j, v, 0⟩ := by
  have h : loadOk (.fld st j) (.fwl st j) false = true := by
    fin_cases st
    · exact fld_table0 j
    · exact fld_table1 j
  obtain ⟨ds, ta, hc, hw, hframe⟩ := load_of_ok h
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨a, vals, _, rfl, rfl⟩ := fires_tcLd (fun s he => by cases he) hf (hpcAt ▸ hw)
  obtain ⟨hpcSet, hsubSet, haccSet, hfaultSet⟩ := setRegs_skel (PTX.next t) ds vals
  refine .inl (.inr ⟨⟨.fwl st j, v, 0⟩, ?_⟩)
  obtain ⟨u, ht, hu⟩ := Code.landsU (C := code p L g) (d := ⟨.fwl st j, v, 0⟩)
    (u := setRegs (PTX.next t) ds vals) (by
      exact ⟨hpcSet.trans (congrArg (· + 1) hpcAt), hsubSet.trans hsubAt,
      haccSet.trans haccAt, hfaultSet.trans hfaultAt,
      holds_after_tcLd (t := t) (vs := vals) hregsAt hframe⟩)
    (cross_span (fld_span st j) _) (.inl rfl) rfl rfl
  exact ⟨u, rfl, ht, hu⟩

private theorem holds_subset {before after : Site} {val : Nat → Value} {regs : Nat → Option Value}
    (h : (liveAt after).all (liveAt before).contains = true)
    (hr : Holds regs (factsFrom (liveAt before) val)) : Holds regs (factsFrom (liveAt after) val) :=
  holds_factsFrom_mono hr fun r hp => List.contains_iff_mem.mp (List.all_eq_true.mp h r hp)

theorem stepAt_rldwU (st : Fin 2) (c : Fin 8) (v : V) :
    (code p L g).StepAtU ⟨.rldw st c, v, 1⟩ := by
  have h : loadOk (.rld st c) (.rldw st c) true = true := by
    fin_cases st
    · exact rld_table0 c
    · exact rld_table1 c
  obtain ⟨ds, ta, hc, hw, _⟩ := load_of_ok h
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain ⟨rfl, rfl⟩ := fires_tcLd_wait (hpcAt ▸ hw) (hsubAt ▸ Nat.one_ne_zero) hf
  obtain ⟨hsp, hsub⟩ := rldw_span st c
  refine .inl (.inr ⟨⟨.rst st c, v, 0⟩, ?_⟩)
  obtain ⟨u, ht, hu⟩ := Code.landsU (C := code p L g) (d := ⟨.rst st c, v, 0⟩)
    (u := { PTX.next t with sub := 0 }) (by
      exact ⟨congrArg (· + 1) hpcAt, rfl, haccAt, hfaultAt, holds_subset hsub hregsAt⟩)
    (cross_span hsp _) (.inl rfl) rfl rfl
  exact ⟨u, rfl, ht, hu⟩

theorem wait_code (st : Fin 2) (j : Fin 16) :
    kernel.code[(Site.fwl st j).pc]? = some ⟨none, .tcWaitLd⟩ := by
  have table : ∀ st j, 8000 ≤ (Site.fwl st j).pc ∧
      (match tailCode[(Site.fwl st j).pc - 8000]? with
        | some ⟨none, .tcWaitLd⟩ => true | _ => false) = true := by decide +kernel
  obtain ⟨hb, hc⟩ := table st j
  rw [← tailCode_eq, List.getElem?_drop, Nat.add_sub_of_le hb] at hc
  split at hc
  · assumption
  · cases hc

theorem stepAt_fwlU (st : Fin 2) (j : Fin 16) (v : V) :
    (code p L g).StepAtU ⟨.fwl st j, v, 0⟩ := by
  have hc := wait_code st j
  refine ⟨fun _ => ⟨_, hc, rfl, trivial⟩, ?_⟩
  intro t e u ins hat _ hins hf
  obtain ⟨hpcAt, hsubAt, haccAt, hfaultAt, hregsAt⟩ := hat
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  obtain rfl := fires_async_next (op := .tcWaitLd) trivial hf
  obtain ⟨hsp, hsub⟩ := fwl_span st j
  obtain ⟨u, ht, hu⟩ := Code.landsU (C := code p L g) (d := ⟨.fst st j 0, v, 0⟩)
    (u := PTX.next t) (by exact ⟨congrArg (· + 1) hpcAt, hsubAt, haccAt,
      hfaultAt, holds_subset hsub hregsAt⟩)
    (cross_span hsp _) (.inl rfl) rfl rfl
  exact .inl (.inr ⟨_, u, rfl, ht, hu⟩)

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
