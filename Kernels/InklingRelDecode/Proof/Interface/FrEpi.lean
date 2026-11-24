-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.FrNnSt
public import Kernels.InklingRelDecode.Proof.Interface.PlFault
public import Kernels.InklingRelDecode.Proof.Interface.RdDPred
public import Kernels.InklingRelDecode.Proof.Interface.Reach

@[expose] public section

/-!
# The epilogue's `o_final` poll does not fault

`Epi.next` at the poll (`Epi.Site.wait`) is `none` where the zero test of the row sum
(`Epi.Prm.setpOk`) or, for `num_iters >= 1`, the reciprocal (`Epi.Prm.rcpOk`) has no outcome. The
registers of an epilogue state are those of the bridge from the softmax state at the loop's exit
(`Br.prm (DComp.exitIn L g d)`, `epi_pr`), whose row sum is a number (`Sm.NnInv`), so both have an
outcome (`Br.prm_setpOk`, `Br.prm_rcpOk`): `epi_wait_ok`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The states an epilogue state comes from**: the softmax region's exit (whose bridge gives its
registers) or the epilogue itself. -/
theorem dnext_epi_pr {s0 : DComp.St} {d : Epi.D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.epi d))) :
    (∃ dsm, s0 = .sm dsm ∧ d.pr = Br.prm (DComp.exitIn L g dsm)) ∨
      ∃ d0, s0 = .epi d0 ∧ Epi.next d0 e = some (some d) := by
  cases s0 with
  | dstart dd =>
    change DComp.dstartNext L g Q dd e = _ at h
    unfold DComp.dstartNext at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    split at ha <;> cases ha
  | pro dp =>
    change DComp.proNext L g Q dp e = _ at h
    unfold DComp.proNext at h
    split at h
    · split at h
      · cases h
      · cases h
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | sm d0 =>
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · unfold DComp.exitNext at h
      split at h
      · left
        refine ⟨d0, rfl, ?_⟩
        simp only [Option.some.injEq, DComp.St.epi.injEq] at h
        split at h <;> (subst h; rfl)
      · cases h
    · obtain ⟨a, -, hs⟩ := map_map_eq_some_some h
      cases hs
  | epi de =>
    change (Epi.next de e).map (Option.map DComp.St.epi) = _ at h
    obtain ⟨a, ha, hs⟩ := map_map_eq_some_some h
    simp only [DComp.St.epi.injEq] at hs
    subst hs
    exact Or.inr ⟨de, rfl, ha⟩

/-- **The registers of an epilogue state are the bridge's** from a softmax state of the same
thread. -/
theorem epi_pr {k : Nat} {d : Epi.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) :
    ∃ (k0 : Nat) (dsm : Sm.D), k0 ≤ (X.tr g).length ∧
      St Q L X g k0 = some (some (.d (.sm dsm))) ∧
        d.pr = { Br.prm (DComp.exitIn L g dsm) with bw := d.pr.bw } := by
  induction k using Nat.strong_induction_on generalizing d with
  | _ k ih =>
    rcases pred_d hk hσ with ⟨-, hs⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · cases hs
    · rcases dnext_epi_pr hn with ⟨dsm, rfl, hpr⟩ | ⟨d0, rfl, hn'⟩
      · exact ⟨k0, dsm, by omega, hσ0, by rw [hpr]⟩
      · obtain ⟨k1, dsm, hk1, h1, hpr⟩ := ih k0 (by omega) (by omega) hσ0
        refine ⟨k1, dsm, hk1, h1, ?_⟩
        calc d.pr = { d0.pr with bw := d.pr.bw } := epi_next_pr hn'
          _ = _ := by rw [hpr]

/-- **The epilogue's zero test and reciprocal have outcomes** at every epilogue state of a
launched thread. -/
theorem epi_wait_ok (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hre : Lk.SmReal Q L X) (hg : g < L.threads) {k : Nat} {d : Epi.D}
    (hσ : St Q L X g k = some (some (.d (.epi d)))) :
    d.pr.setpOk = true ∧ d.pr.rcpOk = true := by
  obtain ⟨k', hk', hσ'⟩ : ∃ k', k' ≤ (X.tr g).length ∧
      St Q L X g k' = some (some (.d (.epi d))) := by
    by_cases h : k ≤ (X.tr g).length
    · exact ⟨k, h, hσ⟩
    · exact ⟨_, le_rfl, (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k)
        (by omega)).symm.trans hσ⟩
  obtain ⟨k0, dsm, -, h0, hpr⟩ := epi_pr hk' hσ'
  obtain ⟨x, -, hx⟩ := (Lk.nnInv_state hpre hX hf hre hg h0).l
  rw [hpr]
  exact ⟨Br.prm_setpOk (DComp.exitIn L g dsm) hx, Br.prm_rcpOk (DComp.exitIn L g dsm) hx⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
