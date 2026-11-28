-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartClass
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Pairs
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsStep
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Step
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpStep
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LStep

@[expose] public section

/-! # The launch's constants at every state of the softmax

Every state of `codeS` (the machine of `Data.code` with the constants of `constF` added) takes the
control machine's step and keeps the constants: the entry's (`startF`, one region check for every
state), the derived ones (`derF`): kept by the preloads and the loop sites, established by the
barrier (`der_bar0`) and the last preload (`der_pre63`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- **The entry's constants are kept** by every state but the epilogue's. -/
theorem start_step {d : D} (hs : d.c.site ≠ .epilogue) :
    DataStep (codeS e L g) (fun _ => startF e) d := by
  have ok := siteC_ok d.c.site hs
  simp only [siteC, Bool.and_eq_true, Bool.not_eq_true'] at ok
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ok
  have key : DataStep (codeS e L g) (fun _ => startF e) d :=
    DataStep.constAny (C := codeS e L g) (sF := fun _ => startF e) (d := d)
      (A := Assumptions.all) (tab := Lib.hooks) (ivs := startIvs)
      Lib.rulesFrame hooks_any (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩
      (fun R h => ((holds_append _ _ _).mp ((holds_append _ _ _).mp h).2).1)
      (fun ins hc => ?_) start_region (fun _ _ _ x hx => hx)
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    exact h4

/-- The register increase's successor is the barrier, which has no derived constants. -/
theorem der_setMaxReg {d : D} (hs : d.c.site = .setMaxReg) :
    DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  exact .inl fun _ _ _ => trivial

/-- **The derived constants after every state.** -/
theorem der_step (d : D) : DataStep (codeS e L g) (fun d => derF e L g d.c.site) d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hs : d.c.site = .epilogue
  · exact @dataS_epilogue e L g d hs (fun d => derF e L g d.c.site) t ev u d' ins hat hi hc' hf hn
  · cases hsite : d.c.site with
    | setMaxReg => exact @der_setMaxReg e L g d hsite t ev u d' ins hat hi hc' hf hn
    | bar0 => exact @der_bar0 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | pre j =>
      by_cases hj : j.val < 63
      · exact @der_pre e L g d j hsite hj t ev u d' ins hat hi hc' hf hn
      · have : j = 63 := Fin.ext (by omega)
        subst this
        exact @der_pre63 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | _ => exact @der_loop e L g d (by rw [hsite]; rfl) hs t ev u d' ins hat hi hc' hf hn

/-- **The data step of every state with the constants**. -/
theorem dataS_step (d : D) :
    DataStep (codeS e L g) (fun d => dF L d ++ constF e L g d) d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hs : d.c.site = .epilogue
  · exact @dataS_epilogue e L g d hs (fun d => dF L d ++ constF e L g d) t ev u d' ins hat hi hc'
      hf hn
  · exact DataStep.addConst (data_step d)
      (DataStep.and (start_step hs) (DataStep.and (der_step d)
        (DataStep.and (pair_step d)
          (DataStep.and (DataStep.and (DataStep.and (words_step d hs) (w1_step d)) (x_step d hs))
            (l_step d)))))
      ins hat hi hc' hf hn

/-- **The constants hold at every state, and each state takes the control machine's step.** -/
theorem overS (e : Entry) (L : Launch) (g : Nat) :
    Code.Over (codeS e L g) (Control.code e L g) D.c (fun d => dF L d ++ constF e L g d) where
  pc _ := rfl
  sub _ := rfl
  acc _ := rfl
  inv _ := Iff.rfl
  facts _ := List.append_assoc _ _ _
  next := (over e L g).next
  stop := (over e L g).stop

theorem stepAtS (d : D) : (codeS e L g).StepAtU d :=
  Code.Over.stepAtU (overS e L g) (fun c => Control.stepAt c) (dataS_step d)

theorem erasesS (e : Entry) (L : Launch) (g : Nat) :
    Code.Erases (codeS e L g) (Control.code e L g) D.c :=
  (overS e L g).erases rfl

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
