-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsKeep
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsLoad
public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsSteps

@[expose] public section

/-! # The bias words at every state

Every state takes the control machine's step and the facts of the bias words follow: the loads add
their word, the barrier of the entry, the last preload and the barriers of the loop pack them
(`WordsSteps`), the sites of the round keep them (`WordsKeep`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The register increase's successor is the barrier, which has no bias words. -/
theorem w_setMaxReg {d : D} (hs : d.c.site = .setMaxReg) : DataStep (codeS e L g) wF d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
  simp only [Control.next, hs, Option.some.injEq] at hnc
  subst hnc
  exact .inl fun _ _ _ => trivial

/-- **The facts of the bias words after every state.** -/
theorem words_step (d : D) (hs : d.c.site ≠ .epilogue) : DataStep (codeS e L g) wF d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hm : midB d.c.site = true
  · exact @w_mid e L g d hm t ev u d' ins hat hi hc' hf hn
  · cases hsite : d.c.site with
    | setMaxReg => exact @w_setMaxReg e L g d hsite t ev u d' ins hat hi hc' hf hn
    | bar0 => exact @w_bar0 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | pre j =>
      by_cases hj : j.val < 63
      · exact @w_pre e L g d j hsite hj t ev u d' ins hat hi hc' hf hn
      · have : j = 63 := Fin.ext (by omega)
        subst this
        exact @w_pre63 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | nxt j => exact @w_nxt e L g d j hsite t ev u d' ins hat hi hc' hf hn
    | bar21 => exact @w_bar21 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | arrive => exact @w_arrive e L g d hsite t ev u d' ins hat hi hc' hf hn
    | epilogue => exact absurd hsite hs
    | _ => exact absurd (by rw [hsite]; rfl) hm

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
