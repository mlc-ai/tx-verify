-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpEst
public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTab

@[expose] public section

/-! # The exponent window's facts at every state

The shuffle of pc 1838 establishes them (`x_shfl5`), the sites of the round keep them (`x_keep`),
the shuffles of pcs 2234 and 2255 and the wait of pc 2329 carry them across the update to the next
event or the barrier (`x_shfl6`, `x_shfl12`, `x_waitStO`), the barrier turns them into the 32
words (`x_bar20`); every other state has none and none of its successors has. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The sites with no facts of the exponent window, whose successors have none. -/
def xNone : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS | .shfl4 | .ldS | .waitLd | .tmemSt
  | .tmemWait | .bar21 | .arrive | .epilogue => true
  | _ => false

theorem succs_none {s z : Site} (h : xNone s = true) (hz : z ∈ succs s) :
    inRound z = false ∧ z ≠ .bar20 ∧ z ≠ .tmemSt := by
  cases s <;> simp only [xNone, succs, Bool.false_eq_true] at h hz
  all_goals (try split_ifs at hz)
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  all_goals rcases hz with rfl | rfl | rfl | rfl <;> simp [inRound]

/-- A state whose successors have no facts of the exponent window. -/
theorem x_triv {d : D} (h : xNone d.c.site = true) : DataStep (codeS e L g) (xF e L g) d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  obtain ⟨h1, h2, h3⟩ := succs_none h (next_mem (e := e) (L := L) (g := g) hnc)
  refine .inl fun _ _ _ => ?_
  simp [xF, xF0, h1, h2, h3]

/-- **The exponent window's facts after every state but the epilogue.** -/
theorem x_step (d : D) (hs : d.c.site ≠ .epilogue) : DataStep (codeS e L g) (xF e L g) d := by
  intro t ev u d' ins hat hi hc' hf hn
  by_cases hk : keepX d.c.site = true
  · exact @x_keep e L g d hk t ev u d' ins hat hi hc' hf hn
  · cases hsite : d.c.site with
    | shfl5 => exact @x_shfl5 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | shfl6 => exact @x_shfl6 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | shfl12 => exact @x_shfl12 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | waitStO => exact @x_waitStO e L g d hsite t ev u d' ins hat hi hc' hf hn
    | bar20 => exact @x_bar20 e L g d hsite t ev u d' ins hat hi hc' hf hn
    | epilogue => exact absurd hsite hs
    | _ => exact @x_triv e L g d (by
        first
          | (rw [hsite]; rfl)
          | exact absurd (by rw [hsite]; rfl) hk) t ev u d' ins hat hi hc' hf hn

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
