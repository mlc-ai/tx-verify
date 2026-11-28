-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.LInit
public import Kernels.InklingRelDecode.Proof.Softmax.Data.LCrossStep

@[expose] public section

/-! # The running sum's facts at every state

The register 1915 (the running sum) and, between its addition and the update, register 1531 (the
round's row sum): established by the start of the loop (`l_bar0`, `l_pre63`), carried by the
sites of the loop (`l_keep`) and across the update (`l_shfl6`, `l_shfl12`, `l_waitStO`); the sites
before the loop hold none. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The epilogue state has no successor. -/
theorem dataS_epilogue {d : D} (hs : d.c.site = .epilogue) {f : D → List (Nat × Value)} :
    DataStep (codeS e L g) f d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, -⟩ := succ_inv hn
  simp [Control.next, hs] at hnc

theorem lFS_nil {z : Site} (h : lK z = []) (v : Vals) : lFS z v = [] := by
  cases z <;> simp [lFS, lK] at h ⊢ <;> split at h <;> simp at h

/-- A state whose successors hold no running-sum facts. -/
theorem l_triv {d : D} (h : ∀ z ∈ succs d.c.site, lK z = []) : DataStep (codeS e L g) lF d := by
  intro t ev u d' ins hat hi hc' hf hn
  obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
  have := lFS_nil (h _ (next_mem (e := e) (L := L) (g := g) hnc)) (record L d ev c'.site)
  exact .inl fun _ _ _ => by simp only [lF, this]; trivial

/-- **The running sum's facts after every state.** -/
theorem l_step (d : D) : DataStep (codeS e L g) lF d := by
  by_cases hs : d.c.site = .epilogue
  · exact dataS_epilogue hs
  cases hsite : d.c.site with
  | setMaxReg => exact l_triv (by simp [hsite, succs, lK])
  | bar0 => exact l_bar0 hsite
  | pre j =>
    by_cases hj : j.val < 63
    · exact l_triv (by simp [hsite, succs, lK, show j.val + 1 < 64 by omega])
    · have : j = 63 := Fin.ext (by omega)
      subst this
      exact l_pre63 hsite
  | shfl6 => exact l_shfl6 hsite
  | shfl12 => exact l_shfl12 hsite
  | waitStO => exact l_waitStO hsite
  | epilogue => exact absurd hsite hs
  | _ => exact l_keep (by rw [hsite]; rfl)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
