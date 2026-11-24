-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatVals
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Row
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Ordered
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Read
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatPos
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatSite
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StatVals

@[expose] public section

/-! # The statistics stores hold the traced row's data

The bytes of a softmax lane's statistics store are the factor, the sum or the maximum of the lane's
row data on its trace (`softRow`), once the Tensor Memory loads of the CTA before the store returned
numbers (`factor_bytes_at`, `sum_bytes_at`, `max_bytes_at`). When all loads did, these are
`SoftStats` (`softStats`); that the maximum of a valid row is finite is a hypothesis. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

private theorem handoff : SmWarp.BiasReadHandoff p L X :=
  biasReadHandoff hp hX hFw (inputsUnwritten hp (Top.noInputWrite hp hX hFw)) (biasWrites hp hX hFw)

section
variable {h i pc N : Nat} {a : Acc} {bs : List Byte} (hw : Prologue.warpIndex L h < 8)
  (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hB : LoadsBefore L X (h, i))
  (hN : SoftRounds p L h N)
include hw he hB hN

/-- **A factor store's word**, once the loads before it returned numbers. -/
theorem factor_bytes_at
    (hu : barOrd X h i (Prologue.warpIndex L h + 3) < N) :
    ∃ w, ScaleWord w ((softRow p L X h).f (barOrd X h i (Prologue.warpIndex L h + 3))) ∧
      bs = w.toBytes := by
  obtain ⟨s, rfl, hword, ⟨pl, rfl, hS, -⟩ | ⟨j, -, hj⟩⟩ := soft_stat_site hp hX hFw hw he
  · obtain ⟨u, w, hu', hbs, hr⟩ :=
      factor_write_word hp hX hFw hw (handoff hp hX hFw) pl he hB
    obtain rfl : u = barOrd X h i (Prologue.warpIndex L h + 3) := by omega
    exact ⟨w, hr, hbs⟩
  · exact absurd (hj N hN) (by omega)

/-- **The final row-sum store's word**, once the loads before it returned numbers. -/
theorem sum_bytes_at (hl : a.loc = statLoc L h 0)
    (hu : barOrd X h i (Prologue.warpIndex L h + 3) = N) :
    bs = (Value.float .f32 (softRow p L X h).rs).toBytes := by
  obtain ⟨s, rfl, hword, ⟨pl, rfl, -, hlt⟩ | ⟨j, rfl, -⟩⟩ := soft_stat_site hp hX hFw hw he
  · exact absurd (hlt N hN) (by omega)
  · have hj : j = 0 := by
      have h1 := hword.2.symm.trans hl
      fin_cases j
      · rfl
      · simp [statLoc, Softmax.statIx] at h1
    subst hj
    exact final_write_of_bias hp hX hFw hw (handoff hp hX hFw) 0 he hB

omit hN in
/-- **The final row-maximum store's word**, once the loads before it returned numbers: minus
infinity on a row without a finite score. -/
theorem max_bytes_at (hl : a.loc = statLoc L h 1) :
    bs = (if softMaxFinite p L X h then Value.float .f32 (softRow p L X h).rm
      else Assumption.erealValue .f32 ⊥).toBytes := by
  obtain ⟨s, rfl, hword, ⟨pl, rfl, -, -⟩ | ⟨j, rfl, -⟩⟩ := soft_stat_site hp hX hFw hw he
  · have h1 := hword.2.symm.trans hl
    simp [statLoc, Softmax.statIx] at h1
  · have hj : j = 1 := by
      have h1 := hword.2.symm.trans hl
      fin_cases j
      · simp [statLoc, Softmax.statIx] at h1
      · rfl
    subst hj
    exact final_write_of_bias hp hX hFw hw (handoff hp hX hFw) 1 he hB

/-- **The final row-sum store writes a nonnegative number.** -/
theorem sum_word_at (hl : a.loc = statLoc L h 0)
    (hu : barOrd X h i (Prologue.warpIndex L h + 3) = N) :
    ∃ x : ℝ, 0 ≤ x ∧ bs = (Value.float .f32 x).toBytes :=
  ⟨_, softRow_rs_nonneg hp, sum_bytes_at hp hX hFw hw he hB hN hl hu⟩

omit hN in
/-- **The final row-maximum store writes a number below `+∞`.** -/
theorem max_word_at (hl : a.loc = statLoc L h 1) :
    ∃ x : EReal, x ≠ ⊤ ∧ bs = (Assumption.erealValue .f32 x).toBytes := by
  have hb := max_bytes_at hp hX hFw hw he hB hl
  split at hb
  · exact ⟨_, EReal.coe_ne_top _, by rw [erealValue_coe]; exact hb⟩
  · exact ⟨⊥, bot_ne_top, hb⟩

end

/-- **The statistics stores hold the traced row's data**, once every load returned numbers. -/
theorem softStats
    (hLd : ∀ {e : EvId} {a : Nat} {vals : List Value}, X.TLd e a vals .s32x32b → F32s vals)
    (hFin : ∀ {h : Nat} {t : Tile}, h < L.threads → Prologue.warpIndex L h < 8 →
      tileOf p L (h / L.block) = some t → t.Valid p (Prologue.warpIndex L h / 4) (rowIx L h) →
      softMaxFinite p L X h = true) :
    SoftStats p L X (tileOf p L) (softRow p L X) where
  factor hw he _ hN hu _ hlt := by
    subst hu
    exact factor_bytes_at hp hX hFw hw he (fun _ _ _ h _ _ => hLd h) hN hlt
  sum hw he hl hN hu _ _ := sum_bytes_at hp hX hFw hw he (fun _ _ _ h _ _ => hLd h) hN hl hu
  max hw he hl _ _ hT hv := by
    have h := max_bytes_at hp hX hFw hw he (fun _ _ _ h _ _ => hLd h) hl
    rwa [hFin (Frame.lt_of_get hX he) hw hT hv] at h

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
