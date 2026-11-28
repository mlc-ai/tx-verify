-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Lemmas.Flow.TypedG
public import Lemmas.Flow.OutKinds
public import Kernels.InklingRelDecode.Proof.Softmax.Export.Butterfly
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand
import Kernels.InklingRelDecode.Proof.Softmax.Data.RoundNum
import Lemmas.Flow.TypedFloatH

/-! # The words of the minimum butterfly are `.f32` data

Stage `0` sends the rescale factor, a number (`alphaWord_has`); a later stage sends the minimum of
the previous stage's words (`stage_back`), which is a datum when both are (`minE_total`); the word
a lane receives is the partner's sent word (`stage_partner`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Flow.TyG Data

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A clean value that reads as an extended real is a datum of four bytes. -/
public theorem dat32_of_read {v : Value} (hc : Clean v) {x : EReal}
    (hr : Assumption.readEReal .f32 v = some (.ok x)) : Dat32 v := by
  obtain ⟨hb, hs, -⟩ := hc
  refine ⟨?_, hb, hs⟩
  by_cases hfl : ∃ x, v = .float .f32 x
  · obtain ⟨x, rfl⟩ := hfl
    exact f32Dat_float x
  rcases hc : classify .f32 v with e | c
  · exfalso
    cases v with
    | float f x =>
      have hf : f ≠ .f32 := fun h => hfl ⟨x, by rw [h]⟩
      simp [Assumption.readEReal, hf, hc, Assumption.readEReal.ofDatum] at hr
    | _ => simp [Assumption.readEReal, hc, Assumption.readEReal.ofDatum] at hr
  · exact ⟨c, hc⟩

/-- A value that reads as a number is a datum of four bytes. -/
public theorem dat32_of_fl {v : Value} (h : SK.fl.Has v) : Dat32 v :=
  dat32_of_read h.1 h.2.choose_spec

/-- A number or `-inf` is a datum of four bytes. -/
public theorem dat32_of_ni {v : Value} (h : SK.ni.Has v) : Dat32 v := by
  rcases h with ⟨hc, r, hr⟩ | rfl
  · exact dat32_of_read hc hr
  · exact dat32_bits _

/-- **The words of stage `k` of the butterfly are data**: the one a lane sends and the one it
receives. -/
public theorem stage_dat (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hR : ∀ g j, g % L.block < 128 → ∀ p ∈ roundWords X g j, SK.ni.Has p.1 ∧ SK.ni.Has p.2) :
    ∀ k, k ≤ 3 → ∀ g j a r, g % L.block < 128 → Stage X k g j a r → Dat32 a ∧ Dat32 r := by
  have send : ∀ k, k ≤ 3 → ∀ g j a r, g % L.block < 128 → Stage X k g j a r → Dat32 a := by
    intro k
    induction k with
    | zero =>
      intro _ g j a r lane st
      rw [alpha_operand hp hX st]
      exact dat32_of_fl (alphaWord_has hp (hR g j lane))
    | succ k ih =>
      intro hk g j a r lane st
      obtain ⟨j', a', r', -, st', rfl⟩ := stage_back hp hX (by omega) st
      obtain ⟨j2, r2, st2, -, low⟩ := stage_partner hp hX hf (by omega) lane st'
      obtain ⟨v, hv, hdv⟩ := minE_total (ih (by omega) g j' a' r' lane st')
        (ih (by omega) _ j2 r' r2 low st2)
      have : Lib.minWord a' r' = v := by
        unfold Lib.minWord
        rw [hv]
        rfl
      rw [this]
      exact hdv
  intro k hk g j a r lane st
  obtain ⟨j2, r2, st2, -, low⟩ := stage_partner hp hX hf hk lane st
  exact ⟨send k hk g j a r lane st, send k hk _ j2 r r2 low st2⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
