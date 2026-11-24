-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.FmaTotal
public import Lemmas.Flow.ArithCore
public import Lemmas.Flow.MaxCore
public import Lemmas.Flow.Ex2Core

@[expose] public section

/-! # Every outcome of the `.f32` floating rules is an `.f32` datum

A proof tool, next to `FmaTotal.lean`. A value an instruction writes is either the ideal outcome
(the value of an extended real, `erealValue`) or the Core rule's (`FVal.toValue`), and both are
`.f32` data (`F32Dat`). So a register that a chain of these instructions writes stays a datum
whatever infinities or NaNs reach it: `mulE_dat`, `subE_dat` (`mul.f32`, `sub.f32`), `maxE_dat`
(`max.f32` of two or three sources), `ex2E_dat` (`ex2.approx{.ftz}.f32` read as the exact power of
two), `coreFloat_dat` (any one-lane `.f32` rule). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section

/-- Every value of the Core rule of a one-lane `.f32` instruction is an `.f32` datum. -/
theorem coreFloat_dat {f : FloatInstr} (h1 : f.ty = ty1 .f32) {vs : List Value} {v : Value}
    (hv : coreFloat f vs = .ok v) : F32Dat v := by
  simp only [coreFloat, h1, ty1, show List.range 1 = [0] from rfl, List.mapM_cons,
    List.mapM_nil, bind, Except.bind, pure, Except.pure] at hv
  generalize (List.mapM (m := Exec) _ vs : Exec (List FVal)) = M at hv
  rcases M with e | xs
  · cases hv
  dsimp only at hv
  generalize f.lane xs = o at hv
  rcases o with _ | (_ | v0) <;> simp [throw, throwThe, MonadExceptOf.throw] at hv
  subst hv
  exact f32Dat_toValue _

theorem erealValue_map_dat {o : Option EReal} {v : Value}
    (h : o.map (fun r => (pure (erealValue .f32 r) : Exec Value)) = some (.ok v)) :
    F32Dat v := by
  obtain ⟨r, rfl⟩ := map_pure_ok h
  exact f32Dat_erealValue r

/-- **Every value of `mul.f32` is an `.f32` datum.** -/
theorem mulE_dat {fz : Bool} {va vb v : Value} (hv : mulE fz va vb = .ok v) : F32Dat v := by
  unfold mulE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    exact erealValue_map_dat hr
  · exact coreFloat_dat rfl hv

/-- **Every value of `sub.f32` is an `.f32` datum.** -/
theorem subE_dat {fz : Bool} {va vb v : Value} (hv : subE fz va vb = .ok v) : F32Dat v := by
  unfold subE at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    obtain ⟨y, -, hr⟩ := bindRead_ok hr
    exact erealValue_map_dat hr
  · exact coreFloat_dat rfl hv

/-- **Every value of `max.f32` is an `.f32` datum.** -/
theorem maxE_dat {vs : List Value} {v : Value} (hv : maxE vs = .ok v) : F32Dat v := by
  unfold maxE at hv
  split at hv
  · rename_i r hr
    subst hv
    unfold idealMax at hr
    split at hr
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      obtain ⟨y, -, hr⟩ := bindRead_ok hr
      simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      rw [← hr]
      exact f32Dat_erealValue _
    · obtain ⟨x, -, hr⟩ := bindRead_ok hr
      obtain ⟨y, -, hr⟩ := bindRead_ok hr
      obtain ⟨z, -, hr⟩ := bindRead_ok hr
      simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
      rw [← hr]
      exact f32Dat_erealValue _
    · simp [throw, throwThe, MonadExceptOf.throw] at hr
  · exact coreFloat_dat rfl hv

/-- **Every value of `ex2.approx{.ftz}.f32`, read as the exact power of two, is an `.f32`
datum.** -/
theorem ex2E_dat {fz : Bool} {va v : Value} (hv : ex2E fz va = .ok v) : F32Dat v := by
  unfold ex2E at hv
  split at hv
  · rename_i r hr
    subst hv
    obtain ⟨x, -, hr⟩ := bindRead_ok hr
    simp only [Option.some.injEq, pure, Except.pure, Except.ok.injEq] at hr
    rw [← hr]
    exact f32Dat_float _
  · exact coreFloat_dat rfl hv

end
end PTX.Flow
