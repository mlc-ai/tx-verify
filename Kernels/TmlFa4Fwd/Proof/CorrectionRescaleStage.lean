-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleNumerics

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- All eight rescale addresses are established before the two-stage loop. -/
def rescaleStageAddresses (l : Launch) (g : Nat) (stage : Fin 2) : List (Nat × Value) :=
  List.ofFn fun chunk : Fin 8 =>
    (rescaleAddressReg stage chunk, b32 (outputAddress l g stage (16 * chunk.val)))

private theorem rescaleAddresses_kept (stage : Fin 2) (chunk : Fin 8) (other : Fin 8) :
    rescaleAddressReg stage other ∉ rescaleDataRegs stage chunk ∧
      rescaleLocalKeeps stage chunk (rescaleAddressReg stage other) := by
  unfold rescaleLocalKeeps
  fin_cases stage <;> fin_cases chunk <;> fin_cases other <;> decide

private def rescaleStagePc (stage : Fin 2) (completed : Nat) : Nat :=
  if h : completed < 8 then rescaleLoadPc stage ⟨completed, h⟩ else rescaleStorePc stage 7 + 1

private theorem rescaleStageNext (stage : Fin 2) (chunk : Fin 8) :
    rescaleStorePc stage chunk + 1 = rescaleStagePc stage (chunk.val + 1) := by
  fin_cases stage <;> fin_cases chunk <;> decide

/-- The three effects of one rescale chunk are ordered on the actual lane trace. -/
def RescaleChunkEffects (l : Launch) (X : Execution) (g pos : Nat)
    (stage : Fin 2) (chunk : Fin 8) (old : Nat → ℝ) (alpha : ℝ) : Prop :=
  X.get (g, pos) = some ⟨rescaleLoadPc stage chunk,
    .tc (.ld (outputAddress l g stage (16 * chunk.val))
      (List.ofFn fun i : Fin 16 => fl (old i.val)) .s32x32b)⟩ ∧
  X.get (g, pos + 1) = some ⟨rescaleLoadPc stage chunk, .tc .waitLd⟩ ∧
  X.get (g, pos + 2) = some ⟨rescaleStorePc stage chunk,
    .tc (.st (outputAddress l g stage (16 * chunk.val))
      (List.ofFn fun i : Fin 16 => fl (old i.val * alpha)) .s32x32b)⟩

/-- The taken rescale path processes all eight chunks on one lane's actual trace and ends
at the checked wait for all stores. Each read's values come from its TMEM source witness. -/
theorem observeRescaleStage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (old : Fin 8 → Nat → ℝ) (alphaWord : Value) (alpha : ℝ)
    (ht : At t (rescaleLoadPc stage 0) (rescaleStageAddresses l g stage ++ F))
    (hFrame : ∀ chunk : Fin 8, ∀ r ∈ F.map Prod.fst, r ∉ rescaleDataRegs stage chunk ∧
      rescaleLocalKeeps stage chunk r)
    (hAlpha : t.regs (statsReg stage .alpha) = some alphaWord)
    (hAlphaBytes : alphaWord.bytes = 4)
    (hAlphaLo : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).1 = .ok alpha)
    (hAlphaHi : valFloat .f32 (splitValue 64 (joinValue alphaWord alphaWord)).2 = .ok alpha)
    (hRead : ∀ (chunk : Fin 8) vals, X.get (g, pos + 3 * chunk.val) =
      some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 16 => fl (old chunk i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ u,
      (∀ chunk : Fin 8, RescaleChunkEffects l X g (pos + 3 * chunk.val)
        stage chunk (old chunk) alpha) ∧
      X.get (g, pos + 24) = some ⟨rescaleStorePc stage 7 + 1, .tc .waitSt⟩ ∧
      At u (rescaleStorePc stage 7 + 2)
        ((rescaleAlphaPair stage, joinValue alphaWord alphaWord) ::
          (rescaleStageAddresses l g stage ++ F)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 25)) none := by
  let facts := rescaleStageAddresses l g stage ++ F
  have hKeeps (chunk : Fin 8) (r : Nat) (hm : r ∈ facts.map Prod.fst) :
      r ∉ rescaleDataRegs stage chunk ∧ rescaleLocalKeeps stage chunk r := by
    unfold facts at hm
    rw [List.map_append] at hm
    rcases List.mem_append.mp hm with h | h
    · have hs : (rescaleStageAddresses l g stage).map Prod.fst =
          List.ofFn (rescaleAddressReg stage) := List.map_ofFn
      rw [hs] at h
      obtain ⟨other, rfl⟩ := List.mem_ofFn.mp h
      exact rescaleAddresses_kept stage chunk other
    · exact hFrame chunk r h
  have walk (n : Nat) (hn : n ≤ 8) :
      ∃ s, At s (rescaleStagePc stage n) facts ∧
        (if n = 0 then s.regs (statsReg stage .alpha) = some alphaWord
          else s.regs (rescaleAlphaPair stage) = some (joinValue alphaWord alphaWord)) ∧
        (∀ chunk : Fin 8, chunk.val < n → RescaleChunkEffects l X g (pos + 3 * chunk.val)
          stage chunk (old chunk) alpha) ∧
        Run kernel Assumptions.all l g s ((X.tr g).drop (pos + 3 * n)) none := by
    induction n with
    | zero =>
      exact ⟨t, ht, hAlpha, (by omega), by simpa only [Nat.mul_zero, Nat.add_zero] using hr⟩
    | succ n ih =>
      have hN : n < 8 := by omega
      let chunk : Fin 8 := ⟨n, hN⟩
      obtain ⟨s, hS, hCoeff, hDone, hRun⟩ := ih (by omega)
      have hPc : rescaleStagePc stage n = rescaleLoadPc stage chunk := by
        unfold rescaleStagePc
        rw [dite_eq_left hN]
      rw [hPc] at hS
      have hAddr : s.regs (rescaleAddressReg stage chunk) =
          some (b32 (outputAddress l g stage (16 * chunk.val))) := by
        apply holds_mem hS.2.2.2.2
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨chunk, rfl⟩)
      obtain ⟨u, he, hw, hst, hU, hTail⟩ := observeRescaledChunk hp stage chunk (old chunk)
        alphaWord alpha hS hAddr (hKeeps chunk) (hRead chunk) hAlphaBytes hAlphaLo hAlphaHi
        hCoeff hRun
      have hAfter : rescaleStorePc stage chunk + 1 = rescaleStagePc stage (n + 1) :=
        rescaleStageNext stage chunk
      refine ⟨u, hAfter ▸ hU.mono hU.2.2.2.2.2, hU.2.2.2.2.1, ?_, ?_⟩
      · intro other hOther
        by_cases hlt : other.val < n
        · exact hDone other hlt
        · have heq : other = chunk := Fin.ext (by change other.val = n; omega)
          subst other
          exact ⟨he, hw, hst⟩
      · have hPos : pos + 3 * chunk.val + 3 = pos + 3 * (n + 1) := by
          change pos + 3 * n + 3 = _
          omega
        rw [← hPos]
        exact hTail
  obtain ⟨s, hS, hCoeff, hEffects, hRun⟩ := walk 8 (by decide)
  have hAt : At s (rescaleStorePc stage 7 + 1)
      ((rescaleAlphaPair stage, joinValue alphaWord alphaWord) :: facts) :=
    hS.mono ⟨hCoeff, hS.2.2.2.2⟩
  obtain ⟨he, hU, hTail⟩ := observeRescaleWait hp stage hAt hRun
  exact ⟨_, fun chunk => hEffects chunk chunk.isLt, he, hU, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
