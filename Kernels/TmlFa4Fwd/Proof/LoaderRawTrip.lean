-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
public import Kernels.TmlFa4Fwd.Flow.Code.Part007

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private theorem truncWord32 (bits : BitVec 64) : (truncBits 32 bits).toNat < 2 ^ 32 := by
  unfold truncBits
  have h := Nat.mod_lt bits.toNat (show 0 < 2 ^ 32 by decide)
  rwa [toNat_ofNat_lt (by omega)]

private theorem readWord32 {l : Launch} {g r : Nat} {t : TState} {bits : BitVec 64}
    (h : readBits l g t 32 (.reg r) = .ok bits) : bits.toNat < 2 ^ 32 := by
  have pattern {raw : Option Nat}
      (h : (match raw with
        | some n => pure (truncBits 32 (BitVec.ofNat 64 n))
        | none => throw .typeMismatch : Exec (BitVec 64)) = .ok bits) : bits.toNat < 2 ^ 32 := by
    cases raw with
    | none => cases h
    | some n => cases h; exact truncWord32 _
  simp only [readBits, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i v _
    cases v <;> first
      | exact pattern h
      | cases h; try exact truncWord32 _

/-- The loader's signed minimum records a genuine 32-bit word whenever the local step
returns, irrespective of how its two inputs were obtained. -/
theorem rawTripWrite {l : Launch} {g : Nat} {t u : TState}
    (hp : t.pc = 462) (h : Tau kernel Assumptions.all l g t u) :
    u.pc = 463 ∧ ∃ raw < 2 ^ 32, u.regs 1088 = some (b32 raw) := by
  have hc : Tau kernel [] l g t u := by
    unfold Tau at h ⊢
    rwa [← loaderOutCore (by omega) (by omega)]
  unfold Tau at hc
  have hf : t.fault = none := by
    cases hF : t.fault
    · rfl
    · simp [out, hF] at hc
  rw [out, hf, hp, Flow.code_462] at hc
  change (match (do
    let a ← readBits l g t 32 (.reg 1818)
    let b ← readBits l g t 32 (.reg 1828)
    pure (next (setReg t 1088 (.bits 32 (if compare .lt .s 32 a b then a else b)))) :
      Exec TState) with
    | .ok v => .tau v
    | .error f => .ev (.ub f)) = Out.tau u at hc
  cases hA : readBits l g t 32 (.reg 1818) with
  | error e => simp [hA, bind, Except.bind] at hc
  | ok a =>
    cases hB : readBits l g t 32 (.reg 1828) with
    | error e => simp [hA, hB, bind, Except.bind] at hc
    | ok b =>
      simp only [hA, hB, bind, Except.bind, pure, Except.pure, Out.tau.injEq] at hc
      let word := if compare .lt .s 32 a b then a else b
      have hu : u = next (setReg t 1088 (.bits 32 word)) := by
        simpa [word] using hc.symm
      have hW : word.toNat < 2 ^ 32 := by
        unfold word
        split
        · exact readWord32 hA
        · exact readWord32 hB
      refine ⟨by rw [hu]; change t.pc + 1 = 463; omega, word.toNat, hW, ?_⟩
      rw [hu]
      simp [next, setReg, b32]

private theorem tripPrefixCode (j : Fin 2) :
    ((kernel.code.drop 174).take (462 - 174)).all
      (fun i => loaderPipelineCutOp 174 462 (ringCounterSite j).branch [] i.op) = true := by
  fin_cases j <;> set_option maxRecDepth 100000 in decide +kernel

private theorem tripSuffixCode (j : Fin 2) :
    ((kernel.code.drop 463).take (477 - 463)).all
      (fun i => loaderPipelineCutOp 463 477 (ringCounterSite j).branch [1088] i.op) = true := by
  fin_cases j <;> set_option maxRecDepth 100000 in decide +kernel

private theorem tripBranchAfter (j : Fin 2) : 477 < (ringCounterSite j).branch := by
  fin_cases j <;> decide

private theorem atRawTripCut (j : Fin 2) {l : Launch} {g budget : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s 462 [])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hLoop : ∀ {raw u events visits}, raw < 2 ^ 32 → At u 477 [(1088, b32 raw)] →
      Walk kernel Assumptions.all l g u events visits →
      loaderVisitsAt (ringCounterSite j).branch visits ≤ budget) :
    loaderVisitsAt (ringCounterSite j).branch vs ≤ budget := by
  have hBound := tripBranchAfter j
  have hAdd (e : Option Event) (tail : List Visit) :
      loaderVisitsAt (ringCounterSite j).branch (visit kernel l g s e :: tail) =
        loaderVisitsAt (ringCounterSite j).branch tail := by
    simp only [loaderVisitsAt, loaderVisits, List.takeWhile_cons, visit_pc, hs.1]
    rw [ite_eq_left (show decide (174 ≤ 462 ∧ 462 < 1906) = true by decide),
      List.countP_cons, visit_pc]
    simp [hs.1, show 462 ≠ (ringCounterSite j).branch by omega]
  cases hw with
  | stop => exact Nat.zero_le _
  | tau ht hTail =>
    rw [hAdd]
    obtain ⟨hPc, raw, hRaw, hValue⟩ := rawTripWrite hs.1 ht
    have hShape := loaderPipelineStepShape (by have := hs.1; omega) (by have := hs.1; omega)
      (ringShapeOfAt hs) (.inl ⟨rfl, ht⟩)
    exact loaderPrefixThroughCheckpoint j (lower := 463) (cut := 477)
      (F := [(1088, b32 raw)]) (by decide) (by decide) hBound ⟨_, Flow.code_477, rfl⟩
      (tripSuffixCode j) (hLoop hRaw) hTail (by rw [hPc]; decide) hShape ⟨hValue, trivial⟩
  | ev he _ =>
    obtain ⟨ins, hCode, hLocal, _⟩ := estep_event_source he
    rw [hs.1, Flow.code_462] at hCode
    obtain rfl := Option.some.inj hCode
    cases hLocal
  | last => rw [hAdd]; exact Nat.zero_le _

/-- From the actual dispatch, any visit to either ring passes the 32-bit minimum
used by the guards. Earlier metadata need not be identified to bound the rings. -/
theorem loaderRingBoundFromDispatch (j : Fin 2) {l : Launch} {g budget : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hs : At s 174 [])
    (hw : Walk kernel Assumptions.all l g s es vs)
    (hLoop : ∀ {raw u events visits}, raw < 2 ^ 32 → At u 477 [(1088, b32 raw)] →
      Walk kernel Assumptions.all l g u events visits →
      loaderVisitsAt (ringCounterSite j).branch visits ≤ budget) :
    loaderVisitsAt (ringCounterSite j).branch vs ≤ budget := by
  have hBranch := tripBranchAfter j
  exact loaderPrefixThroughCheckpoint j (lower := 174) (cut := 462) (F := [])
    (by decide) (by decide) (by omega) ⟨_, Flow.code_462, rfl⟩ (tripPrefixCode j)
    (fun hAt hWalk => atRawTripCut j hAt hWalk hLoop)
    hw (by rw [hs.1]; decide) (ringShapeOfAt hs) trivial

end
end PTX.Kernels.TmlFa4Fwd.Loader
