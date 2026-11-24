-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

def pointerBroadcastInstr (src dst select : Nat) : Instr :=
  ⟨none, .warp ⟨.shfl .idx, some (.int .b 32), [some dst],
    [.reg src, .imm select, .imm 6175], some (.imm (-1))⟩⟩

structure PointerBroadcastInPrefix (l : Launch) (X : Execution)
    (g index ord pc base dst select : Nat) (F : List (Nat × Value))
    (ending : Option TState) where
  low : Value
  high : Value
  lowChecked : Bool
  highChecked : Bool
  state : TState
  first : X.get (g, index) = some ⟨pc, .shfl .idx (b32 (base % 2 ^ 32)) select 6175 low lowChecked⟩
  second : X.get (g, index + 1) =
    some ⟨pc + 1, .shfl .idx (b32 (base / 2 ^ 32)) select 6175 high highChecked⟩
  firstOrdinal : X.ShflK (g, index) ord
  secondOrdinal : X.ShflK (g, index + 1) (ord + 1)
  checkpoint : At state (pc + 2) ((dst, low) :: (dst + 1, high) :: F)
  continuation : Run kernel Assumptions.all l g state ((X.tr g).drop (index + 2)) ending

/-- An adjacent unguarded pair of pointer shuffles consumes its actual records,
even if the lane stops immediately after the second record. -/
theorem pointerBroadcastObserved {l : Launch} {X : Execution}
    {g index ord pc base src dst select : Nat} {F : List (Nat × Value)}
    (hBlock : l.block % 32 = 0) (hPc : 174 ≤ pc ∧ pc + 1 < 1906) (hSelect : select < 8)
    (hCode0 : kernel.code[pc]? = some (pointerBroadcastInstr src dst select))
    (hCode1 : kernel.code[pc + 1]? = some (pointerBroadcastInstr (src + 1) (dst + 1) select))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ dst ∧ pair.1 ≠ dst + 1)
    {s : TState} {ending : Option TState} (hs : At s pc F)
    (hLow : (src, b32 (base % 2 ^ 32)) ∈ F) (hHigh : (src + 1, b32 (base / 2 ^ 32)) ∈ F)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hRank : ((X.tr g).take index).countP Execution.isShfl = ord)
    (hMore : (X.tr g).drop index ≠ [])
    (hSecond : ∀ e, X.get (g, index) = some e → e.pc = pc →
      Execution.isShfl e = true → (X.tr g).drop (index + 1) ≠ []) :
    Nonempty (PointerBroadcastInPrefix l X g index ord pc base dst select F ending) := by
  let step := fun v (_ : Bool) => next (setReg s dst v)
  have hn : Next kernel Assumptions.all l g s s
      (.shfl .idx (b32 (base % 2 ^ 32)) select 6175 step) := by
    refine ⟨.refl,
      primingPointerWordTemplate hBlock hSelect (hs.1.symm ▸ hPc.1)
        (hs.1.symm ▸ (show pc < 1906 by omega)) hs.2.2.2.1 ?_
        (holds_mem hs.2.2.2.2 hLow)⟩
    rw [hs.1]
    exact hCode0
  obtain ⟨lo, okL, he, heRank, hAfter⟩ := hn.shuffle_at_nonempty hr hMore hRank
  rw [hs.1] at he
  have ht : At (step lo okL) (pc + 1) ((dst, lo) :: F) :=
    hs.set (fun pair hm => (hFresh pair hm).1)
  let stepHi := fun v (_ : Bool) => next (setReg (step lo okL) (dst + 1) v)
  have hnHi : Next kernel Assumptions.all l g (step lo okL) (step lo okL)
      (.shfl .idx (b32 (base / 2 ^ 32)) select 6175 stepHi) := by
    refine ⟨.refl,
      primingPointerWordTemplate hBlock hSelect (ht.1.symm ▸ (show 174 ≤ pc + 1 by omega))
        (ht.1.symm ▸ hPc.2) ht.2.2.2.1 ?_
        (holds_mem ht.2.2.2.2.2 hHigh)⟩
    rw [ht.1]
    exact hCode1
  have hAfterRank := (Flow.countP_take_succ he rfl).trans (congrArg (· + 1) hRank)
  obtain ⟨hi, okH, hf, hfRank, hTail⟩ :=
    hnHi.shuffle_at_nonempty hAfter (hSecond _ he rfl rfl) hAfterRank
  rw [ht.1] at hf
  have hu := ht.set (r := dst + 1) (v := hi) (fun pair hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact (hFresh pair hm).2)
  exact ⟨⟨lo, hi, okL, okH, _, he, hf, heRank, hfRank,
    hu.mono ⟨hu.2.2.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.2⟩, hTail⟩⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
