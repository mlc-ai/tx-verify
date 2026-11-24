-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPair
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVSecondSlot

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue AsyncCopy

noncomputable section

def vPacketBytes (p : Params) (batch tile tid : Nat) (pair : Fin 16) : Nat :=
  kvCopySize (p.kLength batch) tile tid pair

def vPacketFrame (p : Params) (l : Launch) (batch tile warp lane : Nat)
    (residual : Nat → Nat) : List (Nat × Value) :=
  let tid := 32 * warp + lane
  primingVPacketFrame l tid (residual lane) (vPacketBytes p batch tile tid)

def vPacketCarry (p : Params) (l : Launch) (batch tile warp lane : Nat)
    (residual : Nat → Nat) : List (Nat × Value) :=
  primingVColumn (32 * warp + lane) :: vPacketFrame p l batch tile warp lane residual

/-- The first V pair computes its column offset, which all successors retain. -/
def vPairCarry {p : Params} {l : Launch} {batch tile warp : Nat}
    (pair : Fin 16) (residual : Nat → Nat) (lane : Nat) : List (Nat × Value) :=
  if pair.val = 0 then vPacketFrame p l batch tile warp lane residual
  else vPacketCarry p l batch tile warp lane residual

/-- Every V pair reads the expected carried column, swizzle, and byte-count registers. -/
theorem vPairFrame (p : Params) (l : Launch) (batch tile warp lane : Nat)
    (pair : Fin 16) (base : Nat) (residual : Nat → Nat) :
    PrimingVPairFrame l pair base (32 * warp + lane)
      (vPacketBytes p batch tile (32 * warp + lane) pair)
      (vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
        pair residual lane) := by
  have hCore : vPacketFrame p l batch tile warp lane residual ⊆
      vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
        pair residual lane := by
    intro x hx
    by_cases hZero : pair.val = 0
    · simpa [vPairCarry, hZero] using hx
    · simp [vPairCarry, hZero, vPacketCarry, hx]
  constructor
  · by_cases hZero : pair.val = 0
    · rw [vPacketColumnInput, ite_eq_left hZero]
      apply hCore
      simp [vPacketFrame, primingVPacketFrame]
    · simp [vPacketColumnInput, vPairCarry, hZero, vPacketCarry]
  · apply hCore
    by_cases hEven : pair.val % 2 = 0
    · simp [vCopyDstReg, hEven, vPacketFrame, primingVPacketFrame]
    · have hOdd : pair.val % 2 = 1 := by omega
      simp [vCopyDstReg, hOdd, vPacketFrame, primingVPacketFrame]
  · apply hCore
    unfold vPacketFrame primingVPacketFrame
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨pair, List.mem_finRange pair, rfl⟩
  · intro fact hf
    have hKey := List.mem_map_of_mem (f := Prod.fst) hf
    have hAudit :
        ((vPairCarry (p := p) (l := l) (batch := batch) (tile := tile) (warp := warp)
            pair residual lane).map Prod.fst).all
          (fun r => decide (r ≠ vPacketShflDst pair 0 ∧ r ≠ vPacketShflDst pair 1)) = true := by
      fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)
    exact of_decide_eq_true (List.all_eq_true.mp hAudit _ hKey)
  · fin_cases pair <;> (set_option maxRecDepth 100000 in kernel_rfl)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Index the eight copy pairs that use a single saved pointer slot. -/
def vHalfPair (slot : Fin 2) (j : Fin 8) : Fin 16 :=
  ⟨8 * slot.val + j.val, by have := slot.isLt; have := j.isLt; omega⟩

def vHalfHeadPc (slot : Fin 2) : Nat := vCopyPc (vHalfPair slot 0) + 2

def vHalfFrame (p : Params) (l : Launch) (batch tile warp : Nat)
    (slot : Fin 2) (bases residual : Nat → Nat) (lane : Nat) : List (Nat × Value) :=
  primingVReloadWords slot (bases lane) ++ vPacketCarry p l batch tile warp lane residual

/-- All eight pairs in a half use the same saved pointer slot. -/
theorem vHalfSlot (slot : Fin 2) (j : Fin 8) : vPacketSlot (vHalfPair slot j) = slot := by
  apply Fin.ext
  have := j.isLt
  change (8 * slot.val + j.val) / 8 = slot.val
  omega

/-- The two actual V issues associated with one selected pair and each lane's source row. -/
def VPacketPairIssued (p : Params) (l : Launch) (X : Execution) (g batch tile warp : Nat)
    (pair : Fin 16) (bases pos : Nat → Nat) : Prop :=
  ∀ lane < 32, ∀ upper : Bool,
    let thread := warpLane l g lane
    let tid := 32 * warp + lane
    X.get (thread, pos lane + if upper then 1 else 0) =
      some ⟨vCopyPc pair + if upper then 1 else 0,
        .copy (vPacketCopySpec l thread tid (bases (vPacketSender pair lane))
          (vPacketBytes p batch tile tid pair) pair upper)⟩

/-- The exact V carry at the end of the actual K packet. -/
def vPacketAfterKFrame (p : Params) (l : Launch) (g batch head tile : Nat)
    (residual : Nat → Nat) (lane : Nat) : List (Nat × Value) :=
  primingVHandoffFrame p l head ++
    vPacketFrame p l batch tile (Prologue.warpIndex l g) lane residual

end
end PTX.Kernels.TmlFa4Fwd.Loader
