-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc
public import Kernels.FlashAttn4Fwd.Proof.Thread.Mma

@[expose] public section

/-! # What the thread layer exports for the MMAs' operands and accumulators

The sources of the MMAs' operands and accumulators (`TcMmaSources*`) need these facts of single
threads, beside the score, accumulator and second P-ready facts:

* **MMA issue** (`mma_desc`): every MMA has the eight zero lane masks; a QK MMA (A in shared
  memory) has the QK instruction descriptor and a PV MMA (A in Tensor Memory) the PV one
  (`Mma.qkIdesc`, `Mma.pvIdesc` decoded for `cta_group::2`, `kind::f16`), the constants of the
  MMA sites' templates (`Mma.qk_isMma`, `Mma.pv_isMma`).
* **Accumulation** (`qk_acc`, `pv_acc`): the enable-input-D operand is false on the first QK MMA of
  every score tile and on the first PV MMA of every item. So an accumulating QK MMA follows a QK MMA
  of the same tile writing the same cells (no S-full commit between them), and an accumulating PV
  MMA follows a PV MMA of its tile or of the tile before writing the same cells.
* **Stored values** (`soft_f16`, `corr_f32`): a softmax store writes packed pairs of FP16 values
  (`cvt.rn.f16x2.f32`, read as exact by the kernel's assumption `fa4-fwd-ideal-arith`); a correction
  store writes single-precision floats (the rescaled accumulator) when the thread's earlier loads
  and statistics reads were finite.
* **P is stored before it is published** (`soft_low`, `soft_high`): a softmax thread's arrival of
  tile `u` on its stage's P-ready object comes after its stores of tile `u` of every column of its
  row of `P` below `112`; its warp barrier of tile `u` (the `u`-th, `warpBars = u`) comes after
  its stores of tile `u` of the columns `112 …`.

The facts are from the run invariants of the MMA warp (`Mma.Counts`: the enable operands of the
MMA blocks) and of the softmax and correction (`Softmax.Counts`, `Correction.Counts`: the stored
registers and the stores of a tile), and the constants of the MMA sites. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The thread layer's facts for the MMAs' operands and accumulators. -/
structure TcMmaThreadFacts (L : Launch) (X : Execution) : Prop where
  /-- An MMA's lane masks are zero; its descriptor is the QK one when A is in shared memory and
  the PV one when A is in Tensor Memory. -/
  mma_desc : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → mask = List.replicate 8 0 ∧
      (s.aTmem = none → decode .two false .f16 Mma.qkIdesc = some s.descriptor) ∧
      (s.aTmem.isSome = true → decode .two false .f16 Mma.pvIdesc = some s.descriptor)
  /-- No MMA reuses a collector buffer (the kernel's MMAs name no `.collector` qualifier). -/
  mma_collector : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {acc : Bool} {mask : List Nat},
    X.MmaIssue i d s acc mask → s.collector.a.reuses = false ∧ s.collector.b.reuses = false
  /-- An accumulating MMA writing a cell of stage `st`'s scores follows an MMA of its thread
  writing the cell after as many commits to the stage's S-full object. -/
  qk_acc : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat},
    X.MmaIssue i d s true mask → X.MmaCell i cell → InS st cell →
      ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ sCommits L X i.1 st k = sCommits L X i.1 st i.2
  /-- An accumulating MMA writing a cell of stage `st`'s accumulator follows an MMA of its thread
  writing the cell with at most one poll of the stage's P-ready object fewer before it. -/
  pv_acc : ∀ {i : EvId} {d : Nat} {s : OperandSpec} {mask : List Nat} {cell : Cell} {st : Nat},
    X.MmaIssue i d s true mask → X.MmaCell i cell → InO st cell →
      ∃ k < i.2, X.MmaCell (i.1, k) cell ∧ pPolls L X i.1 st i.2 ≤ pPolls L X i.1 st k + 1
  /-- A softmax store writes packed pairs of FP16 values, once the thread's earlier Tensor Memory
  loads returned single-precision floats (the stored values are computed from them). -/
  soft_f16 : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → warpOf L h < 8 →
    X.TSt (h, i) a vals .s32x32b →
    (∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
    ∀ v ∈ vals, ∃ x y : ℝ, v = .pair (.float .f16 x) (.float .f16 y)
  /-- A correction store writes single-precision floats, once the thread's earlier Tensor Memory
  loads returned single-precision floats and its earlier reads read finite statistics words (its
  stored values are computed from them). -/
  corr_f32 : ∀ {h i a : Nat} {vals : List Value}, h < L.threads → 8 ≤ warpOf L h →
    warpOf L h < 12 → X.TSt (h, i) a vals .s32x32b →
    (∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (h, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') →
    (∀ k < i, ∀ pc (ac : Acc) (bs : List (Option Byte)),
      X.get (h, k) = some ⟨pc, .rd ac bs⟩ → ∃ x, F32Read bs x) → F32s vals
  /-- A softmax arrival on its stage's P-ready object of tile `u` comes after the thread's stores
  of tile `u` of every cell of its row of `P` below column `112`. -/
  soft_low : ∀ {h e pc tx cnt col : Nat} {rel : Bool} {sc : MbarScope}, h < L.threads →
    warpOf L h < 8 →
    X.get (h, e) = some ⟨pc,
      .arrive (pReadyBar L (leadCta (ctaOf L h)) (warpOf L h / 4)) tx cnt rel sc⟩ →
    InP (warpOf L h / 4) (tcDataCell32 L h 0 col) →
    ¬ InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 col) →
    ∃ k a j, ∃ vals : List Value, k < e ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (warpOf L h / 4) k = pArr L X h (warpOf L h / 4) e + 1
  /-- A softmax thread's warp barrier of tile `u` (the `u`-th) comes after its stores of tile `u`
  of every cell of its row of `P` from column `112`. -/
  soft_high : ∀ {h b m inst col : Nat}, h < L.threads → warpOf L h < 8 → X.WarpBar (h, b) m inst →
    InP (warpOf L h / 4) (tcDataCell32 L h 0 col) →
    InPHigh (warpOf L h / 4) (tcDataCell32 L h 0 col) →
    ∃ k a j, ∃ vals : List Value, k < b ∧ X.TSt (h, k) a vals .s32x32b ∧ j < vals.length ∧
      tcDataCell32 L h a j = tcDataCell32 L h 0 col ∧
      sPolls L X h (warpOf L h / 4) k = warpBars X h b + 1

end
end PTX.Kernels.FlashAttn4Fwd.Proof
