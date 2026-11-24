-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Spec
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Lemmas.Kernel.ElectSource
import Lemmas.Kernel.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The lane of a warp that wins its elections, and the final state of a barrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The lane of warp `w` that wins every election it makes**: the lane an election of the warp
returned, or the warp's first while there is none. -/
theorem warp_winner (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {w : Nat} (hw : w < 16) :
    ∃ z, z < L.threads ∧ z / L.block = g / L.block ∧ Prologue.warpIndex L z = w ∧
      ∀ j pc mk inst ld, X.get (z, j) = some ⟨pc, .elect mk inst ld⟩ → ld = laneOf L z := by
  have hb := hp.block
  have hgr : g / 512 < L.grid := by
    have : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).mpr hg
    rwa [hb] at this
  have hbase : (g / 512 + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ hgr
  have hlane : ∀ l < 32, g / 512 * 512 + 32 * w + l < L.threads ∧
      (g / 512 * 512 + 32 * w + l) / L.block = g / L.block ∧
      Prologue.warpIndex L (g / 512 * 512 + 32 * w + l) = w ∧
      laneOf L (g / 512 * 512 + 32 * w + l) = l := by
    intro l hl
    simp only [Launch.threads, Prologue.warpIndex, laneOf, hb]
    omega
  have hsame : ∀ x y, x < L.threads → y < L.threads → x / L.block = g / L.block →
      y / L.block = g / L.block → Prologue.warpIndex L x = w → Prologue.warpIndex L y = w →
      SameWarp L x y := fun x y h1 h2 h3 h4 h5 h6 =>
    ⟨⟨h1, h2, h3.trans h4.symm⟩, by simp only [Prologue.warpIndex] at h5 h6; omega⟩
  have hfull : ∀ {x j pc mk inst ld}, X.get (x, j) = some ⟨pc, .elect mk inst ld⟩ →
      mk = 2 ^ 32 - 1 := fun {x j pc mk inst ld} he =>
    elect_full hX (show X.Elect (x, j) pc mk inst ld from he)
  by_cases hE : ∃ x j pc mk inst ld, x / L.block = g / L.block ∧ Prologue.warpIndex L x = w ∧
      X.get (x, j) = some ⟨pc, .elect mk inst ld⟩
  · obtain ⟨x, j, pc, mk, inst, ld, hxc, hx, he⟩ := hE
    obtain rfl := hfull he
    obtain ⟨-, -, hld⟩ := hX.elect.1 (x, j) pc _ inst ld he
    obtain ⟨z1, z2, z3, z4⟩ := hlane ld hld.1
    refine ⟨_, z1, z2, z3, fun j' pc' mk' inst' ld' he' => ?_⟩
    obtain rfl := hfull he'
    rw [z4]
    exact elect_leader hX he' he (hsame _ _ z1 (Frame.lt_of_get hX he) z2 hxc z3 hx)
  · push Not at hE
    obtain ⟨z1, z2, z3, -⟩ := hlane 0 (by omega)
    exact ⟨_, z1, z2, z3, fun j pc mk inst ld he => absurd he (hE _ _ _ _ _ _ z2 z3)⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
