-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Lemmas.Flow.Arith32Word

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Proof PTX.Flow

/-- The four packet pairs all execute at the same counter. -/
def Site.inLoop : Site → Bool
  | .poll | .readyBar | .arrive | .page _ | .warpBar _ | .elect _ | .copy .. => true
  | _ => false

/-- Reference interpretation of the counter and limit. Before the pair load has returned
both elements, only the words already read have an interpretation. -/
def Ref (lo hi : Nat) (d : D) : Prop :=
  match d.site with
  | .dec | .first => True
  | .second => d.counter = b32 lo
  | .beginBar => d.counter = b32 lo ∧ d.limit = b32 hi
  | .endBar | .inc | .dispatch => d.limit = b32 hi
  | _ => ∃ j, lo ≤ j ∧ j < hi ∧ d.counter = b32 j ∧ d.limit = b32 hi

theorem ref_init (lo hi : Nat) : Ref lo hi {} := trivial

theorem ref_loop {lo hi : Nat} {d : D} (hr : Ref lo hi d) (hl : d.site.inLoop) :
    ∃ j, lo ≤ j ∧ j < hi ∧ d.counter = b32 j ∧ d.limit = b32 hi := by
  cases d with
  | mk s i n a b => cases s <;> first | exact hr | cases hl

theorem bits_b32 {j : Nat} (hj : j < 2 ^ 32) : bits (b32 j) = BitVec.ofNat 64 j :=
  Arith32.r32_W hj

theorem ref_counter_lt {lo hi : Nat} {d : D} (hr : Ref lo hi d) (hl : d.site.inLoop)
    (hh : hi < 2 ^ 31) : (bits d.counter).toNat < 2 ^ 31 := by
  obtain ⟨j, _, hj, hw, _⟩ := ref_loop hr hl
  rw [hw, bits_b32 (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Loader
