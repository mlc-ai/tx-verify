-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs

@[expose] public section

/-! # Register facts from a liveness table

A proof tool. A site machine states the registers of an abstract state as the registers
live at its program counter, each with the value a table gives it (`factsFrom`). Writing one
register keeps every other fact (`holds_update`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- The registers `live`, each with its value under `val`. -/
def factsFrom (live : List Nat) (val : Nat → Value) : List (Nat × Value) :=
  live.map fun r => (r, val r)

theorem mem_factsFrom {live : List Nat} {val : Nat → Value} {r : Nat}
    (h : r ∈ live) : (r, val r) ∈ factsFrom live val :=
  List.mem_map.mpr ⟨r, h, rfl⟩

/-- Facts that hold register by register hold as a fact list. -/
theorem holds_of_pointwise {R : Nat → Option Value} {live : List Nat}
    {val : Nat → Value} (h : ∀ r ∈ live, R r = some (val r)) :
    Holds R (factsFrom live val) := by
  induction live with
  | nil => trivial
  | cons r rest ih =>
    exact ⟨h r (by simp), ih fun r' hr' => h r' (by simp [hr'])⟩

/-- Facts for fewer live registers with the same values. -/
theorem holds_factsFrom_mono {R : Nat → Option Value} {live live' : List Nat}
    {val : Nat → Value} (h : Holds R (factsFrom live val)) (hsub : ∀ r ∈ live', r ∈ live) :
    Holds R (factsFrom live' val) := by
  induction live' with
  | nil => trivial
  | cons r rest ih =>
    exact ⟨holds_mem h (mem_factsFrom (hsub r (by simp))),
      ih fun r' hr' => hsub r' (by simp [hr'])⟩

end PTX.Flow
