-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Mathlib.Tactic.ByContra
public import Core.Tmem.TmemPairHistory

@[expose] public section

section
namespace PTX.Tmem.Pair
noncomputable section

/-- An access outside every published allocation of its cell's CTA, by the allocation's own event
or through its paired peer allocation (`Covers`), is unsafe. -/
theorem accessUnsafe_of_unallocated {L : Launch} {X : Execution} {e : EvId}
    {cell : TcMma.Cell} (ha : Access L X e cell)
    (hn : ¬ ∃ cta r, r ∈ X.tmemHistory cta ∧ Covers L X r cell.cta e cell.column) :
    AccessUnsafe L X :=
  fun h => hn (h e cell ha).1

end
end PTX.Tmem.Pair
end

section
/-! # Replaying a CTA's whole-allocation history

A proof tool. A history of a CTA's allocator whose warp allocates all 512 columns, relinquishes
its permit and deallocates the column it was given, in that order, with any suffix of the three
still to come and no deallocation without its allocation, replays without a fault
(`run_alloc_ok`); the whole history leaves the allocator empty (`run_alloc_released`). -/

namespace PTX.Tmem.Pair

noncomputable section

/-- The three operations of a CTA's warp: the allocation of 512 columns at `c`, the
relinquishment, the deallocation at the 32-bit base of `c`. -/
def opAct (c : Nat) : Nat → Action
  | 0 => .alloc 512 c
  | 1 => .relinquish
  | _ => .dealloc (c % 2 ^ 32) 512

/-- A replay on actions. -/
def runActs (s : State) : List Action → Outcome
  | [] => .done s
  | a :: rest => match Tmem.perform s a with
    | .done next => runActs next rest
    | .blocked => .blocked
    | .fault reason => .fault reason

/-- A replay depends only on the records' actions. -/
theorem run_acts (s : State) (H : List Requests) :
    runRequests s H = runActs s (H.map (·.action)) := by
  induction H generalizing s with
  | nil => rfl
  | cons r H ih =>
    simp only [runRequests, runActs, List.map_cons]
    cases Tmem.perform s r.action <;> simp [ih]

/-- The allocator after an allocation of all columns at `c`: done only when `c` is 0. -/
theorem perform_alloc (c : Nat) :
    Tmem.perform {} (.alloc 512 c) =
      if c = 0 then .done { previousColumns := some 512, nextLifetime := 1, live := [⟨0, c, 512⟩] }
      else .blocked := by
  by_cases hc : c = 0
  · subst hc
    simp [Tmem.perform, Tmem.validColumns, Tmem.available]
  · simp [Tmem.perform, Tmem.validColumns, Tmem.available, hc]

/-- **A CTA's history of its warp's three operations in order replays without a fault.** -/
theorem run_alloc_ok {H : List Requests} {c : Nat} {ns : List Nat}
    (hacts : H.map (·.action) = ns.map (opAct c))
    (hns : ns = [] ∨ ns = [0] ∨ ns = [1] ∨ ns = [0, 1] ∨ ns = [0, 2] ∨ ns = [0, 1, 2])
    (reason : Tmem.Error) : runRequests {} H ≠ .fault reason := by
  rw [run_acts, hacts]
  rcases hns with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.map, opAct, runActs, perform_alloc] <;>
    by_cases hc : c = 0 <;>
    simp [hc, Tmem.perform, Tmem.validColumns]

/-- **A CTA's whole history of its warp's three operations leaves its allocator empty.** -/
theorem run_alloc_released {H : List Requests} {c : Nat}
    (hacts : H.map (·.action) = [0, 1, 2].map (opAct c)) {s : State}
    (hd : runRequests {} H = .done s) : s.live = [] := by
  rw [run_acts, hacts] at hd
  simp only [List.map, opAct, runActs, perform_alloc] at hd
  by_cases hc : c = 0 <;> simp [hc, Tmem.perform, Tmem.validColumns] at hd
  subst hc
  rw [← hd]

end

end PTX.Tmem.Pair
end
