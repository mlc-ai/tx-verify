-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.StateInv

/-! # Facts along a followed thread and the thread's last state, composed

* a role table with its death obligation gives the ledger of a thread's last followed state as
  the whole trace's counts (`RoleTable.live_of_ok` into `RoleTable.end_ledger`);
* a form-A ledger relation (`Ledger.rel_step`) on concrete counts: two classes whose sum is a
  third, kept by an event of the first class. -/

namespace PTX.Tests.StateInv
open PTX PTX.Flow PTX.Frame

/-- The end-of-trace ledger of a followed thread of a table with its obligations. -/
example {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}
    {D : (g : Nat) → Code K A L g} {κ : Type} {cls : Nat → κ → Event → Bool}
    {T : RoleTable fun g => (D g).counted (cls g)} {S : Nat → Prop}
    (hC : ∀ g < L.threads, ((D g).counted (cls g)).Sound) (hX : Consistent L K A mem0 X)
    (hO : T.Ok S) (hF : T.Followed X S) {g : Nat} (hg : S g) (hgt : g < L.threads) (c : κ)
    (hc : ∀ pc, cls g c ⟨pc, .exit⟩ = false) :
    ∃ k d, stateAt (fun g => (D g).counted (cls g)) X g k = some (some d) ∧ T.J g d ∧
      (X.tr g).countP (cls g c) = d.2 c := by
  obtain ⟨k, d, hd, hJ, -, hcnt⟩ :=
    RoleTable.end_ledger hX hF hg hgt (RoleTable.live_of_ok hC hX hO hF hg)
  exact ⟨k, d, hd, hJ, hcnt c hc⟩

/-- Three classes `a = b + c` on concrete counts, kept by an event of class `b`. -/
example (e : Event) : Code.bump (fun (i : Fin 3) (_ : Event) => decide (i ≠ 2))
    (fun i => if i = 0 then 5 else if i = 1 then 5 else 0) e 0 =
    ([1, 2].map (Code.bump (fun (i : Fin 3) (_ : Event) => decide (i ≠ 2))
      (fun i => if i = 0 then 5 else if i = 1 then 5 else 0) e)).sum + 0 :=
  Ledger.rel_step _ _ e 0 [1, 2] 0 (by decide) (by decide)

end PTX.Tests.StateInv
