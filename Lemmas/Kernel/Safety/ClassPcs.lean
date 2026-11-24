-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Table
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.Resource
public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The events of a class come from the sites at the class's positions

A proof tool, generic over the kernel (Inkling request L-n, the pattern of its
`Proof2/Lib/ResPcs.lean`). A class of events that only one kind of instruction fires (a Tensor
Memory resource event: `tcgen05.alloc`, `relinquish_alloc_permit`, `dealloc`; an exit: `ret`,
`exit`) is fired only at the positions where that kind occurs in the code. The positions are one
evaluated check of the decoded program (`OpPcsFast`, by `decide +kernel`), and which sites of each
machine sit at them is one decided lemma per site type (`site_pcs`).

* `RoleTable.class_pcs`: an event of the class from a thread of `S` is fired from a followed state
  whose site is at one of the positions, with the state's invariant and shape;
* `RoleTable.res_pcs`, `RoleTable.exit_pcs`: the instances for resource events and exits;
* `site_pcs`: closes `∀ s : Site, s.pc ∈ pcs → s ∈ [..]` by cases on the site and evaluation. -/

namespace PTX.Frame

open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0}
  {C : (g : Nat) → Code K A L g} {T : RoleTable C} {S : Nat → Prop} {X : Execution}

section
variable (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) (hT : T.ShapeOk S)
  (hF : T.Followed X S)
include hC hX hT hF

/-- **An event of a class fired by one kind of instruction is fired from a site at a position of
that kind**: `p` selects the instructions that can fire the class `Q` (`hop`), they are at the
positions `pcs` (`hpcs`, one evaluated check), and no event of `Q` is undefined behaviour. -/
theorem RoleTable.class_pcs (p : Op → Bool) (pcs : List Nat) (hpcs : OpPcsFast K.code p pcs = true)
    {Q : Event → Prop} (hQ : ∀ e, Q e → ∀ f, e.kind ≠ .ub f)
    (hop : ∀ pc g t op e o, Fires pc (eventTmpl A L g t op) e o → Q e → p op = true)
    {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e) (hqe : Q e) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e ∧
      (C g).pc d ∈ pcs := by
  obtain ⟨d, hσ, hJ, hi, hev⟩ := RoleTable.ev_of_ne_ub hC hX hT hF hg he (hQ e hqe)
  obtain ⟨t, ins, o, -, -, hc, hf⟩ := fired_site hC hX he hσ
  exact ⟨d, hσ, hJ, hi, hev, OpPcsFast.mem hpcs hc (hop _ g t ins.op e o hf hqe)⟩

/-- **A Tensor Memory resource event is fired from a site at a resource instruction's
position.** -/
theorem RoleTable.res_pcs (pcs : List Nat) (hpcs : OpPcsFast K.code tmemOp pcs = true)
    {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e)
    (hk : ∃ grp dst act, e.kind = .tc (.resource grp dst act)) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e ∧
      (C g).pc d ∈ pcs :=
  RoleTable.class_pcs hC hX hT hF tmemOp pcs hpcs
    (Q := fun e => ∃ grp dst act, e.kind = .tc (.resource grp dst act))
    (fun e ⟨_, _, _, h⟩ f hf => by rw [h] at hf; cases hf)
    (fun _ _ _ _ _ _ hf ⟨_, _, _, h⟩ => fires_resource_op hf h) hg he hk

/-- The `ret` and `exit` instructions. -/
def isRetOp : Op → Bool
  | .ret => true
  | .exit => true
  | _ => false

/-- **An exit is fired from a site at a `ret` or `exit` instruction's position.** -/
theorem RoleTable.exit_pcs (pcs : List Nat) (hpcs : OpPcsFast K.code isRetOp pcs = true)
    {g k : Nat} {e : Event} (hg : S g) (he : X.get (g, k) = some e) (hk : e.kind = .exit) :
    ∃ d, stateAt C X g k = some (some d) ∧ T.J g d ∧ (C g).inv d ∧ T.Ev g d e ∧
      (C g).pc d ∈ pcs :=
  RoleTable.class_pcs hC hX hT hF isRetOp pcs hpcs (Q := fun e => e.kind = .exit)
    (fun e h f hf => by rw [h] at hf; cases hf)
    (fun _ _ _ _ _ _ hf h => by rcases fires_exit_op hf h with h | h <;> rw [h] <;> rfl) hg he hk

end

/-- Closes `∀ s : Site, s.pc ∈ pcs → s ∈ l` (and `∀ s, s.pc ∈ pcs → False`-style goals with
`l = []`) by cases on the site, with the constructor's parameters quantified, and evaluation. -/
macro "site_pcs" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (repeat (rename_i j; revert j)) <;> decide +kernel))

end

end PTX.Frame
