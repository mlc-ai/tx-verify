-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Generated runs between the softmax machine's states

A numeric step of the data machine runs a generated piece (`Tools/out_gen.py`, `SegD` from the
facts of the run's start values to the facts of its end values) between two states. This file
moves a state's facts to a run's start facts (`holds_sub`: the run's registers are among the
state's), carries the control facts the run does not write (`SegD.frame`), and lands the end facts
on the successor's table (`land_run`: the successor's data table lists the run's end facts first,
its control registers have the start state's values). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-- Facts of a value function on fewer registers. -/
theorem holds_sub {R : Nat → Option Value} {live keys : List Nat} {V : Nat → Value}
    (h : Holds R (factsFrom live V)) (hs : keys.all (live.contains ·) = true) :
    Holds R (factsFrom keys V) :=
  holds_of_pointwise fun r hr => holds_mem h (mem_factsFrom (by
    have := List.all_eq_true.mp hs r hr; simpa using this))

/-- Facts after a write `(r0, v0)` in front of a state's facts, as facts of the updated value
function on registers among `r0` and the state's. -/
theorem holds_start {R : Nat → Option Value} {live keys : List Nat} {W : Nat → Value} {r0 : Nat}
    {v0 : Value} (h : Holds R ((r0, v0) :: factsFrom live W))
    (hk : keys.all (fun r => r == r0 || live.contains r) = true) :
    Holds R (factsFrom keys (Function.update W r0 v0)) := by
  refine holds_of_pointwise fun r hr => ?_
  by_cases e : r = r0
  · subst e; rw [Function.update_self]; exact h.1
  · rw [Function.update_of_ne e]
    have := List.all_eq_true.mp hk r hr
    simp only [Bool.or_eq_true, beq_iff_eq, e, false_or, List.contains_iff_mem] at this
    exact holds_mem h.2 (mem_factsFrom this)

/-- The first entry of a list of distinct keys is found first in the list and its extensions. -/
theorem lookup_prefix {G X : List (Nat × Value)} (hnd : (G.map Prod.fst).Nodup) {q : Nat × Value}
    (hq : q ∈ G) : (G ++ X).lookup q.1 = some q.2 := by
  induction G with
  | nil => cases hq
  | cons a G ih =>
    obtain ⟨r, v⟩ := a
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hq with rfl | hm
    · simp
    · have hne : q.1 ≠ r := fun e => hnd.1 ⟨q, hm, e⟩
      have hb : (q.1 == r) = false := by simpa using hne
      simp only [List.cons_append, List.lookup, hb]
      exact ih hnd.2 hm

/-- **The landing of a run**: the successor's facts from the run's end facts `G` and the start
state's control facts `Hc`, when the successor's value function agrees with `G` and, on the
control registers, with the start values, and its registers are among those. -/
theorem land_run {R : Nat → Option Value} {G : List (Nat × Value)} {Vt Vs : Nat → Value}
    {live ctlK : List Nat}
    (hG : ∀ q ∈ G, Vt q.1 = q.2) (hc : ∀ r ∈ ctlK, Vt r = Vs r)
    (hk : live.all (fun r => (G.map Prod.fst).contains r || ctlK.contains r) = true)
    (h1 : Holds R G) (h2 : Holds R (factsFrom ctlK Vs)) : Holds R (factsFrom live Vt) := by
  refine holds_of_pointwise fun r hr => ?_
  have h := List.all_eq_true.mp hk r hr
  simp only [Bool.or_eq_true, List.contains_iff_mem, List.mem_map] at h
  rcases h with ⟨q, hq, rfl⟩ | hc'
  · rw [hG q hq]; exact holds_mem h1 hq
  · rw [hc r hc']; exact holds_mem h2 (mem_factsFrom hc')

/-- The data machine's value function on a register its data table lists first. -/
theorem valueOfD_prefix {d : D} {G X : List (Nat × Value)} (hd : valuesData p L g d = G ++ X)
    (hnd : (G.map Prod.fst).Nodup) : ∀ q ∈ G, valueOfD p L g d q.1 = q.2 := by
  intro q hq
  simp only [valueOfD, hd, lookup_prefix hnd hq, Option.getD_some]

/-- Two states whose control tables agree have the same data machine values on control
registers. -/
theorem valueOfD_ctl_eq {d d' : D} (hv : valueOf p L g d = valueOf p L g d') {ctlK : List Nat}
    (hc : ctlK.all ctl = true) : ∀ r ∈ ctlK, valueOfD p L g d' r = valueOfD p L g d r := by
  intro r hr
  have hcr := List.all_eq_true.mp hc r hr
  rw [valueOfD_ctl d' hcr, valueOfD_ctl d hcr, hv]

/-- A `SegD` piece whose condition holds is a `Seg` piece of any length. -/
theorem seg_of_segD {K : Kernel} {A : List Assumption} {n s b : Nat} {F G : List (Nat × Value)}
    {C : Prop} (h : SegD K A L g n s F b G C) (hc : C) : ∃ n, Seg K A L g n s F b G :=
  ⟨n, h.seg hc⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
