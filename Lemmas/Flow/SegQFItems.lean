-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFCtl
public import Lemmas.Flow.OutRunCond
public import Lemmas.Flow.OutRun

@[expose] public section

/-! # A run of items under the float tag invariant

The run's condition is not assumed: the typed check shows the run succeeds, and a run that
succeeded satisfies the condition of its items (`xRun_cond`), so the values after it are the
items'. Facts `H` of registers the run does not write are carried across. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Tagged PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}
  {abs : EnvF → Op → Option (List (Nat × TagF))}

/-- **A run of items** that passes the typed check is a strict segment, from the facts by `V` to
the facts by the values after the run. -/
theorem SegQF.of_items (qt : Nat → EnvF) {pc : Nat} {items : List XItem} {liveS liveT : List Nat}
    {V : Nat → Value} {H : List (Nat × Value)} (hat : OAt K A L g pc items)
    (hloc : xLocalB items = true) (hreads : xReadsB liveS items = true)
    (hreq : xReq V items = true) (hcov : ∀ r ∈ liveT, r ∈ xWrites items ∨ r ∈ liveS)
    (hH : ∀ p ∈ H, p.1 ∉ xWrites items) (hlen : pc + items.length ≤ K.code.length)
    (hA : AbsSound A L g pc (pc + items.length) abs)
    (hc : checkF abs qt pc (pc + items.length) [] []
      ((K.code.drop pc).take (pc + items.length - pc)) = true) :
    SegQ K A L g (QTF qt) pc (factsFrom liveS V ++ H) (pc + items.length)
      (factsFrom liveT (xFinal V items) ++ H) := by
  intro t ht hq
  obtain ⟨u, hu, -, hQ, -⟩ := typedF_run (K := K) (abs := abs) qt (Ft := []) (Gk := [])
    (Nat.le_add_right _ _) hlen hA trivial hc ht hq
  rw [Nat.add_sub_cancel_left] at hu
  have hR := ht.2.2.2.2
  have hd : ∀ r ∈ liveS, t.regs r = some (V r) := fun r hr =>
    holds_mem hR (List.mem_append_left _ (mem_factsFrom hr))
  have hcode : xCodeB K t.pc items = true := by rw [ht.1]; exact hat.code
  have hrules : XRules A L g t.pc items := by rw [ht.1]; exact hat.rules
  have hcond := xRun_cond items V liveS t u hcode ht.2.2.2.1 hd hreads hreq hloc hrules hu
  obtain ⟨t', hr, hpc, hsub, hacc, hf, hfr, hw⟩ :=
    ((xRun items V liveS t hcode ht.2.2.2.1 hd hreads hreq hloc hrules).1 hcond)
  rw [hr] at hu
  obtain rfl := Option.some.inj hu
  refine ⟨t', run_rtg hr, ⟨by rw [hpc, ht.1], hsub.trans ht.2.1, hacc.trans ht.2.2.1,
    hf.trans ht.2.2.2.1, holds_of_forall fun p hp => ?_⟩, hQ⟩
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp h
    refine hw r ?_
    rcases hcov r hr' with h1 | h1
    · exact List.mem_append_left _ h1
    · exact List.mem_append_right _ h1
  · rw [hfr _ (hH p h)]
    exact holds_mem hR (List.mem_append_right _ h)

end PTX.Flow.TyG

namespace PTX.Flow
open PTX PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The first items of a run. -/
theorem OAt.left : ∀ {pc : Nat} {a b : List XItem}, OAt K A L g pc (a ++ b) → OAt K A L g pc a
  | _, [], _, _ => trivial
  | _, _ :: _, _, ⟨h, h'⟩ => ⟨h, OAt.left h'⟩

/-- The last items of a run. -/
theorem OAt.right : ∀ {pc : Nat} {a b : List XItem}, OAt K A L g pc (a ++ b) →
    OAt K A L g (pc + a.length) b
  | _, [], _, h => h
  | _, _ :: _, _, ⟨_, h'⟩ => by
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using OAt.right h'

end PTX.Flow
