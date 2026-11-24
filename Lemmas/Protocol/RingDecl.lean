-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.PairTmaRing.Decl
public import Lemmas.Protocol.SingleTmaRing.Hyp

@[expose] public section

/-! # TMA rings as declarations

A proof tool. A TMA ring is declared once as data (`RingDecl`): a ring of a `cta_group::2` pair
(`PairTmaRing.Decl`, two producers each with its CTA's empty barrier) or a ring of one CTA
(`SingleTmaRing.Decl`, an arrival thread and a copy thread sharing one empty barrier, slots
preloaded before the loop, polls acquiring at a declared scope). The thread side of the ring is
stated once (`RingDecl.Events`), and every slot then has the hypotheses of its protocol
(`RingDecl.hyp`). The pair declaration is used unchanged, so the kernels that already declare
pair rings are not affected.

The budgets in the thread-side events (an arrival after more successful polls of the empty
barrier than earlier arrivals, a copy within its share of them, a commit after more polls of the
full barrier than earlier commits) are inequalities between counts of a thread's events. A kernel
whose machines keep these counts as ghost counters (`Code.counted`) states each budget as a
conjunct of its reference invariant at the site and transfers it to the trace by
`Frame.budget_of_counts`. -/

namespace PTX

/-- **A TMA ring as data.** -/
inductive RingDecl (nc : Nat) where
  | pair (R : PairTmaRing.Decl nc)
  | single (R : SingleTmaRing.Decl) (sc : MbarScope)

namespace RingDecl

variable {nc : Nat}

/-- The slots of a declared ring. -/
def depth : RingDecl nc → Nat
  | .pair R => R.depth
  | .single R _ => R.depth

/-- The thread-side events of a declared ring. -/
def Events (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) :
    RingDecl nc → Prop
  | .pair R => R.Events L K A X
  | .single R sc => R.Events L K A X sc

/-- The protocol hypotheses of slot `s` of a declared ring. -/
def SlotHyp (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) :
    (D : RingDecl nc) → Fin D.depth → Prop
  | .pair R, s => PairTmaRing.Hyp L K A X (R.slot s)
  | .single R sc, s => SingleTmaRing.Hyp L K A X (R.slot s) sc

/-- **Every slot of a declared ring has its protocol's hypotheses.** -/
theorem hyp {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) :
    ∀ (D : RingDecl nc), D.Events L K A X → ∀ s, D.SlotHyp L K A X s
  | .pair _, hE, s => PairTmaRing.Decl.hyp hX hE s
  | .single _ _, hE, s => SingleTmaRing.Decl.hyp hX hE s

end RingDecl
end PTX
