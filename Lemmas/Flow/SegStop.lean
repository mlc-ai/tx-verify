-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataOver
public import Lemmas.Flow.SegDead
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # Where a generated run ends, the thread performs an event

A proof tool, generic over the kernel. A generated run (`SegD`) ends at a checkpoint `b`; when the
instruction at `b` is an event (not local, its guard true under the run's end facts), the end
state stops (`stops_of_at`), and so the run gives a value machine's data step: every state that
local steps reach from the run's start and that performs an event holds the run's end facts, or
the thread is dead (`SegD.dataFacts`; the condition of the run is not needed: without it the
thread is dead). A run that ends at a local instruction (one cut mid-segment) must first be
composed with the next piece (`SegD.comp`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A state at an event instruction stops: its outcome is the event. -/
theorem stops_of_at {t : TState} {b : Nat} {G : List (Nat × Value)} {ins : Instr}
    (ht : At t b G) (hc : K.code[b]? = some ins) (hg : Code.GuardTrue G ins.guard)
    (hl : ins.op.isLocal = false) : Stops K A L g t :=
  ⟨_, out_event ht.2.2.2.1 (ht.1.symm ▸ hc) (Code.guardHolds_of ht.2.2.2.2 hg) hl⟩

/-- **A run to an event gives the data facts at the first stopping state**, or a dead thread. -/
theorem SegD.dataFacts {n s b : Nat} {F G F' : List (Nat × Value)} {C : Prop} {ins : Instr}
    (h : SegD K A L g n s F b G C) (hc : K.code[b]? = some ins) (hg : Code.GuardTrue G ins.guard)
    (hl : ins.op.isLocal = false) (hG : ∀ R, Holds R G → Holds R F') {u : TState}
    (hu : At u s F) :
    (∀ t', Relation.ReflTransGen (Tau K A L g) u t' → Stops K A L g t' → Holds t'.regs F') ∨
      Machine.Dead (K := K) (A := A) (L := L) (g := g) u := by
  by_cases hC : C
  · obtain ⟨t2, hr, ht2⟩ := (h u hu).1 hC
    exact .inl (Code.DataStep.of_run (run_rtg hr) (stops_of_at ht2 hc hg hl) (hG _ ht2.2.2.2.2))
  · exact .inr ((h u hu).2 hC)

end
end PTX.Flow
