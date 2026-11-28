-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQFH

@[expose] public section

/-! # A local instruction whose output is a fact of the segment

`SegQ.local1` keeps the facts of the registers the step leaves alone; `SegQ.local1x` states the
facts after the step as a whole (`Holds`), so that the written register may carry a value the
segment computes. -/

namespace PTX.Flow.TyG
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem SegQ.local1x {Q : TState → Prop} {pc : Nat} {op : Op} {F G : List (Nat × Value)}
    (hc : K.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hs : ∀ t, At t pc F → Q t → ∃ u, execLocalA A L g t op = .ok u ∧ u.pc = pc + 1 ∧
      u.sub = t.sub ∧ u.acc = t.acc ∧ u.fault = t.fault ∧ Holds u.regs G ∧
      (Tau K A L g t u → Q u)) : SegQ K A L g Q pc F (pc + 1) G := by
  intro t ht hq
  obtain ⟨u, hex, hpc, hsub, hacc, hf, hG, hQ⟩ := hs t ht hq
  have htau := tau_of_ok (A := A) (L := L) (g := g) (by rw [ht.1]; exact hc) hl ht.2.2.2.1 hex
  exact ⟨u, .single htau, ⟨hpc, hsub.trans ht.2.1, hacc.trans ht.2.2.1, hf.trans ht.2.2.2.1, hG⟩,
    hQ htau⟩

end PTX.Flow.TyG
