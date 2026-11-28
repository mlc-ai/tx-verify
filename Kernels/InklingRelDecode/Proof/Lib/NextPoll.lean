-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.NextEv
import Lemmas.Flow.ReturningPrefix

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Sched

variable {K : Kernel} {A : List Assumption} {L : Launch} {m : Mem0}
  {X : Execution} {g pc q : Nat} {l : Loc} {sc : MbarScope}

private theorem wait_template {t : TState} {o : Option TState} {v : Tmpl}
    (hf : Fires t.pc v ⟨pc, .wait l q false true sc⟩ o) :
    ∃ k, t.pc = pc ∧ v = .wait l q k true sc := by
  cases v <;> simp_all [Fires]

/-- A witnessed next poll fixes its instruction, object, scope and parity for both
local outcomes, even when the witnessing execution changed other lanes. -/
public theorem next_poll_blocked {M : Timed K A L} (he : NextEv L K A m X g
    ⟨pc, .wait l q false true sc⟩) (hb : WaitBlk M X g l q) : PollBlocked M X g := by
  refine ⟨l, pc, q, ?_, hb⟩
  intro t ht ok
  obtain ⟨Y, hY, hpre, hget⟩ := he
  obtain ⟨o, hrun⟩ := hY.thr g (Frame.lt_of_get hY hget)
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp hget
  have hs := List.take_append_drop (X.tr g).length (Y.tr g)
  rw [hpre, List.drop_eq_getElem_cons hlt, hv] at hs
  rw [← hs] at hrun
  have htail := ht.after_returned_prefix hrun
  generalize (Y.tr g).drop ((X.tr g).length + 1) = rest at htail
  cases htail with
  | step hl ef _ =>
    obtain ⟨v, hout, hf⟩ := ef
    obtain ⟨k, hpc, rfl⟩ := wait_template hf
    exact ⟨_, k ok, sc, hl, _, hout, ok, by rw [hpc], rfl⟩
  | last hl ef =>
    obtain ⟨v, _, hf⟩ := ef
    obtain ⟨k, _, rfl⟩ := wait_template hf
    obtain ⟨_, _, h⟩ := hf
    cases h

end PTX.Kernels.InklingRelDecode.Proof.Lib
