-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Rescale
import Lemmas.Flow.Final

@[expose] public section

/-! # Completion of a softmax rescale store -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleHistory

open PTX PTX.Flow

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg0.D} {k : Fin 4}
    {words : List Value} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hstate : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleStore k) (hst : X.TSt (g, i) (64 * k.val) words .s32x32b)
include hpre hX hs hstate hsite hst

/-- When the trace extends past an actual rescale store, the next event completes the store. -/
theorem wait_next_state (hlen : i + 1 < (X.tr g).length) :
    ∃ tag q, X.get (g, i + 1) = some ⟨tag, .tc .waitSt⟩ ∧
      Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) ∧
      q.site = .rescaleWaitSt k := by
  obtain ⟨tag, hget⟩ := hst
  let q : Wg0.D := { d with site := .rescaleWaitSt k, o := Wg0.tileOutput L g d k words }
  have hq : Frame.stateAt (Machine.code P L) X g (i + 1) = some (some (.wg0 q)) := by
    rw [Frame.stateAt_succ hget, hstate, Option.bind_some]
    change Machine.next P L g (.wg0 d) ⟨tag, .tc (.st (64 * k.val) words .s32x32b)⟩ = _
    simp only [Machine.next, Wg0.next, Wg0.nextSite, hsite, q]
    rfl
  have he : X.get (g, i + 1) = some (X.tr g)[i + 1] := List.getElem?_eq_getElem hlen
  obtain ⟨t, ins, u, hat, _, hc, hf⟩ := Frame.fired_site hs hX he hq
  cases u with
  | none =>
    change kernel.code[q.site.pc]? = some ins at hc
    have hcode : kernel.code[(Wg0.Site.rescaleWaitSt k).pc]? = some ⟨none, .tcWaitSt⟩ := by
      fin_cases k <;> kernel_rfl
    have hins := Option.some.inj (hc.symm.trans hcode)
    subst ins
    change Fires q.site.pc (eventTmpl Assumptions.all L g t (.tcWaitSt)) _ none at hf
    simp [eventTmpl, tcTmpl, hpre.block, ofExec, Pure.pure, Except.pure, Fires] at hf
  | some u =>
    have hf' := (Wg0.fires_rescaleWaitSt (L := L) (g := g) (d := q) rfl hc hf).1
    generalize (X.tr g)[i + 1] = ev at hf' he
    obtain ⟨site, kind⟩ := ev
    change kind = .tc .waitSt at hf'
    exact ⟨site, q, by rw [he, hf'], hq, rfl⟩

/-- When the trace extends past an actual rescale store, the next event completes the store. -/
theorem wait_next (hlen : i + 1 < (X.tr g).length) :
    ∃ tag, X.get (g, i + 1) = some ⟨tag, .tc .waitSt⟩ := by
  obtain ⟨tag, _, hw, _, _⟩ := wait_next_state hpre hX hs hstate hsite hst hlen
  exact ⟨tag, hw⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0RescaleHistory
