-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CtlStepsU

@[expose] public section

/-! # A `vote.any` in an exact machine

`Code.step_voteAnyS` is `Code.voteAnyU` for the exact obligation: the result of the vote decides the
successor `nv r` (`some none` where the machine stops following the thread), reached from the facts
after the event by an exact segment (`Lands`). -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

theorem step_voteAnyS {d : C.D} {nv : Bool → Option (Option C.D)} {ty dv pr neg mask}
    (hc : K.code[C.pc d]? = some ⟨none, .warp ⟨.vote .any neg, ty, [some dv], [.reg pr],
      some mask⟩⟩)
    (hoff : dv ∉ (C.facts d).map Prod.fst)
    (hn : ∀ m p r, C.next d ⟨C.pc d, .voteMode .any m p r⟩ = nv r)
    (hnn : ∀ r, nv r ≠ none)
    (hs : C.sub d = 0) (ha : C.acc d = [])
    (hl : ∀ r d', nv r = some (some d') →
      C.Lands d (C.pc d + 1) ((dv, .pred r) :: C.facts d) d') : C.StepOk d := by
  constructor
  intro t e u ins hat hi hc' hf
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain ⟨m, p, r, rfl, rfl⟩ := fires_voteAnyU hf
  have ht := At.set (r := dv) (v := .pred r) (at_of_atD hat hs ha)
    (fun q hq he => hoff (he ▸ List.mem_map_of_mem hq))
  rcases hnv : nv r with _ | _ | d'
  · exact absurd hnv (hnn r)
  · exact .inl (.inl ((hn m p r).trans hnv))
  · exact (hl r d' hnv).cont hi ((hn m p r).trans hnv) ht

end PTX.Flow.Code
