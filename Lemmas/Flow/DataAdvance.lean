-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReachFrameGuard
public import Lemmas.Flow.Next

@[expose] public section

/-! # The data step of an event that advances, from a `Reach`

A proof tool, generic over the kernel. A value machine at an advancing event (a barrier, a fence,
an arrival, a tensor issue, an initialization: `AdvancesOp`, any guard) leaves the thread in
`next t`, so its data step is a `Reach` from the next position with the data facts of the state
(`DataStep.advance`). `DataStep.advance_frame` takes the `Reach` from a frame set (`frameSetG`):
the data facts of the successor are among the state's and no instruction before the next event
writes them. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of an advancing event.** -/
theorem DataStep.advance {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ins : Instr} (hc : K.code[C'.pc d]? = some ins) (hadv : AdvancesOp ins.op)
    (hs : C'.sub d = 0) (ha : C'.acc d = [])
    (hF : ∀ R, Holds R (C'.facts d) → Holds R (dF d))
    (hrun : ∀ e d', C'.next d e = some (some d') →
      Reach K A L g (C'.pc d + 1) (dF d) (dF d')) :
    DataStep C' dF d := by
  intro t e u d' ins' hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  obtain rfl := fires_next hadv hf
  obtain ⟨hpc, hsub, hacc, hft, hreg⟩ := hat
  exact hrun e d' hn (PTX.next t) ⟨by simp [PTX.next, hpc], hsub.trans hs, hacc.trans ha, hft,
    hF _ hreg⟩

/-- **The data step of an advancing event over control code that keeps the data facts.** -/
theorem DataStep.advance_frame {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ins : Instr} (hA : RulesFrame A) (hc : K.code[C'.pc d]? = some ins)
    (hadv : AdvancesOp ins.op) (hs : C'.sub d = 0) (ha : C'.acc d = [])
    (hF : ∀ R, Holds R (C'.facts d) → Holds R (dF d)) {S : List Nat}
    (hS : ∀ pc ∈ S, Assumption.SegFreePc A pc) (hp : (S.contains (C'.pc d + 1) ||
      evAtB K (C'.pc d + 1)) = true)
    (hB : ∀ e d', C'.next d e = some (some d') → frameSetG K S ((dF d').map Prod.fst) = true)
    (hsub : ∀ e d', C'.next d e = some (some d') → ∀ x ∈ dF d', x ∈ dF d) :
    DataStep C' dF d :=
  DataStep.advance hc hadv hs ha hF fun e d' hn =>
    reach_frameSetG hA (hB e d' hn) hS hp fun _ hR => holds_of_mem fun _ _ hm =>
      holds_mem hR (hsub e d' hn _ hm)

end
end PTX.Flow.Code
