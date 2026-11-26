-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ShflU
public import Lemmas.Flow.StrictWindow
public import Lemmas.Flow.Step.Combinators

@[expose] public section

/-! # A shuffle's strict step for one received word

`Code.step_shflFor`: the strict step obligation (`Code.StepFor`) of a shuffle into register `r` and
validity predicate `p` for one event. The machine's successor `nv recv ok` is a function of the
received word and its validity and never stops the machine on a fault; the strict obligation needs
the local segment to the successor (`Code.Lands`) only for the successors the event reaches, so a
shuffle whose other words end in a UB-tolerant segment is still strict for the words whose
segment is strict (`step_shflU` is tolerant for every word). -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **The strict step of a shuffle for one event.** -/
theorem step_shflFor {d : C.D} {nv : Value → Bool → Option (Option C.D)} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv ok)
    (hs : C.sub d = 0) (ha : C.acc d = []) (hnn : ∀ recv ok, nv recv ok ≠ none)
    (e : Event)
    (hl : ∀ recv ok d', (∃ m av bv cv, e = ⟨C.pc d, .shfl m av bv cv recv ok⟩) →
      nv recv ok = some (some d') →
      C.Lands d (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d) d') : C.StepFor d e := by
  intro t u ins h hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  have h0 := at_of_atD h hs ha
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := some p) hf
  have h1 : At (setReg t r recv) (C.pc d) ((r, recv) :: C.facts d) :=
    ⟨h0.1, h0.2.1, h0.2.2.1, h0.2.2.2.1, Function.update_self .., holds_update h0.2.2.2.2 hr⟩
  have hp' : ∀ q ∈ (r, recv) :: C.facts d, q.1 ≠ p := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hrp
    · exact hp q hq
  have hu := At.set (v := .pred ok) h1 hp'
  exact cont_sel hi (hn ..) hu (fun hx => absurd hx (hnn recv ok))
    (fun d' hd' => hl recv ok d' ⟨_, _, _, _, rfl⟩ hd')

end PTX.Flow.Code
