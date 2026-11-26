-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepsQ
public import Lemmas.Flow.ShflFor

@[expose] public section

/-! # A shuffle's strict step for one received word, under an invariant

`Code.step_shflForQ`: the strict step obligation under an invariant (`Code.StepForQ`) of a shuffle
into register `r` and validity predicate `p` for one event, whose successor `nv recv ok` is a
function of the received word. The states right after the shuffle satisfy the invariant (`hq`) and
the segment to the successor is strict (`SegQ`): the dispatch of warpgroup 1's head on the word
`7` reaches the index warp this way. -/

namespace PTX.Flow.Code
open PTX.Proof PTX.Flow.Havoc

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- **The strict step under an invariant of a shuffle for one event.** -/
theorem step_shflForQ {Q : TState → Prop} {Wf : Event → Prop} {d : C.D}
    {nv : Value → Bool → Option (Option C.D)} {mode : ShflMode}
    {ty : Option DType} {r p : Nat} {a b c mask : Opnd}
    (hc0 : K.code[C.pc d]? = some ⟨none, .warp ⟨.shfl mode, ty, [some r, some p], [a, b, c],
      some mask⟩⟩)
    (hr : ∀ q ∈ C.facts d, q.1 ≠ r) (hp : ∀ q ∈ C.facts d, q.1 ≠ p) (hrp : r ≠ p)
    (hn : ∀ m av bv cv recv ok, C.next d ⟨C.pc d, .shfl m av bv cv recv ok⟩ = nv recv ok)
    (hs : C.sub d = 0) (ha : C.acc d = []) (e : Event)
    (hl : ∀ recv ok, Wf e → (∃ m av bv cv, e = ⟨C.pc d, .shfl m av bv cv recv ok⟩) →
      ∃ d', nv recv ok = some (some d') ∧
        (∀ w, At w (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d) → Q w) ∧
        C.sub d' = 0 ∧ C.acc d' = [] ∧ (C.inv d → C.inv d') ∧
        SegQ K A L g Q (C.pc d + 1) ((p, .pred ok) :: (r, recv) :: C.facts d) (C.pc d')
          (C.facts d')) : C.StepForQ Q Wf d e := by
  intro t u ins h hi hc hQ hWe hf
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
  obtain ⟨d', hd', hq1, hs', ha', hi', seg⟩ := hl recv ok hWe ⟨_, av, bv, cv, rfl⟩
  obtain ⟨t', hr', hg, hq'⟩ := landQ hu (hq1 _ hu) seg (hi' hi) hs' ha'
  exact .inl ⟨d', t', (hn _ av bv cv recv ok).trans hd', hr', hg, hq'⟩

end PTX.Flow.Code
