-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.RegionFrame
public import Lemmas.Flow.DataOver
public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # The data step of an event whose data facts are carried

A proof tool, generic over the kernel. A value machine's data facts that no instruction after an
event writes (`regionB`: a Boolean check of the code from the event to a final event) and that the
event itself does not write (`eventWrites`) are still true at the first state that performs an
event, whatever the kind of the event:

* `DataStep.carry`: the data step of a state whose successors' data facts are among its own;
* `Reach.region`: the same for a `Reach` from a position (the compute sites' carried part). -/

namespace PTX.Flow.Code
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A `Reach` of facts the code in a region does not write.** -/
theorem Reach.region (hA : RulesFrame A) {lo hi p : Nat} {F H : List (Nat × Value)}
    (hB : regionB K lo hi (H.map Prod.fst) = true)
    (hS : ∀ pc, lo ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) (h1 : lo ≤ p) (h2 : p ≤ hi)
    (hF : ∀ R, Holds R F → Holds R H) : Reach K A L g p F H := by
  intro u hu
  obtain ⟨hup, -, -, -, huF⟩ := hu
  refine .inl fun t' hr _ => holds_of_mem fun r v hm => ?_
  rw [region_frame hA hB hS hr (by omega) (by omega) r (List.mem_map_of_mem (f := Prod.fst) hm)]
  exact holds_mem (hF _ huF) hm

/-- **The data step of an event whose successors' data facts are carried**: the event writes no
register of the state's data facts, and no instruction from the event on, up to the final event
of the region, does. -/
theorem DataStep.carry {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ins : Instr} {hi : Nat} (hA : RulesFrame A) (hc : K.code[C'.pc d]? = some ins)
    (hF : ∀ R, Holds R (C'.facts d) → Holds R (dF d))
    (hB : regionB K (C'.pc d) hi ((dF d).map Prod.fst) = true)
    (hS : ∀ pc, C'.pc d ≤ pc → pc ≤ hi → Assumption.SegFreePc A pc) (hh : C'.pc d + 1 ≤ hi)
    (hev : ((dF d).map Prod.fst).all (fun r => !(eventWrites ins.op).contains r) = true)
    (hsub : ∀ e d', C'.next d e = some (some d') → ∀ x ∈ dF d', x ∈ dF d) :
    DataStep C' dF d := by
  intro t e u d' ins' hat hi' hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have hpc : t.pc = C'.pc d := hat.1
  have hS0 : Assumption.SegFreePc A t.pc := hS _ (by omega) (by omega)
  have hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u :=
    fun op u h => execLocalA_frame hA h hS0
  rw [← hpc] at hf
  have hup := callbackFrame_fires (eventTmpl_return_frame_at (op := ins'.op) hloc) hf
  have hkept := callbackFrame_fires (eventTmpl_kept_at (op := ins'.op) hloc) hf
  refine .inl fun t' hr _ => holds_of_mem fun r v hm => ?_
  have hm' := hsub e d' hn _ hm
  have hr1 := List.mem_map_of_mem (f := Prod.fst) hm'
  rw [region_frame hA hB hS hr (by omega) (by omega) r hr1, hkept r (by
    have := List.all_eq_true.mp hev r hr1
    simpa using this)]
  exact holds_mem (hF _ hat.2.2.2.2) hm'

end
end PTX.Flow.Code
