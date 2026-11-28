-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataFrameAny
public import Lemmas.Flow.RegionHooks

@[expose] public section

/-! # Constant facts added to a value machine

A proof tool, generic over the kernel. `C.withConst sF` is the machine `C` whose states also state
the facts `sF d` (the launch's constants: registers no code of the region writes). Every data step
of `C` is a data step of `C.withConst sF` (`DataStep.of_base`); the new facts are kept by an
event whose frame set writes none of them (`DataStep.frameAny`); two data steps of one machine
combine (`DataStep.and`), so `DataStep.addConst` gives the data step for the old facts followed by
the constants. -/

namespace PTX.Flow.Code
open PTX PTX.Proof PTX.EventFrame

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- The machine `C` with the facts `sF d` added at every state. -/
@[reducible] def withConst (C : Code K A L g) (sF : C.D → List (Nat × Value)) : Code K A L g :=
  { C with facts := fun d => C.facts d ++ sF d }

theorem DataStep.of_base {C : Code K A L g} {dF sF : C.D → List (Nat × Value)} {d : C.D}
    (h : DataStep C dF d) : DataStep (C.withConst sF) dF d := by
  intro t e u d' ins hat hi hc hf hn
  obtain ⟨a, b, c, f, hh⟩ := hat
  exact h ins ⟨a, b, c, f, ((holds_append _ _ _).mp hh).1⟩ hi hc hf hn

theorem DataStep.and {C : Code K A L g} {f1 f2 : C.D → List (Nat × Value)} {d : C.D}
    (h1 : DataStep C f1 d) (h2 : DataStep C f2 d) : DataStep C (fun d => f1 d ++ f2 d) d := by
  intro t e u d' ins hat hi hc hf hn
  rcases h1 ins hat hi hc hf hn with a | a
  · rcases h2 ins hat hi hc hf hn with b | b
    · exact .inl fun t' hr hs => (holds_append _ _ _).mpr ⟨a t' hr hs, b t' hr hs⟩
    · exact .inr b
  · exact .inr a

/-- **The data step for the old facts followed by constants** that the event keeps. -/
theorem DataStep.addConst {C : Code K A L g} {dF sF : C.D → List (Nat × Value)} {d : C.D}
    (h : DataStep C dF d) (hs : DataStep (C.withConst sF) sF d) :
    DataStep (C.withConst sF) (fun d => dF d ++ sF d) d :=
  DataStep.and h.of_base hs

/-- **The data step of an event that keeps constants**: the event writes none of their registers
and the local code after it stays in a region (with the segments of the hook table) that writes
none. -/
theorem DataStep.constAny {C : Code K A L g} {sF : C.D → List (Nat × Value)} {d : C.D}
    {tab : Nat → Option Havoc.Hook} (hA : RulesFrame A) (hh : HooksAny A L g tab)
    {ivs : List (Nat × Nat)}
    (hs0 : Assumption.SegFreePc A (C.pc d))
    (hp : inIvs ivs (C.pc d) = true ∧ inIvs ivs (C.pc d + 1) = true)
    (hF : ∀ R, Holds R (C.facts d) → Holds R (sF d))
    (hev : ∀ ins, K.code[C.pc d]? = some ins →
      ((sF d).map Prod.fst).all (fun r => !(eventWrites ins.op).contains r) = true)
    (hB : regionH K tab ivs ((sF d).map Prod.fst) = true)
    (hsub : ∀ e d', C.next d e = some (some d') → ∀ x ∈ sF d', x ∈ sF d) :
    DataStep C sF d := by
  intro t e u d' ins hat hi' hc' hf hn
  obtain ⟨hpc, -, -, -, hreg⟩ := hat
  have hloc : ∀ op u, execLocalA A L g t op = .ok u → LocalFrame op t u := fun op u h =>
    execLocalA_frame hA h (hpc ▸ hs0)
  rw [← hpc] at hf
  have hup := callbackFrame_fires (eventTmpl_return_frame_at (op := ins.op) hloc) hf
  have hkept := callbackFrame_fires (eventTmpl_kept_at (op := ins.op) hloc) hf
  have hH : Holds t.regs (sF d') := holds_of_mem fun r v hm =>
    holds_mem (hF _ hreg) (hsub e d' hn _ hm)
  refine .inl fun t' hr _ => ?_
  have hu : inIvs ivs u.pc = true := by
    rcases hup with h | h <;> rw [h, hpc]
    exacts [hp.1, hp.2]
  have key := region_frame_h hA hh hB hr hu
  refine holds_of_mem fun r v hm => ?_
  have hm' : (r, v) ∈ sF d := hsub e d' hn _ hm
  have hr' : r ∈ (sF d).map Prod.fst := List.mem_map.mpr ⟨_, hm', rfl⟩
  rw [key r hr', hkept r ?_]
  · exact holds_mem ((hF _ hreg)) hm'
  · intro hmem
    have := List.all_eq_true.mp (hev ins hc') r hr'
    simp [hmem] at this

end
end PTX.Flow.Code
