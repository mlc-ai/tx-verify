-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Lemmas.Flow.PhaseTableJump
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Machine
public import Kernels.InklingRelDecode.Proof.Lib.Havoc

@[expose] public section

/-! # Facts by position with jumps, at the first stop

The table's facts hold at the first stop after a state of the region, or the thread is dead
(`goal_tabJ`), given the stop's position; a segment of a generated run is a jump of the table
(`jump_segU`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code

noncomputable section
variable {L : Launch} {g : Nat}

/-- **The table's facts hold at the first stop**, or the thread is dead. -/
theorem goal_tabJ {ivs : List (Nat × Nat)} {keys : Nat → List Nat} {post spec : Nat → Bool}
    {V1 V2 : Nat → Value} {F : List (Nat × Value)} {u : TState} {q : Nat}
    (hscan : tabScan kernel ivs keys post spec = true)
    (hS : ∀ pc, inIvs ivs pc = true → spec pc = false → Assumption.SegFreePc Assumptions.all pc)
    (hjump : ∀ pc, spec pc = true → inIvs ivs pc = true → ∀ t : TState, t.pc = pc →
      t.fault = none → TabAt keys post V1 V2 t →
      (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
        TabGood kernel ivs keys post V1 V2 w) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t)
    (hu : TabGood kernel ivs keys post V1 V2 u)
    (hstops : (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = q) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u)
    (hconv : ∀ R, Holds R (phi keys post V1 V2 q) → Holds R F) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs F) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  by_cases hD : Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u
  · exact .inr hD
  refine .inl fun t' hr hs => ?_
  rcases hstops with hst | hd
  · rcases rtg_tableJ Lib.rulesFrame hscan hS hjump hu hr hs with ⟨-, -, -, hh⟩ | hd
    · rw [hst t' hr hs] at hh
      exact hconv _ hh
    · exact absurd hd hD
  · exact absurd hd hD

/-- **A segment of a run is a jump of the table.** -/
theorem jump_segU {ivs : List (Nat × Nat)} {keys : Nat → List Nat} {post : Nat → Bool}
    {V1 V2 : Nat → Value} {s q : Nat} {F G : List (Nat × Value)}
    (h : SegU kernel Assumptions.all L g s F q G) (hne : s ≠ q)
    (hq : (inIvs ivs q || evAtB kernel q) = true)
    (hF : ∀ R, Holds R (phi keys post V1 V2 s) → Holds R F)
    (hG : ∀ R, Holds R G → Holds R (phi keys post V1 V2 q)) :
    ∀ t : TState, t.pc = s → t.fault = none → TabAt keys post V1 V2 t →
      (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
        TabGood kernel ivs keys post V1 V2 w) ∨
        Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  intro t hpc hf hT
  obtain ⟨hsub, hacc, hH⟩ := hT
  rcases h t ⟨hpc, hsub, hacc, hf, hF _ (hpc ▸ hH)⟩ with ⟨u, hr, hu⟩ | hd
  · obtain ⟨hu1, hu2, hu3, -, hu5⟩ := hu
    refine .inl ⟨u, hr, fun e => hne (by rw [← hpc, e, hu1]), ?_, hu2, hu3, ?_⟩
    · rwa [hu1]
    · rw [hu1]
      exact hG _ hu5
  · exact .inr hd

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
