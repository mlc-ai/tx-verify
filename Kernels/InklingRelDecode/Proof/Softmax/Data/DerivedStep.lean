-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.DerivedRun
public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Init
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The derived constants after the entry and after the last preload

The barrier of pc 575 and the last preload (pc 806) are followed by the generated runs of
`Gen/SoftmaxEntry`; the first stop after them is a preload (only after the barrier) or a loop
site, whose constants are `derF`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The table's facts hold at the first stop, or the thread is dead. -/
theorem derived_goal {u : TState} {q : Nat} {F : List (Nat × Value)}
    (hu : TabGood kernel ivsD tk (fun _ => false) (derV e L g) (derV e L g) u)
    (hstops : (∀ t'', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t'' →
      Stops kernel Assumptions.all L g t'' → t''.pc = q) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u)
    (hconv : ∀ R, Holds R (factsFrom (tk q) (derV e L g)) → Holds R F) :
    (∀ t', Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t' →
      Stops kernel Assumptions.all L g t' → Holds t'.regs F) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u := by
  by_cases hD : Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) u
  · exact .inr hD
  refine .inl fun t' hr hs => ?_
  rcases hstops with hst | hd
  · rcases rtg_tableJ Lib.rulesFrame tk_scan tk_seg
      (fun pc hsp hp t hpc hf hT => by
        simp only [tkSpec, Bool.or_eq_true, decide_eq_true_eq] at hsp
        rcases hsp with ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl
        exacts [jmp_en hpc hf hT, jmp_dv hpc hf hT, jmp_e8 hpc hf hT, jmp_ng hpc hf hT,
          jmp_ie hpc hf hT, jmp_io hpc hf hT])
      hu hr hs with ⟨-, -, -, hh⟩ | hd
    · rw [hst t' hr hs] at hh
      exact hconv _ (by simpa [phi] using hh)
    · exact absurd hd hD
  · exact absurd hd hD

/-- The facts of a stop's site follow from the table at its position. -/
theorem conv_der {d' : D} (hd : d'.c.site = .pre 0 ∨ d'.c.site = .nxt 0 ∨ d'.c.site = .waitS ∨
    d'.c.site = .epilogue) {R : Nat → Option Value}
    (h : Holds R (factsFrom (tk d'.c.site.pc) (derV e L g))) :
    Holds R (derF e L g d'.c.site) := by
  rcases hd with h1 | h1 | h1 | h1 <;> rw [h1] at h ⊢
  · exact holds_factsFrom_mono h (by decide)
  · exact holds_factsFrom_mono h (by decide)
  · exact holds_factsFrom_mono h (by decide)
  · trivial

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
