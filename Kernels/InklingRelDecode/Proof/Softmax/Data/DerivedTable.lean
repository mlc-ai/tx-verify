-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.Derived
import Kernels.InklingRelDecode.Flow.Code

@[expose] public section

/-! # The derived constants by position

On every path from the barrier of pc 575 or the last preload (pc 806) to a loop site the thread
runs the four generated runs of `Gen/SoftmaxEntry` (pcs 576, 609, 814 and 849) and keeps their
registers over the code between. `tk` lists, for each position, the registers whose facts
(`derV`) hold there. The runs are the jumps of `rtg_tableJ`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

/-- The registers whose facts hold at a position. -/
def tk (pc : Nat) : List Nat :=
  if pc = 576 then [462, 481, 482, 525]
  else if pc ≤ 599 then [1, 2, 496, 798, 482, 525]
  else if pc ≤ 608 then [1, 2, 496, 798, 482, 498, 805]
  else if pc = 609 then [798, 1, 2, 496, 482, 498, 805]
  else if pc ≤ 807 then [1956, 1, 2, 496, 798, 482, 498, 805]
  else if pc ≤ 814 then [1956, 1, 2, 496, 798, 482, 805, 499]
  else if pc ≤ 848 then [810, 811, 1, 2, 1956, 805, 499]
  else keysC

def tkSpec (pc : Nat) : Bool :=
  pc = 576 || pc = 599 || pc = 609 || pc = 807 || pc = 814 || pc = 848

/-- The positions of the paths: the runs' starts, the code between them, the loop. -/
def ivsD : List (Nat × Nat) :=
  [(576, 1), (597, 3), (602, 213), (816, 33), (943, 56), (1049, 208), (2560, 5)]

theorem tk_scan : tabScan kernel ivsD tk (fun _ => false) tkSpec = true := by decide +kernel

theorem tk_seg : ∀ pc, inIvs ivsD pc = true → tkSpec pc = false →
    Assumption.SegFreePc Assumptions.all pc :=
  hseg_ivs (by decide +kernel)

/-- The table's facts hold from the run's start, or the thread is dead. -/
abbrev TabD (e : Entry) (L : Launch) (g : Nat) : TState → Prop :=
  TabAt tk (fun _ => false) (derV e L g) (derV e L g)

/-- A generated run as a jump of the table: the run's start facts and the frame hold at the
start's position, the run's end facts and the frame give the table's at its end. -/
theorem jump_tab {n s b : Nat} {F G : List (Nat × Value)} {C : Prop} {ins : List Instr}
    {Hk : List Nat}
    (seg : SegD kernel Assumptions.all L g n s F b G C)
    (hcode : (kernel.code.drop s).take n = ins) (hlen : ins.length = n)
    (hB : frameB ins Hk = true) (hS : ∀ i < n, Assumption.SegFreePc Assumptions.all (s + i))
    (hne : s ≠ b) (hbi : (inIvs ivsD b || evAtB kernel b) = true)
    (hin : ∀ R, Holds R (factsFrom (tk s) (derV e L g)) →
      Holds R F ∧ Holds R (factsFrom Hk (derV e L g)))
    (hout : ∀ R, Holds R G → Holds R (factsFrom Hk (derV e L g)) →
      Holds R (factsFrom (tk b) (derV e L g)))
    {t : TState} (ht : t.pc = s) (hf : t.fault = none) (hT : TabD e L g t) :
    (∃ w, Relation.ReflTransGen (Tau kernel Assumptions.all L g) t w ∧ t ≠ w ∧
      TabGood kernel ivsD tk (fun _ => false) (derV e L g) (derV e L g) w) ∨
      Machine.Dead (K := kernel) (A := Assumptions.all) (L := L) (g := g) t := by
  obtain ⟨hsub, hacc, hH⟩ := hT
  rw [ht] at hH
  obtain ⟨h1, h2⟩ := hin _ hH
  have hat : At t s (F ++ factsFrom Hk (derV e L g)) :=
    ⟨ht, hsub, hacc, hf, (holds_append _ _ _).mpr ⟨h1, h2⟩⟩
  rcases jump_gen (H := factsFrom Hk (derV e L g)) seg hcode hlen
    (by simpa [factsFrom, List.map_map, Function.comp_def] using hB) hS hne hat with
    ⟨w, hr, hne', hw⟩ | hd
  · refine .inl ⟨w, hr, hne', ?_, hw.2.1, hw.2.2.1, ?_⟩
    · rw [hw.1]; exact hbi
    · obtain ⟨hp, -, -, -, hR⟩ := hw
      rw [hp]
      exact hout _ ((holds_append _ _ _).mp hR).1 ((holds_append _ _ _).mp hR).2
  · exact .inr hd

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
