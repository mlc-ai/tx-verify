-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Election
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.InitSpan
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Init
import Kernels.InklingRelDecode.Flow.Code.Part002
import Lemmas.Flow.SegChain
import Lemmas.Flow.SegPieces
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

def elLeader (i : Fin 12) := if i=0 then 665 else 666+i.val
theorem el_fetch (i : Fin 12) : kernel.code[(Site.el i).pc]? =
    some ⟨none,.warp ⟨.elect,none,[some (elLeader i),some (41+i.val)],[],some (.imm (-1))⟩⟩ := by
  fin_cases i <;> first | exact Flow.code_130 | exact Flow.code_135 | exact Flow.code_139 |
    exact Flow.code_143 | exact Flow.code_147 | exact Flow.code_151 | exact Flow.code_155 |
    exact Flow.code_159 | exact Flow.code_163 | exact Flow.code_167 | exact Flow.code_171 |
    exact Flow.code_175

theorem el_checked : ∀ i : Fin 12, (ctlLive (Site.el i).pc).all (fun k => !voteReg k) ∧
    elLeader i ∉ ctlLive (Site.el i).pc ∧ 41+i.val ∉ ctlLive (Site.el i).pc ∧
    elLeader i ≠ 41+i.val := by decide +kernel

theorem step_init_elect {Q L g w} (d : D) (i : Fin 12) (hs : d.site = .el i) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,b,c,old,bcast⟩ := d
  cases hs
  let d : D := ⟨.el i,a,b,c,old,bcast⟩
  let z := fun win : Bool => if g%L.block<32 && win then Site.init i else afterInit i
  obtain ⟨key,sub,pc,live⟩ := init_checked i
  apply full_elect d z (el_fetch i) (el_checked i).1 (el_checked i).2 (fun _ _ _ => rfl) rfl
  · intro win
    dsimp only [z]
    split
    · rfl
    · exact sub
  · intro win
    dsimp only [z]
    split
    · rename_i h
      simpa [Inv] using h
    · unfold afterInit
      split <;> trivial
  · intro win
    let dd := {d with elected := win}
    apply (init_span (Q := Q) (L := L) (g := g) (w := w) dd i).comp
    dsimp only [z]
    split
    · exact fun t ht => .inl ⟨t,.refl,ht⟩
    · rename_i h
      have val : valueOf Q L g w dd (26+i.val) = .pred (decide (g%L.block<32) && win) := by
        fin_cases i <;> rfl
      have no : (decide (g%L.block<32) && win) = false := by simpa using h
      rw [no] at val
      have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
        (init_fetch i) (val ▸ mem_factsFrom (val := valueOf Q L g w dd) key) rfl
      exact (SegU.of_seg skip).comp (samePc pc live)

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
