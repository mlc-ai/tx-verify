-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopySpan
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.CopyRoute
import Kernels.InklingRelDecode.Flow.Code.Part003
import Kernels.InklingRelDecode.Flow.Code.Part004
import Lemmas.Flow.SegPieces
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
open PTX PTX.Flow PTX.Proof

set_option maxRecDepth 100000
def pelLeader (b : Fin 3) (j : Fin 4) :=
  ([[694,698,699,700],[715,720,721,722],[737,742,743,744]][b.val]!)[j.val]!

theorem pel_fetch (b j) : kernel.code[(Site.pel b j).pc]? =
    some ⟨none,.warp ⟨.elect,none,[some (pelLeader b j),some (copyVote b j)],[],
      some (.imm (-1))⟩⟩ := by
  fin_cases b <;> fin_cases j
  · exact Flow.code_203
  · exact Flow.code_213
  · exact Flow.code_223
  · exact Flow.code_228
  · exact Flow.code_245
  · exact Flow.code_255
  · exact Flow.code_265
  · exact Flow.code_270
  · exact Flow.code_287
  · exact Flow.code_297
  · exact Flow.code_307
  · exact Flow.code_312

theorem ptc_guarded (b j) : ∃ op, kernel.code[(Site.ptc b j).pc]? =
    some ⟨some (copyGuard b j,false),op⟩ := by
  fin_cases b <;> fin_cases j <;> apply Exists.intro _
  · exact Flow.code_211
  · exact Flow.code_217
  · exact Flow.code_226
  · exact Flow.code_231
  · exact Flow.code_253
  · exact Flow.code_259
  · exact Flow.code_268
  · exact Flow.code_273
  · exact Flow.code_295
  · exact Flow.code_301
  · exact Flow.code_310
  · exact Flow.code_315

theorem pel_checked : ∀ b j, let rs := ctlLive (pelPc b j)
    rs.all (fun k => !voteReg k) ∧ (pelLeader b j ∉ rs ∧ copyVote b j ∉ rs ∧
      pelLeader b j ≠ copyVote b j) ∧ copyGuard b j ∈ ctlLive (ptcPc b j) := by decide +kernel

theorem copyResume {m} (hp : Pre Q L m) (d : D) (b j) :
    let z := afterCopy d (g%L.block) (preloadN Q L g d) b j
    SegU kernel Assumptions.all L g (ptcPc b j+1) (facts Q L g w d (ptcPc b j))
      z.pc (facts Q L g w d z.pc) := by
  fin_cases j
  · apply cross
    exact (by decide +kernel : ∀ b, crossCheck (ptcPc b 0) (ptcPc b 0+1) (pbPc b 2)) b
  · fin_cases b
    · exact block_half_0
    · exact block_half_1
    · exact block_half_2
  · apply cross
    exact (by decide +kernel : ∀ b, crossCheck (ptcPc b 2) (ptcPc b 2+1) (pbPc b 4)) b
  · exact copy_tail hp b

/-- The lost election of the last issue, when the copy tail leaves the preload loop: up to the
end of the copy tail. -/
theorem elect_lose_316 (dd : D) (b : Fin 3)
    (no : (decide (g%L.block%128<64) && dd.elected) = false)
    (h0 : b = 0 → preloadN Q L g dd = 1) (h1 : b = 1 → preloadN Q L g dd < 3) :
    SegU kernel Assumptions.all L g (pelPc b 3+1)
      ((copyVote b 3,.pred dd.elected)::facts Q L g w dd (pelPc b 3)) 316
      (facts Q L g w dd 316) := by
  apply (copy_span (Q := Q) (L := L) (g := g) (w := w) dd b 3).comp
  have val : valueOf Q L g w dd (copyGuard b 3) =
      .pred (decide (g%L.block%128<64) && dd.elected) := by
    fin_cases b <;> rfl
  rw [no] at val
  obtain ⟨op,hc⟩ := ptc_guarded b 3
  have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
    hc (val ▸ mem_factsFrom (val := valueOf Q L g w dd) (pel_checked b 3).2.2) rfl
  exact (SegU.of_seg skip).comp (copy_tail_316 b h0 h1)

theorem step_copy_elect {m} (hp : Pre Q L m) (d : D) (b j) (hs : d.site = .pel b j) :
    (code Q L g w).StepAtU d := by
  obtain ⟨s,a,x,c,old,bcast⟩ := d
  cases hs
  let d : D := ⟨.pel b j,a,x,c,old,bcast⟩
  let tail := afterCopy d (g%L.block) (preloadN Q L g d) b j
  let z := fun win : Bool => if g%L.block%128<64 && win then Site.ptc b j else tail
  obtain ⟨keys,fresh,guardKey⟩ := pel_checked b j
  apply full_elect d z (pel_fetch b j) keys fresh (fun _ _ _ => rfl) rfl
  · intro win
    dsimp only [z,tail]
    obtain ⟨_,_,qsub⟩ := query_route (Q := Q) (L := L) (g := g) (w := w) (d := d) 0
    fin_cases j <;> simp only [afterCopy] <;> (try split_ifs) <;> first | rfl | exact qsub
  · intro win
    dsimp only [z]
    split
    · rename_i h
      simpa [Inv] using h
    · obtain ⟨_,qinv,_⟩ := query_route (Q := Q) (L := L) (g := g) (w := w)
          (d := {d with elected := win}) 0
      dsimp only [tail]
      fin_cases j <;> simp only [afterCopy] <;> (try split_ifs) <;> trivial
  · intro win
    let dd := {d with elected := win}
    apply (copy_span (Q := Q) (L := L) (g := g) (w := w) dd b j).comp
    dsimp only [z]
    split
    · exact fun t ht => .inl ⟨t,.refl,ht⟩
    · rename_i h
      have val : valueOf Q L g w dd (copyGuard b j) = .pred (decide (g%L.block%128<64) && win) := by
        fin_cases b <;> fin_cases j <;> rfl
      have no : (decide (g%L.block%128<64) && win) = false := by simpa using h
      rw [no] at val
      obtain ⟨op,hc⟩ := ptc_guarded b j
      have skip := Seg.guardSkip (A := Assumptions.all) (L := L) (g := g)
        hc (val ▸ mem_factsFrom (val := valueOf Q L g w dd) guardKey) rfl
      have endSeg := copyResume (w := w) (g := g) hp dd b j
      fin_cases j <;> exact (SegU.of_seg skip).comp endSeg

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Control
