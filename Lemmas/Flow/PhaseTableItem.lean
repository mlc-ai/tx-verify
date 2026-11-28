-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.PhaseTableJump
public import Lemmas.Flow.OutLit

@[expose] public section

/-! # A table's jump that is one run item

A proof tool, generic over the kernel. At a position of a table (`PhaseTableJump`) where one
instruction, an item of an outcome run, writes a fact's register, the item's step reaches the
table's facts of the next position (`jump_item`), or the thread is dead. -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **A jump of a table that is one item.** -/
theorem jump_item {keys : Nat → List Nat} {post : Nat → Bool} {V1 V2 : Nat → Value}
    {ivs : List (Nat × Nat)} {pc : Nat} {it : XItem} (hit : OAt K A L g pc [it])
    (hloc : it.localB = true) (hrd : it.reads.all (· ∈ keys pc) = true)
    (hreq : it.req (if post pc then V2 else V1) = true)
    (hcov : ∀ r ∈ keys (pc + 1), r ∈ it.writes ∨ r ∈ keys pc)
    (hval : ∀ r ∈ keys (pc + 1), (if post (pc + 1) then V2 else V1) r =
      it.upd (if post pc then V2 else V1) r)
    (hin : (inIvs ivs (pc + 1) || evAtB K (pc + 1)) = true) {t : TState} (ht : t.pc = pc)
    (hf : t.fault = none) (hT : TabAt keys post V1 V2 t) :
    (∃ w, Relation.ReflTransGen (Tau K A L g) t w ∧ t ≠ w ∧
      TabGood K ivs keys post V1 V2 w) ∨ Machine.Dead (K := K) (A := A) (L := L) (g := g) t := by
  obtain ⟨hsub, hacc, hH⟩ := hT
  have seg : SegD K A L g 1 pc (factsFrom (keys pc) (if post pc then V2 else V1)) (pc + 1)
      (factsFrom (keys (pc + 1)) (xFinal (if post pc then V2 else V1) [it]))
      (xCond (if post pc then V2 else V1) [it]) :=
    SegD.xouts (items := [it]) hit.code (by simpa [xReadsB] using hrd)
      (by simpa [xReq] using hreq) (by simpa [xLocalB] using hloc) hit.rules
      (fun r hr => by simpa [xWrites] using hcov r hr)
  have hat : At t pc (factsFrom (keys pc) (if post pc then V2 else V1)) :=
    ⟨ht, hsub, hacc, hf, by rw [ht] at hH; exact hH⟩
  by_cases hC : xCond (if post pc then V2 else V1) [it]
  · obtain ⟨w, hr, h1, h2, h3, -, h5⟩ := (seg t hat).1 hC
    refine .inl ⟨w, run_rtg hr, fun e => ?_, ?_, h2, h3, ?_⟩
    · rw [← e] at h1; omega
    · rw [h1]; exact hin
    · rw [h1]
      refine holds_of_pointwise fun r hr => ?_
      have hm := holds_mem h5 (mem_factsFrom (val := xFinal (if post pc then V2 else V1) [it]) hr)
      rw [hval r hr]
      exact hm
  · exact .inr ((seg t hat).2 hC)

end
end PTX.Flow.Code
