-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DivStep
public import Lemmas.Flow.SegQOps

@[expose] public section

/-! # `div.u32` of two register facts under the tag invariant

`SegQ.of_seg_frame'` is `SegQ.of_seg_frame` (`Lemmas/Flow/SegQOps.lean`) for a piece that lands
only on states of the invariant. `SegQ.div_u32`: a division whose divisor the invariant tags
nonzero (`Tag.nz`) is a strict piece: the quotient is a fact. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged PTX.Flow.Arith32

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **An exact piece that does not touch the tagged registers**, landing under the invariant. -/
theorem SegQ.of_seg_frame' {qt : Nat → Env} {a b n : Nat} {F G : List (Nat × Value)}
    (hA : RulesFrame A)
    (hseg : ∀ t, At t a F → QT qt t → ∃ u, run K A L g n t = some u ∧ At u b G)
    (hn : n = b - a) (hlen : b ≤ K.code.length)
    (hab : a ≤ b) (hS : PlainSegs A a b)
    (hB : frameB ((K.code.drop a).take n) ((qt b).map Prod.fst) = true)
    (hq : tagsIn (qt b) (qt a) = true) : SegQ K A L g (QT qt) a F b G := by
  intro t ht hQ
  obtain ⟨u, hu, hAt⟩ := hseg t ht hQ
  have hlen' : ((K.code.drop a).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  have hfr := run_frame hA n a _ t u rfl hlen' hB (fun i hi => hS (a + i) (by omega) (by omega))
    ht.1 ht.2.2.2.1 hu
  refine ⟨u, run_rtg hu, hAt, ?_⟩
  have hQ' : Typed (qt a) t := by simpa [QT, ht.1] using hQ
  have hT := typed_of_tagsIn hq hQ'
  intro r tg hr
  rw [hAt.1] at hr
  rw [hfr r (List.mem_map_of_mem (f := Prod.fst) (lookup_mem hr))]
  exact hT r tg hr

/-- **A division by a register the invariant tags nonzero**: a strict piece with the quotient as
a fact. -/
theorem SegQ.div_u32 {qt : Nat → Env} {pc d a r : Nat} {x y : BitVec 64} {F : List (Nat × Value)}
    (hA : RulesFrame A)
    (hc : K.code[pc]? =
      some ⟨none, .int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩⟩)
    (ha : (a, Value.bits 32 x) ∈ F) (hr : (r, Value.bits 32 y) ∈ F)
    (hnz : (qt pc).lookup r = some (Tag.nz 32)) (hd : ∀ q ∈ F, q.1 ≠ d)
    (hL : ∀ (t : TState), t.pc = pc → ∀ as ∈ A,
      as.localRule L g t (.int ⟨.div, .int .u 32, false, [some d], [.reg a, .reg r]⟩) = none)
    (hSF : Assumption.SegFreePc A pc) (hlen : pc + 1 ≤ K.code.length)
    (hS : PlainSegs A pc (pc + 1))
    (hB : frameB ((K.code.drop pc).take 1) ((qt (pc + 1)).map Prod.fst) = true)
    (hq : tagsIn (qt (pc + 1)) (qt pc) = true) :
    SegQ K A L g (QT qt) pc F (pc + 1) ((d, .bits 32 (divu32 x y)) :: F) := by
  refine SegQ.of_seg_frame' (n := 1) hA (fun t ht hQ => ?_) (by omega) hlen (Nat.le_succ pc) hS
    hB hq
  have hQ' : Typed (qt pc) t := by simpa [QT, ht.1] using hQ
  obtain ⟨x', hx', hnz'⟩ := hQ' r (.nz 32) hnz
  have hy := holds_mem ht.2.2.2.2 hr
  rw [hy] at hx'
  obtain ⟨-, rfl⟩ := Value.bits.inj (Option.some.inj hx')
  have hz : (r32 y).toNat % 4294967296 ≠ 0 := by
    simp only [r32, truncBits, BitVec.toNat_ofNat]; omega
  exact Seg.div_u32 hc ha hr hz hd hL hSF t ht

end PTX.Flow.Havoc
