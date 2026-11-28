-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQOps
public import Lemmas.Flow.RunFrame

@[expose] public section

/-! # An exact stretch under explicit facts

`SegQ.of_seg_pre`: an exact stretch (`Seg`) between two fact lists is a strict stretch under the
invariant `QT qt` when explicit facts `D` ride along. The stretch writes none of the registers the
facts `D` name and none of those `qt b` tags (`frameB`), and its tags are among those of `qt a`. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem SegQ.of_seg_pre {qt : Nat → Env} {a b n : Nat} {Dk : List Nat} {D F G : List (Nat × Value)}
    (hD : ∀ p ∈ D, p.1 ∈ Dk) (hA : RulesFrame A) (hseg : Seg K A L g n a F b G) (hn : n = b - a)
    (hlen : b ≤ K.code.length) (hab : a ≤ b) (hS : PlainSegs A a b)
    (hB : frameB ((K.code.drop a).take n) (Dk ++ (qt b).map Prod.fst) = true)
    (hq : tagsIn (qt b) (qt a) = true) :
    SegQ K A L g (QT qt) a (D ++ F) b (D ++ G) := by
  intro t ht hQ
  obtain ⟨hp, hs, ha, hf, hr⟩ := ht
  rw [holds_append] at hr
  obtain ⟨u, hu, hAt⟩ := hseg t ⟨hp, hs, ha, hf, hr.2⟩
  have hlen' : ((K.code.drop a).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  have hfr := run_frame hA n a _ t u rfl hlen' hB
    (fun i hi => hS (a + i) (by omega) (by omega)) hp hf hu
  refine ⟨u, run_rtg hu, ⟨hAt.1, hAt.2.1, hAt.2.2.1, hAt.2.2.2.1, ?_⟩, ?_⟩
  · rw [holds_append]
    refine ⟨holds_of_forall fun p hp' => ?_, hAt.2.2.2.2⟩
    rw [hfr p.1 (List.mem_append_left _ (hD p hp'))]
    exact holds_mem hr.1 hp'
  · have hQ' : Typed (qt a) t := by simpa [QT, hp] using hQ
    have hT := typed_of_tagsIn hq hQ'
    intro r tg hr'
    rw [hAt.1] at hr'
    rw [hfr r (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) (lookup_mem hr')))]
    exact hT r tg hr'

/-- No step: the facts `G` follow from the facts `F`. -/
theorem SegQ.weaken {Q : TState → Prop} {a : Nat} {F G : List (Nat × Value)}
    (h : ∀ R, Holds R F → Holds R G) : SegQ K A L g Q a F a G := fun t ht hq =>
  ⟨t, .refl, ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, h _ ht.2.2.2.2⟩, hq⟩

end PTX.Flow.Havoc
