-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Lk5MShape
public import Kernels.InklingRelDecode.Proof.Thread.Lk3Min

@[expose] public section

/-!
# The scratch words of the softmax region: the steps that pass a barrier

* `cross23`, `cross21`: a step whose rank passes the rank of `bar23` of iteration `i0 ≥ 1` (of
  `bar21` of iteration `i0`) is the step from that state: the loop has no other edge over these
  barriers;
* `MidOk`: the sites between the `o_done` poll and the O rescale are reached only in iterations
  `i ≥ 1` (the first iteration goes from `shfl6` to the P store); `next_midOk` keeps it;
* `ldL_next`: the successor of the scratch load records the rebuilt word;
* `erealValue_store`: the value of an extended real is stored and rebuilt unchanged.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {L : Launch} {g : Nat} {d : D} {e : Event}

/-- **A step over `bar23` of iteration `i0 ≥ 1` is the step from it.** -/
theorem cross23 {d d' : D} {i0 : Nat} (hn : next L g d e = some (some d'))
    (h1 : d.rank ≤ 64 * i0 + 17) (h2 : 64 * i0 + 17 < d'.rank) (hi : 1 ≤ i0) :
    d.site = .bar23 ∧ d.i = i0 := by
  unfold D.rank at h1 h2
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum]; omega)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum])
    | (obtain ⟨h3, h4 | h4⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)
    | (obtain ⟨h3, h4⟩ := toBar20_rank hn
       try simp only [D.afterSum] at h3
       rw [h3, h4] at h2
       simp_all [Site.ord]
       omega)
    | (unfold afterArrive at hn
       obtain ⟨h3, h4 | h4⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)

/-- **A step over `bar21` of iteration `i0` is the step from it.** -/
theorem cross21 {d d' : D} {i0 : Nat} (hn : next L g d e = some (some d'))
    (h1 : d.rank ≤ 64 * i0 + 29) (h2 : 64 * i0 + 29 < d'.rank) :
    d.site = .bar21 ∧ d.i = i0 := by
  unfold D.rank at h1 h2
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum]; omega)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [Site.ord, D.afterSum])
    | (obtain ⟨h3, h4 | h4⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)
    | (obtain ⟨h3, h4⟩ := toBar20_rank hn
       try simp only [D.afterSum] at h3
       rw [h3, h4] at h2
       simp_all [Site.ord]
       omega)
    | (unfold afterArrive at hn
       obtain ⟨h3, h4 | h4⟩ := afterSetup_rank hn <;> simp_all [Site.ord] <;> omega)

/-- The sites of the rescale test and the O rescale. -/
def MidSite : Site → Prop
  | .waitO | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO => True
  | _ => False

/-- **A state at those sites is in an iteration `i ≥ 1`.** -/
def MidOk (d : D) : Prop := MidSite d.site → 1 ≤ d.i

theorem toBar20_midOk {x d' : D} (hn : toBar20 x = some (some d')) : MidOk d' := by
  intro hm
  rw [(toBar20_rank hn).2] at hm
  exact hm.elim

theorem afterSetup_midOk {x d' : D} (hn : afterSetup L g x = some (some d')) : MidOk d' := by
  intro hm
  rcases (afterSetup_rank hn).2 with h | h <;> rw [h] at hm <;> exact hm.elim

theorem next_midOk {d d' : D} (h : MidOk d) (hn : next L g d e = some (some d')) : MidOk d' := by
  unfold next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; unfold MidOk at h ⊢
       simp_all [MidSite, D.afterSum]; omega)
    | (simp only [Option.some.injEq] at hn; subst hn; unfold MidOk at h ⊢; simp_all [MidSite])
    | exact toBar20_midOk hn
    | exact afterSetup_midOk hn
    | (unfold afterArrive at hn; exact afterSetup_midOk hn)

/-- **The successor of the scratch load**: the word the read's bytes rebuild to is recorded. -/
theorem ldL_next {d d' : D} {pc : Nat} {ac : Acc} {bs : List (Option Byte)}
    (hs : d.site = .ldL) (hn : next L g d ⟨pc, .rd ac bs⟩ = some (some d')) :
    ∃ x, rebuild 3 bs = .ok x ∧ d'.stg.ld = x := by
  simp only [next, hs] at hn
  split at hn
  · rename_i x hx
    simp only [Option.some.injEq] at hn
    subst hn
    exact ⟨x, hx, rfl⟩
  · cases hn

theorem erealValue_bytes (w : EReal) : (erealValue .f32 w).bytes = 4 := by
  unfold erealValue
  split_ifs <;> simp [FVal.toValue, Value.bytes, FloatFmt.bytes]

/-- **The value of an extended real** is a scalar of four bytes: stored unchanged and
rebuilt from its bytes. -/
theorem erealValue_store (w : EReal) :
    storeValue 32 (erealValue .f32 w) = .ok (erealValue .f32 w) ∧
      rebuild 3 ((erealValue .f32 w).toBytes.map some) = .ok (erealValue .f32 w) := by
  have hb : (erealValue .f32 w).bytes = 4 ∧ (erealValue .f32 w).byteAt 0 =
      (erealValue .f32 w, 0) := by
    unfold erealValue
    split_ifs <;> simp [FVal.toValue, Value.bytes, Value.byteAt, FloatFmt.bytes]
  refine ⟨storeValue_of_bytes (by rw [hb.1]), rebuild_scalar (by rw [hb.1]; omega) hb.2⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
