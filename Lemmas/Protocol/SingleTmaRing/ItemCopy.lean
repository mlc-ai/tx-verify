-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Order
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # The copies of a use of a single-CTA TMA ring slot

A proof tool. A counted copy item of a use (`SF`, kind `k ≠ 0`) is a notified tensor copy on the
slot's full barrier of that use (`item_copy`), and the items of one use are distinct events
(`item_inj`). -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}

/-- **A copy item of a use is a notified copy of that use.** -/
theorem item_copy (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {k : Kind S} {u : Nat}
    (hx : (k, u) ∈ SF X S) (hk : k.val ≠ 0) :
    ∃ pc al sp o, X.get (opF X S k u) = some ⟨pc, .tensorIssue al sp⟩ ∧ sp.mbar = S.full ∧
      copyUse X S (opF X S k u) = u ∧ X.tensor (opF X S k u) = some o ∧ o.spec = sp ∧
      o.effects.notified = true := by
  obtain ⟨-, r, hr, hid, -, -, h1⟩ := Finset.mem_filter.mp hx
  have ha := h1 hk
  have hδ := H.δ_le
  have hit : itF X S k u = .async (opF X S k u) (.notify .load) := by simp [itF, hk]
  have hobj : objectAction X X.async S.full (.async (opF X S k u) (.notify .load)) =
      some (.completeTx S.bytes) := by
    have h := ((hX.tma.2.2.1 S.full).2.1 r hr).1
    rw [hid, hit, ha] at h
    exact h
  obtain ⟨pc', a', s', o, hget', hobs, -, hnot, -⟩ := PairTmaRing.tensorNotify_facts hobj
  have hspec : o.spec = s' := by
    obtain ⟨mA, pc'', hget''⟩ := (hX.tensor _ o hobs).1
    have h := Option.some.inj (hget'.symm.trans hget'')
    simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
    exact h.2.2.symm
  rcases item_completion H (x := (k, u)) hk hr hid ha with
    ⟨hδ1, hu, pc, al, sp, he, hm⟩ | ⟨hpz, j, pc, al, sp, hop, he, hm, hcnt, -⟩
  · have hop : opF X S k u = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      simp only at hu
      simp [opF, hδ1, hu, hk]
    refine ⟨pc, al, sp, o, he, hm, ?_, hobs, ?_, hnot⟩
    · simp only at hu
      rw [hop, hu]
      simp [copyUse, hδ1]
    · rw [hspec]
      have h := Option.some.inj (hget'.symm.trans he)
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
      exact h.2.2
  · simp only at hpz hcnt
    refine ⟨pc, al, sp, o, by rw [hop]; exact he, hm, ?_, hobs, ?_, hnot⟩
    · have hnp : ¬ (S.δ = 1 ∧ ∃ i : Fin S.n, (S.cp, j) = S.pCp i) := by
        rintro ⟨hδ1, i, hi⟩
        exact (H.pre_ne hδ1).2 i (congrArg Prod.fst hi).symm
      rw [hop]
      simp only [copyUse, hnp, ↓reduceIte, hcnt]
      have := k.isLt
      have hn : 0 < S.n := by omega
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt (by omega)]
      omega
    · rw [hspec]
      have h := Option.some.inj (hget'.symm.trans (by rw [hop]; exact he))
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at h
      exact h.2.2

/-- **The copy items of one use are distinct events.** -/
theorem item_inj (H : Hyp L K A X S sc) {k k' : Kind S} {u : Nat} (hx : (k, u) ∈ SF X S)
    (hx' : (k', u) ∈ SF X S) (hk : k.val ≠ 0) (hk' : k'.val ≠ 0)
    (heq : opF X S k u = opF X S k' u) : k = k' := by
  obtain ⟨-, r, hr, hid, -, -, h1⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, r', hr', hid', -, -, h1'⟩ := Finset.mem_filter.mp hx'
  have := k.isLt
  have := k'.isLt
  rcases item_completion H (x := (k, u)) hk hr hid (h1 hk) with
    ⟨hδ1, hu, -⟩ | ⟨hpz, j, pc, al, sp, hop, he, -, hcnt, -⟩
  · simp only at hu
    have e1 : opF X S k u = S.pCp ⟨k.val - 1, by have := k.isLt; omega⟩ := by
      simp [opF, hδ1, hu, hk]
    have e2 : opF X S k' u = S.pCp ⟨k'.val - 1, by have := k'.isLt; omega⟩ := by
      simp [opF, hδ1, hu, hk']
    rw [e1, e2] at heq
    have h := H.pre_inj hδ1 heq
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · rcases item_completion H (x := (k', u)) hk' hr' hid' (h1' hk') with
      ⟨hδ1, hu, -⟩ | ⟨-, j', pc', al', sp', hop', he', -, hcnt', -⟩
    · exact absurd ⟨hδ1, hu⟩ hpz
    · simp only at hcnt hcnt' hop hop'
      rw [hop, hop'] at heq
      simp only [Prod.mk.injEq, true_and] at heq
      subst heq
      exact Fin.ext (by omega)

end
end PTX.SingleTmaRing
