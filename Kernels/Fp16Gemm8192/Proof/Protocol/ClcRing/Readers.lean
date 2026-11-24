-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Interface
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Observes

@[expose] public section

/-! # The CLC responses of every reader

Every thread that polls its CTA's CLC response barrier observes, at its `n`-th successful poll, the
cluster's request issued after `n` earlier ones, and its read right after the poll holds that
request's response. The selected readers (the loader, the MMA warps of the leader CTA, the
scheduler) observe it through their consumer selector (`sel_observed`); the consumers observe it
through their warp group's CLC barrier (`cons_observed`). Two readers of one cluster at one ordinal
observe one request, so they read the same bytes (`allResponsesAgree`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace ClcRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The loader's selected consumer of CTA parity `k`: index `k`, warp 11 of its CTA. -/
def loadB (k : Fin 2) : Fin 10 := ⟨k.val, by have := k.isLt; omega⟩

theorem loadB_facts (k : Fin 2) :
    ctaOf (loadB k) = k.val ∧ warpOf (loadB k) = 11 ∧ laneZero (loadB k) = false := by
  fin_cases k <;> decide

/-- The scheduler's selected consumer of CTA parity `k`: index `2 + k`, warp 10 of its CTA. -/
def schedB (k : Fin 2) : Fin 10 := ⟨2 + k.val, by have := k.isLt; omega⟩

theorem schedB_facts (k : Fin 2) :
    ctaOf (schedB k) = k.val ∧ warpOf (schedB k) = 10 ∧ laneZero (schedB k) = false := by
  fin_cases k <;> decide

/-- The MMA selected consumer of warp `8 + w` of CTA 0: index `4 + w`. -/
def mmaB (w : Fin 2) : Fin 10 := ⟨4 + w.val, by have := w.isLt; omega⟩

theorem mmaB_facts (w : Fin 2) :
    ctaOf (mmaB w) = 0 ∧ warpOf (mmaB w) = 8 + w.val ∧ laneZero (mmaB w) = false := by
  fin_cases w <;> decide

/-- The threads of a selector: a thread of its CTA, warp and (for lane-0 selectors) lane. -/
theorem consumerSel_of (L : Launch) (b : Fin 10) {g : Nat}
    (hc : g / L.block = 2 * (g / L.block / 2) + ctaOf b) (hw : g % L.block / 32 = warpOf b)
    (hl : laneZero b = true → g % 32 = 0) : consumerSel L (g / L.block / 2) b g = true := by
  simp only [consumerSel, decide_eq_true_eq]
  exact ⟨hc, hw, hl⟩

/-- Two events of a list that `p` selects, preceded by equally many selected events, are one. -/
theorem index_eq_of_countP {α : Type} {p : α → Bool} {es : List α} {a b : Nat} {x y : α}
    (ha : es[a]? = some x) (hb : es[b]? = some y) (hx : p x = true) (hy : p y = true)
    (h : (es.take a).countP p = (es.take b).countP p) : a = b := by
  have key : ∀ {a b : Nat} {x : α}, es[a]? = some x → p x = true → a < b → b ≤ es.length →
      (es.take a).countP p < (es.take b).countP p := by
    intro a b x ha hx hab hb
    have hsplit : es.take b = es.take a ++ (es.drop a).take (b - a) := by
      conv_lhs => rw [show b = a + (b - a) by omega]
      rw [List.take_add]
    rw [hsplit, List.countP_append]
    have hal : a < es.length := (List.getElem?_eq_some_iff.mp ha).1
    have hd : (es.drop a).take (b - a) = x :: (es.drop (a + 1)).take (b - a - 1) := by
      rw [List.drop_eq_getElem_cons hal]
      obtain ⟨_, hx'⟩ := List.getElem?_eq_some_iff.mp ha
      rw [hx', show b - a = (b - a - 1) + 1 by omega, List.take_succ_cons]
      simp
    rw [hd, List.countP_cons, hx]
    simp
  have hal : a < es.length := (List.getElem?_eq_some_iff.mp ha).1
  have hbl : b < es.length := (List.getElem?_eq_some_iff.mp hb).1
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · exact absurd h (Nat.ne_of_lt (key ha hx hab hbl.le))
  · rfl
  · exact absurd h.symm (Nat.ne_of_lt (key hb hy hab hal.le))

/-- **The CLC responses of every reader at a poll count**, when the responses read at smaller poll
counts agree (which the consumers' group barrier needs). -/
theorem values_below (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) {n : Nat}
    (hag : OutputRing.ResponsesAgreeBelow L X n) :
    ∀ (c g j pc p : Nat) (acq : Bool) (sc : MbarScope), g / L.block / 2 = c →
      X.get (g, j) = some ⟨pc, .wait (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) p true acq sc⟩ →
      okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) = n →
      ∃ i s tg r, X.ClcIssue i s tg ∧ i.1 / L.block = 2 * c ∧ i.1 % L.block / 32 = 10 ∧
        ((X.tr i.1).take i.2).countP (clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩)) =
          okPolls (Bar.loc L (g / L.block) ⟨.clc, 0, true⟩) ((X.tr g).take j) ∧
        ClcObserved L X i (g / L.block) (g, j) ∧ (X.clc i).resolved = some r ∧
        ∀ pcr (src : Acc) bs, X.get (g, j + 1) = some ⟨pcr, .rd src bs⟩ →
          src.SameFootprint ⟨⟨.shared, g / L.block, L.sharedBase + 144⟩, 16, false, false, .cta,
            0, false⟩ →
          bs = (Value.clc r).toBytes.map some := by
  intro c g j pc p acq sc hc he hn
  subst hc
  have hg := Frame.lt_of_get hX he
  obtain ⟨ro, hσ, hwr⟩ := wait_role hX ht hg he rfl
  rcases ro with l | mm | sd | cc
  · -- the loader: warp 11 of its CTA
    have hwl : g % L.block / 32 = 11 := hwr
    exact sel_observed hpre hX ht hrw
      (b := loadB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩)
      (consumerSel_of L _ (by
          rw [(loadB_facts _).1]
          show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
          omega)
        (by rw [(loadB_facts _).2.1]; exact hwl)
        (by rw [(loadB_facts _).2.2]; simp)) he
  · -- the MMA warps: the leader CTA's; the odd CTA's MMA threads poll no response
    have hwm : mm.w = g % L.block / 32 ∧ (g % L.block / 32 = 8 ∨ g % L.block / 32 = 9) := hwr
    rcases Nat.mod_two_eq_zero_or_one (g / L.block) with h0 | h1
    · exact sel_observed hpre hX ht hrw
        (b := mmaB ⟨g % L.block / 32 - 8, by have := hwm.2; omega⟩)
        (consumerSel_of L _ (by
            rw [(mmaB_facts _).1]
            omega)
          (by
            rw [(mmaB_facts _).2.1]
            show g % L.block / 32 = 8 + (g % L.block / 32 - 8)
            have := hwm.2
            omega)
          (by rw [(mmaB_facts _).2.2]; simp)) he
    · exact absurd rfl (ht.mma_odd_quiet hg he hσ ⟨mm, rfl⟩ h1 p true acq sc)
  · -- the scheduler: warp 10 of its CTA
    have hws : g % L.block / 32 = 10 := hwr
    exact sel_observed hpre hX ht hrw
      (b := schedB ⟨g / L.block % 2, Nat.mod_lt _ (by norm_num)⟩)
      (consumerSel_of L _ (by
          rw [(schedB_facts _).1]
          show g / L.block = 2 * (g / L.block / 2) + g / L.block % 2
          omega)
        (by rw [(schedB_facts _).2.1]; exact hws)
        (by rw [(schedB_facts _).2.2]; simp)) he
  · -- the consumers: their warp group's CLC barrier
    exact cons_observed hpre hX ht hrw hg hσ he (by rw [hn]; exact hag)

/-- **The responses read at poll counts below `n + 1` agree**, when those below `n` do: two
readers of one cluster at one ordinal read the responses of the leader's requests with equally
many earlier ones, which are one. -/
theorem agree_succ (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) {n : Nat}
    (hag : OutputRing.ResponsesAgreeBelow L X n) : OutputRing.ResponsesAgreeBelow L X (n + 1) := by
  intro c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2
    hc1 hc2 hw1 hw2 hn hlt hr1 hf1 hr2 hf2
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
  · exact hag c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2
      hc1 hc2 hw1 hw2 hn hlt' hr1 hf1 hr2 hf2
  obtain ⟨⟨i1t, i1k⟩, s1, tg1, r1, hi1, -, -, hcn1, ho1, hres1, hrd1⟩ :=
    values_below hpre hX ht hrw hag c g1 j1 pc1 p1 acq1 sc1 hc1 hw1 heq
  obtain ⟨⟨i2t, i2k⟩, s2, tg2, r2, hi2, -, -, hcn2, ho2, hres2, hrd2⟩ :=
    values_below hpre hX ht hrw hag c g2 j2 pc2 p2 acq2 sc2 hc2 hw2 (hn ▸ heq)
  have hb1 := hrd1 pcr1 src1 bs1 hr1 hf1
  have hb2 := hrd2 pcr2 src2 bs2 hr2 hf2
  have hct1 := clcObs_mem ho1 hi1
  have hct2 := clcObs_mem ho2 hi2
  obtain ⟨pci1, hei1⟩ := hi1
  obtain ⟨pci2, hei2⟩ := hi2
  obtain ⟨hp1, hm1, -, -⟩ := issue_facts (c := c) hpre hX ht hei1 hct1 hc1
  obtain ⟨hp2, hm2, -, -⟩ := issue_facts (c := c) hpre hX ht hei2 hct2 hc2
  subst hp1 hp2
  have hk : i1k = i2k := by
    refine index_eq_of_countP (p := clcIssuesTo (Bar.loc L (2 * c) ⟨.clc, 0, true⟩))
      hei1 hei2 ?_ ?_ (by rw [hcn1, hcn2, hn])
    · simp [clcIssuesTo, hm1]
    · simp [clcIssuesTo, hm2]
  subst hk
  rw [hres1] at hres2
  cases hres2
  rw [hb1, hb2]

/-- The responses read at every poll count agree, by induction on the count. -/
theorem agree_below (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) :
    ∀ n, OutputRing.ResponsesAgreeBelow L X n
  | 0 => by
    intro c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2
      hc1 hc2 hw1 hw2 hn hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | n + 1 => agree_succ hpre hX ht hrw (agree_below hpre hX ht hrw n)

/-- **The CLC responses of every reader.** -/
theorem readerValues (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) : ReaderValues L X :=
  fun c g j pc p acq sc hc he =>
    values_below hpre hX ht hrw (agree_below hpre hX ht hrw _) c g j pc p acq sc hc he rfl

/-- **Two readers of one cluster at one ordinal read the same response.** -/
theorem allResponsesAgree (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) (hrw : ResponseWriters L X) : AllResponsesAgree L X := by
  intro c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2 src1 src2 bs1 bs2
    hc1 hc2 hw1 hw2 hn hr1 hf1 hr2 hf2
  exact agree_below hpre hX ht hrw _ c g1 g2 j1 j2 pc1 pc2 p1 p2 pcr1 pcr2 acq1 acq2 sc1 sc2
    src1 src2 bs1 bs2 hc1 hc2 hw1 hw2 hn (Nat.lt_succ_self _) hr1 hf1 hr2 hf2

end ClcRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
