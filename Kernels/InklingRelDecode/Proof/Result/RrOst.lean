-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.RdSLoad
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# The coordinates of a rescale store are the softmax state's loop counter

`Sr.OSt` carries the event of the store and the number of successful `o_done` polls of the thread
before it. The thread's states count those polls (`Rd.sm_cnt`: at a softmax state `d` they number
`smOPolled d`, which is `d.i` at the site `stO`), so:

* `Rr.ostIter_of`: the coordinate `b` of a rescale store is the loop counter `d.i` of the thread's
  state at the store (`Rs.OStIter`);
* `Rr.ostBound_of`: the coordinate is below the thread's `num_iters` (`Sm.Inv.late`: the loop
  counter of a late state is below `num_iters`);
* `Rr.oaccOstIter_of`: two rescale stores of one thread are in the order of the iterations: after
  a state at `stO` the iteration rises before the next `stO` (the sites `waitStO`, `bar20`,
  `tmemSt`, `tmemWait`, `bar21` and `arrive` follow it in the same iteration, and the counter rises
  only after `bar21` and `arrive`, `Interface.next_iter`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Rr
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Sr
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.EvW (oDone)

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The sites that follow the rescale store within an iteration. -/
def AfterStO : Sm.Site → Prop
  | .waitStO | .bar20 | .tmemSt | .tmemWait | .bar21 | .arrive => True
  | _ => False

/-- **The rescale store is followed by `waitStO`, `bar20`, `tmemSt`, `tmemWait`, `bar21` and
`arrive`** within its iteration: a step from `stO` or from such a site that keeps the loop counter
lands on such a site. -/
theorem next_afterStO {d0 d : Sm.D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d0.site = .stO ∨ AfterStO d0.site) (hi : d.i = d0.i) : AfterStO d.site := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [AfterStO])
    | (rename_i hh; rcases hs with hs | hs <;> simp_all [AfterStO]; done)
    | (have h1 := Sv.toBar20_site hn; simp [AfterStO, h1])
    | (unfold Sm.afterArrive at hn
       have h1 := afterSetup_i hn
       simp only at h1
       omega)

/-- **The state before a rescale store**: a softmax state at `stO` whose `o_done` polls number the
store's coordinate, so its loop counter is the coordinate. -/
theorem stO_iter (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {c t sk b a : Nat} {vals : List Value} {sh : TcShape}
    {p0 : Nat} {Soft : Nat → Prop} {tm : Nat}
    (hO : OSt L X c p0 Soft tm t sk b a vals sh) (ht : t < L.threads) (htc : t / L.block = c) :
    ∃ d : Sm.D, St Q L X t sk = some (some (.d (.sm d))) ∧ d.site = .stO ∧ d.i = b ∧
      d.i < Q.numIters (reqOf L t) (splitOf L t) := by
  obtain ⟨hsh, -, -⟩ := hO.shape
  subst hsh
  obtain ⟨pcs, hget⟩ := hO.event
  obtain ⟨d, hσ, hds⟩ := Rs.stO_state hX hf hget
  have hk : sk ≤ (X.tr t).length := (len_of_get hget).le
  have hc := ((Rd.sm_cnt hpre hX hf ht sk hk _ hσ).2 d rfl).o
  have h1 := hO.polls
  rw [← htc] at h1
  have hI := Sv.sm_inv_at hX hf hget hσ
  refine ⟨d, hσ, hds, ?_, ?_⟩
  · rw [h1] at hc
    rw [hc]
    simp [SO.smOPolled, hds]
  · have h26 : d.e.r26 = Q.numIters (reqOf L t) (splitOf L t) := r26_eq hpre hX hf ht hget hσ
    rw [← h26]
    exact (hI.late (by rw [hds]; trivial)).2.2

/-- **`Rs.OStIter`**: the coordinate of a rescale store is the loop counter of the softmax state at
the store. -/
theorem ostIter_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {K : Kernel} {A : List Assumption}
    (G : SrPkg L K A mem0 X) : Rs.OStIter Q L X G := by
  intro c _ t sk b a vals sh d hO hσ
  obtain ⟨ht, htc, -⟩ := hO.gate.soft
  obtain ⟨d', hσ', -, hi, -⟩ := stO_iter hpre hX hf hO ht htc
  rw [hσ'] at hσ
  simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at hσ
  subst hσ
  exact hi

/-- **`OSrcPrem.ostBound`**: the coordinate of a rescale store is below the thread's
`num_iters`. -/
theorem ostBound_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {K : Kernel} {A : List Assumption}
    (G : SrPkg L K A mem0 X) : ∀ c, c < L.grid → ∀ {t sk i a : Nat} {vals : List Value}
      {sh : TcShape}, OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk i a vals sh →
      i < Q.numIters (reqOf L t) (splitOf L t) := by
  intro c _ t sk i a vals sh hO
  obtain ⟨ht, htc, -⟩ := hO.gate.soft
  obtain ⟨d, -, -, hi, hb⟩ := stO_iter hpre hX hf hO ht htc
  rw [← hi]
  exact hb

/-- **The states after a rescale store.** At an event after the state `d` at `stO`, a softmax state
is in a later iteration or in the same iteration at a site that follows the store. -/
theorem after_stO {k : Nat} {d : Sm.D}
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .stO) :
    ∀ m, k ≤ m → m ≤ (X.tr g).length → ∀ s : DComp.St,
      St Q L X g m = some (some (.d s)) →
      ¬ PreSt s ∧ ∀ d', s = .sm d' → (m = k ∧ d' = d) ∨
        (k < m ∧ (d.i < d'.i ∨ (d'.i = d.i ∧ AfterStO d'.site))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hkm hm s hσm
    rcases Nat.eq_or_lt_of_le hkm with rfl | hlt
    · rw [hσ] at hσm
      simp only [Option.some.injEq, TSt.d.injEq] at hσm
      subst hσm
      exact ⟨by simp [PreSt], fun d' h => by
        simp only [DComp.St.sm.injEq] at h
        exact Or.inl ⟨rfl, h.symm⟩⟩
    · rcases pred_d hm hσm with ⟨rfl, -⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
      · omega
      · obtain ⟨hp0, hr0⟩ := ih k0 (by omega) (by omega) (by omega) s0 hσ0
        refine ⟨fun hp => hp0 (dnext_pre hn hp), fun d' hd' => ?_⟩
        subst hd'
        rcases dnext_sm hn with ⟨dp, rfl, -⟩ | ⟨d0, rfl, hn0⟩
        · exact absurd trivial hp0
        · have hr := hr0 d0 rfl
          right
          refine ⟨by omega, ?_⟩
          rcases next_iter hn0 with hi | ⟨hi, -⟩
          · rcases hr with ⟨-, rfl⟩ | ⟨-, hr | ⟨hi0, hA⟩⟩
            · right
              exact ⟨hi, next_afterStO hn0 (Or.inl hs) hi⟩
            · left; omega
            · right
              exact ⟨by omega, next_afterStO hn0 (Or.inr hA) hi⟩
          · left
            rcases hr with ⟨-, rfl⟩ | ⟨-, hr | ⟨hi0, hA⟩⟩ <;> omega

/-- **`OAccPrem.ostIter`**: the rescale stores of one thread are in the order of the
iterations. -/
theorem oaccOstIter_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {K : Kernel} {A : List Assumption}
    (G : SrPkg L K A mem0 X) :
    ∀ c, c < L.grid → ∀ {t sk sk' i i' a a' : Nat} {vals vals' : List Value}
      {sh sh' : TcShape},
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk i a vals sh →
    OSt L X c (G.p0 c) (G.Soft c) (G.tm c) t sk' i' a' vals' sh' →
    (sk < sk' → i < i') ∧ (sk = sk' → i = i') := by
  intro c _ t sk sk' i i' a a' vals vals' sh sh' hO hO'
  obtain ⟨ht, htc, -⟩ := hO.gate.soft
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · obtain ⟨d, hσ, hds, hi, -⟩ := stO_iter hpre hX hf hO ht htc
    obtain ⟨d', hσ', hds', hi', -⟩ := stO_iter hpre hX hf hO' ht htc
    obtain ⟨pcs', hget'⟩ := hO'.event
    have hk' : sk' ≤ (X.tr t).length := (len_of_get hget').le
    obtain ⟨-, hr⟩ := after_stO hσ hds sk' hlt.le hk' _ hσ'
    rcases hr d' rfl with ⟨h1, -⟩ | ⟨-, hr | ⟨hi0, hA⟩⟩
    · omega
    · omega
    · rw [hds'] at hA
      exact absurd hA (by simp [AfterStO])
  · subst heq
    rw [← hO.polls, ← hO'.polls]

end
end PTX.Kernels.InklingRelDecode.Proof.Rr
