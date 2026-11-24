-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5PeerPair
public import Kernels.InklingRelDecode.Proof.Interface.Lk5VShfl
public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg
public import Kernels.InklingRelDecode.Proof.Thread.Lk5WStepT

@[expose] public section

/-!
# A thread's shared numbers along its trace, by iteration

The shared numbers `Sm.pf` (entry numbers, running maximum, decision, new maximum) and `alpha` of a
softmax state are fixed by the thread's state at the exchange of the row maximum (`shfl5`) of the
iteration, or of the previous one, and the word it received there (`WInv`):

* before the stage's second exchange of iteration 0: the region's first state's;
* before it in a later iteration `i`: `pfU` of the state after the exchange of iteration `i - 1`;
* from the second exchange to the update: those of the state after the exchange of iteration `i`,
  and its `alpha`;
* after the update: `pfU` of that state.

`wInv` proves it along the trace. `sm_shfl_unique`: a thread has one state at a shuffle site of
one iteration (the count of shuffles names it).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The thread's exchange of the row maximum of iteration `j`, before index `k`, with the property
`P` of its state and the received word. -/
def Wit (Q : Params) (L : Launch) (X : Execution) (g k j : Nat) (P : Sm.D → Value → Prop) :
    Prop :=
  ∃ (k0 : Nat) (d0 : Sm.D) (r : Value) (o : Bool), k0 < k ∧
    St Q L X g k0 = some (some (.d (.sm d0))) ∧ d0.site = .shfl5 ∧ d0.i = j ∧
    X.get (g, k0) = some ⟨d0.site.pc, .shfl .bfly d0.ownW 16 31 r o⟩ ∧
    d0.e.Ok ∧ P d0 r

theorem Wit.mono {k k' j : Nat} {P : Sm.D → Value → Prop} (h : Wit Q L X g k j P)
    (hk : k ≤ k')
    {P' : Sm.D → Value → Prop} (hP : ∀ d0 r, P d0 r → P' d0 r) : Wit Q L X g k' j P' := by
  obtain ⟨k0, d0, r, o, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨k0, d0, r, o, by omega, h2, h3, h4, h5, h6, hP _ _ h7⟩

/-- **The shared numbers of a softmax state, from the exchanges of the row maximum.** -/
def WInv (Q : Params) (L : Launch) (X : Execution) (g k : Nat) (d : Sm.D) : Prop :=
  (Late d.site = false → d.i = 0 → ∃ k1 d1, k1 ≤ k ∧
    St Q L X g k1 = some (some (.d (.sm d1))) ∧ d1.site = .setMaxReg ∧ pf d = pf d1) ∧
  (Late d.site = false → 1 ≤ d.i →
    Wit Q L X g k (d.i - 1) (fun d0 r => pf d = pfU (d0.afterS L g r))) ∧
  (Late d.site = true → PostU d.site = false → Wit Q L X g k d.i (fun d0 r =>
    pf d = pf (d0.afterS L g r) ∧ d.stg.al = (d0.afterS L g r).stg.al ∧
      d.stg.alr = (d0.afterS L g r).stg.alr)) ∧
  (PostU d.site = true → Wit Q L X g k d.i (fun d0 r => pf d = pfU (d0.afterS L g r)))

theorem post_late {s : Site} (h : PostU s = true) : Late s = true := by
  cases s <;> simp_all [PostU, Late]

/-- **`WInv` along the trace.** -/
theorem wInv (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ {d : Sm.D}, St Q L X g k = some (some (.d (.sm d))) →
      WInv Q L X g k d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ
    rcases pred_sm_pro hk hσ with ⟨k0, dp, -, -, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · refine ⟨fun _ _ => ⟨k, _, le_rfl, hσ, rfl, rfl⟩, fun _ h => ?_, fun h => ?_,
        fun h => ?_⟩
      · simp [SmEntry.d0] at h
      · simp [SmEntry.d0, Late] at h
      · simp [SmEntry.d0, PostU] at h
    have I0 := ih k0 (by omega) (by omega) hσ0
    obtain ⟨A1, A2, A3, A4⟩ := I0
    have he' : X.get (g, k0) = some e := he
    by_cases h5 : d0.site = .shfl5
    · -- the exchange of the row maximum
      obtain ⟨u, hF⟩ := fired_cont hX hf hg he' hσ0 (by simp [ExitState])
      obtain ⟨recv, ok, he5⟩ := Sm.shape_shfl5 (fired_sm hF) h5
      obtain ⟨m, av, bv, cv, r, o, hk, rfl⟩ := Sm.next_shfl5_eq h5 hn
      have hr : r = recv := by
        rw [he5] at hk
        exact (shflKind_recv hk).symm
      rw [← hr] at he5
      have hok : d0.e.Ok := by
        obtain ⟨t, ins, o', -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he' hσ0
        exact hinv.2.ok
      have hw : Wit Q L X g (k0 + 1) d0.i (fun d1 r' => pf (d0.afterS L g r) =
          pf (d1.afterS L g r') ∧ (d0.afterS L g r).stg.al = (d1.afterS L g r').stg.al ∧
            (d0.afterS L g r).stg.alr = (d1.afterS L g r').stg.alr) :=
        ⟨k0, d0, r, ok, by omega, hσ0, h5, rfl, by rw [he', he5, h5]; rfl, hok, rfl, rfl, rfl⟩
      have hsite := Sm.afterS_site L g d0 r
      refine ⟨fun h => ?_, fun h => ?_, fun _ _ => ?_, fun h => ?_⟩
      · rw [hsite] at h; cases h
      · rw [hsite] at h; cases h
      · rw [Sm.afterS_i]; exact hw
      · rw [hsite] at h; cases h
    · have hpf := step_pf hn h5
      have hal := step_al hn h5
      rcases Interface.next_iter hn with hi | ⟨hi, hs0, hsite⟩
      · -- the same iteration
        by_cases hl0 : Late d0.site = true
        · by_cases hp0 : PostU d0.site = true
          · have hp : PostU d.site = true := post_next hn hp0 hi
            have hpf' : pf d = pf d0 := by
              rcases hpf with ⟨hb, -⟩ | ⟨-, hpf⟩
              · exact absurd hb (post_not_bar20 hn hp0)
              · exact hpf
            refine ⟨fun h => absurd ((post_late hp).symm.trans h) (by decide),
              fun h => absurd ((post_late hp).symm.trans h) (by decide),
              fun _ h => absurd (hp.symm.trans h) (by decide), fun _ => ?_⟩
            rw [hi]
            exact (A4 hp0).mono (by omega) (fun d1 r h => hpf'.trans h)
          · have hp0' : PostU d0.site = false := by simpa using hp0
            have hl : Late d.site = true := late_next hn hl0 hi
            obtain ⟨k1, d1, r, o, h1, h2, h3, h4, h5', h6, hpa, hala, halr⟩ := A3 hl0 hp0'
            rcases hpf with ⟨hb, hpf⟩ | ⟨hb, hpf⟩
            · have hp : PostU d.site = true := by rw [hb]; rfl
              refine ⟨fun h => absurd (hl.symm.trans h) (by decide),
                fun h => absurd (hl.symm.trans h) (by decide),
                fun _ h => absurd (hp.symm.trans h) (by decide), fun _ => ?_⟩
              rw [hi]
              exact ⟨k1, d1, r, o, by omega, h2, h3, h4, h5', h6, hpf.trans (pfU_congr hpa)⟩
            · have hp : PostU d.site = false := by
                cases hq : PostU d.site
                · rfl
                · exact absurd (pre_to_post hn hl0 hp0' hq) hb
              refine ⟨fun h => absurd (hl.symm.trans h) (by decide),
                fun h => absurd (hl.symm.trans h) (by decide),
                fun _ _ => ?_, fun h => absurd (hp.symm.trans h) (by decide)⟩
              rw [hi]
              exact ⟨k1, d1, r, o, by omega, h2, h3, h4, h5', h6, hpf.trans hpa,
                hal.1.trans hala, hal.2.trans halr⟩
        · have hl0' : Late d0.site = false := by simpa using hl0
          have hl : Late d.site = false := early_next hn hl0' h5
          have hpf' : pf d = pf d0 := by
            rcases hpf with ⟨hb, -⟩ | ⟨-, hpf⟩
            · rw [hb] at hl; cases hl
            · exact hpf
          refine ⟨fun _ hi0 => ?_, fun _ hi1 => ?_, fun h => absurd (hl.symm.trans h) (by decide),
            fun h => absurd ((post_late h).symm.trans hl) (by decide)⟩
          · obtain ⟨k1, d1, h1, h2, h3, h4⟩ := A1 hl0' (by omega)
            exact ⟨k1, d1, by omega, h2, h3, hpf'.trans h4⟩
          · rw [hi]
            exact (A2 hl0' (by omega)).mono (by omega) (fun d1 r h => hpf'.trans h)
      · -- the iteration rises at `bar21` or `arrive`
        have hp0 : PostU d0.site = true := by rcases hs0 with h | h <;> rw [h] <;> rfl
        have hl : Late d.site = false := by rcases hsite with h | h <;> rw [h] <;> rfl
        have hpf' : pf d = pf d0 := by
          rcases hpf with ⟨hb, -⟩ | ⟨-, hpf⟩
          · rw [hb] at hl; cases hl
          · exact hpf
        refine ⟨fun _ h => by omega, fun _ _ => ?_, fun h => absurd (hl.symm.trans h) (by decide),
          fun h => absurd ((post_late h).symm.trans hl) (by decide)⟩
        rw [hi, Nat.add_sub_cancel]
        exact (A4 hp0).mono (by omega) (fun d1 r h => hpf'.trans h)

/-- **A thread has one state at a shuffle site of an iteration.** -/
theorem sm_shfl_unique (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k k' : Nat} {d d' : Sm.D}
    {e : Event} (he : X.get (g, k) = some e) (hk' : k' ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hσ' : St Q L X g k' = some (some (.d (.sm d')))) (hsh : Sm.smShfl d.site = true)
    (hs : d'.site = d.site) (hi : d'.i = d.i) : k = k' := by
  have c1 := (cnt_inv hpre hX hf hg k (event_le he) hσ).1
  have c2 := (cnt_inv hpre hX hf hg k' hk' hσ').1
  have hw : Sm.smW d' = Sm.smW d := by simp only [Sm.smW, hs, hi]
  simp only [cntF, hw] at c1 c2
  have step : ∀ {a b : Nat} {da : Sm.D} {ea : Event}, X.get (g, a) = some ea →
      St Q L X g a = some (some (.d (.sm da))) → Sm.smShfl da.site = true → a < b →
      cnt Execution.isShfl X g a < cnt Execution.isShfl X g b := by
    intro a b da ea hea hσa hsa hab
    have hsh : shflSt (.d (.sm da)) = true := by
      show shflPc da.site.pc = true
      rw [sm_shfl]; exact hsa
    have h1 := cnt_succ Execution.isShfl (X := X) (g := g) (show (X.tr g)[a]? = some ea from hea)
    rw [isShfl_state hX hf hg hea hσa, hsh] at h1
    have h2 := cnt_mono Execution.isShfl (X := X) g (show a + 1 ≤ b by omega)
    simp only [↓reduceIte] at h1
    omega
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have := step he hσ hsh h; omega
  · exact h
  · obtain ⟨e', he'⟩ : ∃ e', X.get (g, k') = some e' :=
      ⟨_, List.getElem?_eq_getElem (show k' < (X.tr g).length by have := event_le he; omega)⟩
    have := step he' hσ' (hs ▸ hsh) h; omega

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
