-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Bar1Exit

@[expose] public section

/-! # Barrier 1's count along the default partition

`dp_c1`: the barrier-1 events before a state of a thread of warps 0 to 3: none in the startup and
the prologue (one at the prologue's exit, after its `barrier.sync 1`), one at the softmax region's
first two sites (the second is its `barrier.sync 1`), two after them and in the epilogue up to its
first `barrier.sync 1`, three up to its second, four after. The softmax region's machine reaches
its `barrier.sync 1` only from its first site (`sm_pred_bar0`), so the count is exact. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The softmax region reaches its first two sites only from its first.** -/
theorem sm_pred_bar0 {d d' : Proof.Sm.D} {e : Event} (h : Proof.Sm.next L g d e = some (some d'))
    (hs : d'.site = .setMaxReg ∨ d'.site = .bar0) : d.site = .setMaxReg := by
  unfold Proof.Sm.next at h
  split at h
  · rename_i hd; exact hd
  all_goals exfalso
  all_goals
    repeat' first
      | (split at h)
      | (simp only [Proof.Sm.afterSetup, Proof.Sm.afterArrive, Proof.Sm.toBar20] at h)
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp_all [Proof.Sm.D.afterSum])


local macro "site_cls1" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem proA_site_bar1 (s : ProA.Site) (h : s.pc ∈ bar1Pcs) : s = .bar18 := by
  cases s with
  | bar18 => rfl
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

theorem sm_bar1 : ∀ s : Proof.Sm.Site, s.pc ∈ bar1Pcs → s = .bar0 := by site_cls1
theorem epi_bar1 : ∀ s : Proof.Epi.Site, s.pc ∈ bar1Pcs → s = .bar1 ∨ s = .bar2 := by
  site_cls1
theorem startup_bar1 : ∀ s : Startup.Site, s.pc ∈ bar1Pcs → False := by
  intro s h; revert h
  cases s with
  | enter r => cases r <;> decide
  | _ => decide

/-- The prologue's phase: one barrier-1 event at its exit. -/
def proPh (d : ProA.D) : Nat := if d.site = .exit then 1 else 0

/-- The softmax region's phase: one barrier-1 event at its first two sites, two after. -/
def smPh (d : Proof.Sm.D) : Nat := if d.site = .setMaxReg ∨ d.site = .bar0 then 1 else 2

/-- The epilogue's phase. -/
def epiPh (d : Proof.Epi.D) : Nat :=
  match d.site with
  | .setMaxInc | .stTab | .bar2 => 3
  | .bar3 | .dealloc | .exit => 4
  | _ => 2

/-- **The barrier-1 count of a default-partition state.** -/
def C1 (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inl _, _), c => c = 0
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), c => c = proPh d
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _), c => c = smPh d
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi d⟩⟩, _), c => c = epiPh d
  | _, _ => True

theorem epi_next_ph {d d' : Proof.Epi.D} {e : Event} (h : Proof.Epi.next d e = some (some d')) :
    epiPh d' = epiPh d + (if d.site = .bar1 ∨ d.site = .bar2 then 1 else 0) := by
  unfold Proof.Epi.next at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [epiPh, Proof.Epi.D.stores, Proof.Epi.stNext]
       done)
    | (simp only [Option.some.injEq] at h; subst h
       simp_all [epiPh, Proof.Epi.D.stores, Proof.Epi.stNext]
       split_ifs <;> simp_all)

theorem bar18_next {dt : Proof.ProA.Dat} {e : Event} {d' : ProA.D}
    (h : ProA.next L g ⟨.bar18, dt⟩ e = some (some d')) : d'.site = .exit := by
  simp only [ProA.next] at h
  split at h
  · cases h
  · simp only [ProA.next0, Option.some.injEq] at h
    rw [← h]

theorem isBarId1_kind {e : Event} (h : Execution.isBarId 1 e = true) :
    ∃ c md, e.kind = .bar 1 c md := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp [Execution.isBarId] at h
  subst h
  exact ⟨_, _, rfl⟩

/-- An event whose instruction is not a `barrier.sync 1` is no barrier-1 event. -/
theorem notBar1 {pc : Nat} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hb : L.block ≠ 128)
    (hpc : pc ∉ bar1Pcs) : Execution.isBarId 1 e = false := by
  cases h : Execution.isBarId 1 e with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨c, md, hk⟩ := isBarId1_kind h
    exact hpc (bar1_pc hc hf hk hb)

/-- **A continuing step keeps the default partition's barrier-1 count.** -/
theorem c1_step (hp : Pre Q L m) (hg : g < L.threads) {σ σ' : (thread Q L g).D} {e : Event}
    {t u : TState} {ins : Instr} (hJ : Ref Q L g σ) (hat : (thread Q L g).AtD σ t)
    (hi : (thread Q L g).inv σ) (hc : kernel.code[(thread Q L g).pc σ]? = some ins)
    (hf : Fires ((thread Q L g).pc σ) (eventTmpl Assumptions.all L g t ins.op) e (some u))
    {c : Nat} (hC : C1 Q L g σ c) (hn : (thread Q L g).next σ e = some (some σ')) :
    C1 Q L g σ' (c + if Execution.isBarId 1 e then 1 else 0) := by
  have hb : L.block ≠ 128 := by rw [hp.block]; decide
  have hev := frag_ev hp hg hJ hat hi hc hf
  obtain ⟨x, n⟩ := σ
  rcases x with s | ⟨_ | r, d⟩
  · have hC' : c = 0 := hC
    have hnb : Execution.isBarId 1 e = false :=
      notBar1 hc hf hb (fun h => startup_bar1 s.site h)
    rw [hnb]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    rw [next_start] at hn
    obtain ⟨s', -, rfl⟩ := mm_some hn
    simp only [Code.enter]
    split
    · rename_i j _
      rcases j with (_ | _) | _
      · show _ = proPh _
        rw [hC']
        rfl
      · trivial
      · trivial
    · exact hC'
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · have hC' : c = proPh d := hC
        have hx : d.site ≠ .exit := fun h => by
          simp [Code.gatedExit, ProA.exitOf, h] at hi
        rw [next_pro] at hn
        obtain ⟨d', hd', rfl⟩ := mm_some hn
        by_cases hs : d.site = .bar18
        · have hbe : Execution.isBarId 1 e = true := by
            have hc' : kernel.code[573]? = some ins := by
              have : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = 573 := by
                show d.site.pc = 573; rw [hs]; rfl
              rw [← this]; exact hc
            rw [Flow.code_bar_18] at hc'
            obtain rfl := Option.some.inj hc'
            have hf' := hf
            have : (thread Q L g).pc (.inr ⟨.inl (.dp tm bw), .inl d⟩, n) = 573 := by
              show d.site.pc = 573; rw [hs]; rfl
            rw [this] at hf'
            rw [Proof.EvD.fires_barSync_imm (id := 1) (by omega) hf']
            rfl
          rw [hbe]
          obtain ⟨site, dt⟩ := d
          simp only at hs
          subst hs
          have hx' := bar18_next hd'
          have hpo : proPh ⟨.bar18, dt⟩ = 0 := rfl
          rw [hC', hpo]
          cases hxo : ProA.exitOf d' with
          | none => simp [ProA.exitOf, hx'] at hxo
          | some v =>
            cases hsel : ProA.selTail Q L g v d' with
            | some dt' =>
              rw [Code.enter_some (i := Sum.inl dt') (by simp [Code.gatedExit, hxo, hsel])]
              rfl
            | none =>
              rw [Code.enter_some (i := Sum.inr ()) (by simp [Code.gatedExit, hxo, hsel])]
              trivial
        · have hnb : Execution.isBarId 1 e = false :=
            notBar1 hc hf hb (fun h => hs (proA_site_bar1 d.site h))
          rw [hnb]
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          have hpo : proPh d = 0 := by simp [proPh, hx]
          cases hxo : ProA.exitOf d' with
          | none =>
            rw [Code.enter_none (by simp [Code.gatedExit, hxo])]
            show c = proPh d'
            have hx' : d'.site ≠ .exit := fun h => by simp [ProA.exitOf, h] at hxo
            rw [hC', hpo]
            simp [proPh, hx']
          | some v =>
            have hx' : d'.site = .exit := by
              obtain ⟨site, dt⟩ := d'
              cases site <;> simp_all [ProA.exitOf]
            exact absurd (exit_from_bar18 hd' hx') hs
      · rw [next_tail] at hn
        obtain ⟨τ', hτ, rfl⟩ := mm_some hn
        cases τ with
        | sm d =>
          have hC' : c = smPh d := hC
          by_cases hs : d.site = .bar0
          · have hbe : Execution.isBarId 1 e = true := by
              have h' := hev
              simp only [FragEv, Proof.Sm.Shape, hs] at h'
              rw [h']; rfl
            rw [hbe]
            have h1 : smPh d = 1 := by simp [smPh, hs]
            simp only [Tail.next] at hτ
            split at hτ
            · simp only [Tail.exitNext] at hτ
              split at hτ
              · simp only [Option.some.injEq] at hτ
                subst hτ
                show _ = epiPh _
                simp [epiPh, Proof.Epi.D.entry, hC', h1]
              · cases hτ
            · obtain ⟨d', hd', rfl⟩ := mm_some hτ
              show _ = smPh d'
              have hn' : ¬ (d'.site = .setMaxReg ∨ d'.site = .bar0) := fun h => by
                have := sm_pred_bar0 hd' h
                rw [hs] at this
                cases this
              simp [smPh, hn', hC', hs]
          · have hnb : Execution.isBarId 1 e = false :=
              notBar1 hc hf hb (fun h => hs (sm_bar1 d.site h))
            rw [hnb]
            simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            simp only [Tail.next] at hτ
            split at hτ
            · rename_i hl
              have hns : d.site ≠ .setMaxReg := fun h => by
                simp [Proof.DComp.leaves, h] at hl
              simp only [Tail.exitNext] at hτ
              split at hτ
              · simp only [Option.some.injEq] at hτ
                subst hτ
                show _ = epiPh _
                have h2 : smPh d = 2 := by simp [smPh, hs, hns]
                simp [epiPh, Proof.Epi.D.entry, hC', h2]
              · cases hτ
            · obtain ⟨d', hd', rfl⟩ := mm_some hτ
              show _ = smPh d'
              by_cases hm : d.site = .setMaxReg
              · have : d'.site = .bar0 := by
                  simp only [Proof.Sm.next, hm, Option.some.injEq] at hd'
                  rw [← hd']
                simp [smPh, this, hC', hm]
              · have hn' : ¬ (d'.site = .setMaxReg ∨ d'.site = .bar0) := fun h =>
                  hm (sm_pred_bar0 hd' h)
                simp [smPh, hn', hC', hm, hs]
        | epi d =>
          have hC' : c = epiPh d := hC
          simp only [Tail.next] at hτ
          obtain ⟨d', hd', rfl⟩ := mm_some hτ
          show _ = epiPh d'
          rw [epi_next_ph hd', hC']
          by_cases hs : d.site = .bar1 ∨ d.site = .bar2
          · have hbe : Execution.isBarId 1 e = true := by
              have h' := hev
              rcases hs with hs | hs <;> simp only [FragEv, Proof.Epi.Shape, hs] at h' <;>
                rw [h'] <;> rfl
            simp [hbe, hs]
          · have hnb : Execution.isBarId 1 e = false :=
              notBar1 hc hf hb (fun h => hs (epi_bar1 d.site h))
            simp [hnb, hs]
      · exact hJ.elim
    | worker w =>
      rw [next_worker] at hn
      obtain ⟨_, -, rfl⟩ := mm_some hn
      trivial
  · exact hJ.elim

/-- **The default partition's barrier-1 count along a thread.** -/
theorem c1_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      C1 Q L g σ (((X.tr g).take k).countP (Execution.isBarId 1)) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    rfl
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX (k := k) he hk0
      cases o with
      | none => exact absurd (fires_none_ends hf) (not_ends_of_lt hX hg he hk)
      | some u =>
        rw [List.take_add_one, he, Option.toList_some, countP_snoc]
        exact c1_step hp hg (hF.2 σ hk0) hat hi hc hf (ih hlt σ hk0) hn

end
end PTX.Kernels.InklingRelDecode.Proof2
