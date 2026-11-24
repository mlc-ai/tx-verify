-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.RdSmBack
public import Kernels.InklingRelDecode.Proof.Interface.ExitFacts

@[expose] public section

/-!
# Every softmax thread reaches the `P` store of every iteration

The progress statement behind the existence of the covering `P` store of each tile cell
(`Rs.PReadSrc`): in a complete execution a launched thread of the default partition passes the
site `tmemSt` of every iteration `i < num_iters`.

* `dnext_epi`, `epi_back`: the epilogue's first state follows the softmax state at the event that
  leaves the loop (`DComp.leaves`);
* `next_iter`: the loop counter of the region rises only at `bar21` and `arrive`;
* `bar21_back`: a softmax state in a later iteration, or at `bar21` or `arrive` of iteration `i0`,
  is preceded by the state at `bar21` of iteration `i0`;
* `sm_reaches_tmemSt`: the thread has a state at `tmemSt` of iteration `i0` (the `P` store).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Sv

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The states the epilogue's states come from: the softmax region at the event that leaves the
loop, or the epilogue. -/
theorem dnext_epi {s0 : DComp.St} {de : Epi.D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.epi de))) :
    (∃ d0, s0 = .sm d0 ∧ DComp.leaves L g d0 e) ∨ ∃ de0, s0 = .epi de0 := by
  cases s0 with
  | dstart dd =>
    change DComp.dstartNext L g Q dd e = _ at h
    unfold DComp.dstartNext at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    split at ha <;> cases ha
  | pro dp =>
    change DComp.proNext L g Q dp e = _ at h
    unfold DComp.proNext at h
    split at h
    · split at h <;> cases h
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | sm d0 =>
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · rename_i hl
      exact Or.inl ⟨d0, rfl, hl⟩
    · obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
      cases ha
  | epi de0 => exact Or.inr ⟨de0, rfl⟩

/-- **The state before the epilogue.** An epilogue state at event `k` follows, at an earlier
event, a softmax state whose event leaves the loop. -/
theorem epi_back : ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {d : Epi.D},
    St Q L X g k = some (some (.d (.epi d))) →
    ∃ (k0 : Nat) (e : Event) (d0 : Sm.D), k0 < k ∧ (X.tr g)[k0]? = some e ∧
      St Q L X g k0 = some (some (.d (.sm d0))) ∧ DComp.leaves L g d0 e := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ
    rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · exfalso
      cases h0
    · rcases dnext_epi hn with ⟨d0, rfl, hl⟩ | ⟨de0, rfl⟩
      · exact ⟨k0, e, d0, by omega, he, hσ0, hl⟩
      · obtain ⟨k1, e1, d1, hk1, he1, hσ1, hl1⟩ := ih k0 (by omega) (by omega) hσ0
        exact ⟨k1, e1, d1, by omega, he1, hσ1, hl1⟩

theorem afterSetup_i {d d' : D} (h : Sm.afterSetup L g d = some (some d')) : d'.i = d.i := by
  unfold Sm.afterSetup at h
  split at h
  · cases h
  · split at h <;> (simp only [Option.some.injEq] at h; subst h; rfl)

theorem toBar20_i {d d' : D} (h : Sm.toBar20 d = some (some d')) : d'.i = d.i := by
  unfold Sm.toBar20 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

/-- **The loop counter rises only at `bar21` and `arrive`.** -/
theorem next_iter {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d)) :
    d.i = d0.i ∨ (d.i = d0.i + 1 ∧ (d0.site = .bar21 ∨ d0.site = .arrive) ∧
      (d.site = .nxt 0 ∨ d.site = .waitS)) := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all [D.afterSum])
    | (have h1 := afterSetup_i hn; left; simpa using h1)
    | (have h1 := toBar20_i hn; left; simpa [D.afterSum, D.upd] using h1)
    | (unfold Sm.afterArrive at hn
       have h1 := afterSetup_i hn
       have h2 := afterSetup_site hn
       right
       simp only at h1
       exact ⟨h1, by simp_all, h2⟩)

/-- The state before `arrive` is `bar21` of the same iteration. -/
theorem next_arrive {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .arrive) : d0.site = .bar21 ∧ d.i = d0.i := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)

/-- The state before `bar21` is `tmemWait` of the same iteration. -/
theorem next_bar21 {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .bar21) : d0.site = .tmemWait ∧ d.i = d0.i := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)

/-- The state before `tmemWait` is `tmemSt` of the same iteration. -/
theorem next_tmemWait {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d))
    (hs : d.site = .tmemWait) : d0.site = .tmemSt ∧ d.i = d0.i := by
  unfold Sm.next at hn
  repeat' split at hn
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
    | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
    | (have := afterSetup_site hn; rcases this with h | h <;> simp_all)
    | (have := toBar20_site hn; simp_all)
    | (simp only [Option.some.injEq] at hn; subst hn; simp [D.afterSum] at hs)

/-- **The state at `bar21` of an iteration.** A softmax state in a later iteration `i0 < d.i`, or at
`bar21` or `arrive` of iteration `i0`, is preceded (or is) a state at `bar21` of iteration
`i0`. -/
theorem bar21_back (i0 : Nat) : ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {d : D},
    St Q L X g k = some (some (.d (.sm d))) →
    (i0 < d.i ∨ (d.i = i0 ∧ (d.site = .bar21 ∨ d.site = .arrive))) →
    ∃ (k' : Nat) (d' : D), k' ≤ k ∧ St Q L X g k' = some (some (.d (.sm d'))) ∧
      d'.site = .bar21 ∧ d'.i = i0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ hc
    by_cases hb : d.i = i0 ∧ d.site = .bar21
    · exact ⟨k, d, le_refl _, hσ, hb.2, hb.1⟩
    rcases pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exfalso
      simp [SmEntry.d0] at hc
    · rcases next_iter hn with hi | ⟨hi, hs0, hsite⟩
      · by_cases harr : d.i = i0 ∧ d.site = .arrive
        · obtain ⟨hs1, hi1⟩ := next_arrive hn harr.2
          exact ⟨k0, d0, by omega, hσ0, hs1, by omega⟩
        · obtain ⟨k1, d1, hk1, hσ1, hs1, hi1⟩ := ih k0 (by omega) (by omega) hσ0
            (by rcases hc with h | ⟨h1, h2 | h2⟩
                · exact Or.inl (by omega)
                · exact absurd ⟨h1, h2⟩ hb
                · exact absurd ⟨h1, h2⟩ harr)
          exact ⟨k1, d1, by omega, hσ1, hs1, hi1⟩
      · have hi0 : i0 ≤ d0.i := by
          rcases hc with h | ⟨h1, h2⟩
          · omega
          · exfalso
            rcases hsite with h | h <;> rcases h2 with h' | h' <;> simp_all
        obtain ⟨k1, d1, hk1, hσ1, hs1, hi1⟩ := ih k0 (by omega) (by omega) hσ0
          (by rcases Nat.lt_or_ge i0 d0.i with h | h
              · exact Or.inl h
              · exact Or.inr ⟨by omega, hs0⟩)
        exact ⟨k1, d1, by omega, hσ1, hs1, hi1⟩


/-- The number of blocks of a split is below `2 ^ 31`. -/
theorem numIters_lt31 (hpre : Pre Q L mem0) {r : Nat} (hr : r < Q.b) (s : Nat) :
    Q.numIters r s < 2 ^ 31 := by
  have h1 := SmEntry.iters_lt Q r s hpre.splitsPos
  have h2 := hpre.seqRange r hr
  unfold Params.blocks at h1
  omega

/-- **Every softmax thread reaches the `P` store of every iteration.** In a complete execution a
launched thread of the default partition has, for each iteration `i0 < num_iters`, a state at the
site `tmemSt` of iteration `i0`, whose event is the `tcgen05.st` of 32 words at the tile address. -/
theorem sm_reaches_tmemSt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hc : Complete L X) (hg : g < L.threads)
    (hdef : g % L.block < 128) {i0 : Nat}
    (hi : i0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ (k : Nat) (ds : D) (pc a : Nat) (vals : List Value),
      St Q L X g k = some (some (.d (.sm ds))) ∧ ds.site = .tmemSt ∧ ds.i = i0 ∧
      X.get (g, k) = some ⟨pc, .tc (.st a vals (.s16x32bx2 32))⟩ ∧ a = Sm.tileAddr L g ds := by
  obtain ⟨kx, pcx, hgetx, hx⟩ := exit_of_complete hX hf.sound hf.tracked hc hg
  have hkx : kx < (X.tr g).length := len_of_get hgetx
  obtain ⟨d, hσx, -⟩ : ∃ d : Epi.D, St Q L X g kx = some (some (.d (.epi d))) ∧ d.site = .exit := by
    rcases hx with h | ⟨x, hσ, -⟩
    · exact h
    · exfalso
      obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hgetx hσ
      have : ¬ IsDefault L g := hinv.1
      exact this hdef
  obtain ⟨k0, e0, d0, hk0, he0, hσ0, hl⟩ := epi_back kx hkx.le hσx
  have hge0 : X.get (g, k0) = some e0 := he0
  have hI := Sv.sm_inv_at hX hf hge0 hσ0
  have hm := ((hf.reach hg hσ0).2 : SmMeans Q L g d0.e)
  have hr25 := hm.ent.r25
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have hn31 := numIters_lt31 hpre hz (ProA.cta L g .x)
  have hr26 : d0.e.r26 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    have h1 := hI.ok.r26
    rw [hr25] at h1
    rw [h1]
    simp only [hn31, ↓reduceIte]
  have hleave := leaveSite_of_leaves hl
  have hlast : d0.i + 1 = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      (d0.site = .bar21 ∨ d0.site = .arrive) := by
    rcases hleave with ⟨hs, he⟩ | ⟨j, hs, he⟩ | ⟨hs, he⟩
    · exfalso
      have := (hI.loop.2 hs).1
      omega
    · exfalso
      have := (hI.loop.1 j hs).1
      omega
    · exact ⟨by omega, hs⟩
  obtain ⟨k', d', hk', hσ', hs', hi'⟩ := bar21_back i0 k0 (by omega) hσ0
    (by rcases Nat.lt_or_ge i0 d0.i with h | h
        · exact Or.inl h
        · exact Or.inr ⟨by omega, hlast.2⟩)
  have hk'l : k' ≤ (X.tr g).length := by omega
  rcases pred_sm hk'l hσ' with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · simp [SmEntry.d0] at hs'
  obtain ⟨hs1, hi1⟩ := next_bar21 hn1 hs'
  rcases pred_sm (by omega) hσ1 with ⟨dt, rfl⟩ | ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
  · simp [SmEntry.d0] at hs1
  obtain ⟨hs2, hi2⟩ := next_tmemWait hn2 hs1
  have hge2 : X.get (g, k2) = some e2 := he2
  obtain ⟨u, hF⟩ := fired_cont hX hf hg hge2 hσ2 (by simp [ExitState])
  obtain ⟨vals, hl32, hw, -, hev⟩ := Sm.shape_tmemSt (fired_sm hF) hs2
  refine ⟨k2, d2, Sm.evPc d2.site, Sm.tileAddr L g d2, vals, hσ2, hs2, by omega, ?_, rfl⟩
  rw [hge2, hev]

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
