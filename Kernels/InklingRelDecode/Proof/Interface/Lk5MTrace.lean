-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5Defs
public import Kernels.InklingRelDecode.Proof.Thread.Lk5MCross
public import Kernels.InklingRelDecode.Proof.Interface.RdDPred
public import Kernels.InklingRelDecode.Proof.Interface.FootPhase

@[expose] public section

/-!
# The softmax region along a thread's trace: rank, barriers, iterations

* `rank_mono_m`: along a thread's trace the rank of its softmax states (`Sm.D.rank`: the iteration,
  then the site's place in the loop) does not fall. A softmax state is reached from a softmax
  state or from the prologue, and no prologue state follows a softmax state (the prologue's states
  have no barrier-1 event before them, the softmax region's at least one);
* `back23`, `back21`: a softmax state of a higher rank than `bar23` of iteration `i0 ≥ 1` (than
  `bar21` of iteration `i0`) is preceded by a state at that site and iteration;
* `midOk_state`: the sites between the `o_done` poll and the O rescale are in iterations `i ≥ 1`;
* `bar_event`: a softmax state at `bar20` … `bar24` fires `bar.sync 0, 128`, and `bar_cnt`: the
  count of barrier-0 events rises by one over it.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Sm PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The predecessor of a softmax state -/

theorem smNext_sm {s0 : DComp.St} {d : Sm.D} {e : Event}
    (h : DComp.next L g Q s0 e = some (some (DComp.St.sm d))) :
    (∃ d0, s0 = .sm d0 ∧ Sm.next L g d0 e = some (some d)) ∨
      (∃ d0, s0 = .dstart d0) ∨ (∃ d0, s0 = .pro d0) := by
  cases s0 with
  | dstart dd => exact .inr (.inl ⟨dd, rfl⟩)
  | pro dp => exact .inr (.inr ⟨dp, rfl⟩)
  | sm d0 =>
    left
    change DComp.smNext L g d0 e = _ at h
    unfold DComp.smNext at h
    split at h
    · unfold DComp.exitNext at h
      split at h
      · cases h
      · cases h
    · obtain ⟨a, ha, hs⟩ := map_map_eq_some_some h
      simp only [DComp.St.sm.injEq] at hs
      subst hs
      exact ⟨d0, rfl, ha⟩
  | epi de =>
    exfalso
    change (Epi.next de e).map (Option.map DComp.St.epi) = _ at h
    obtain ⟨a, -, ha⟩ := map_map_eq_some_some h
    cases ha

theorem b1N_mono (X : Execution) (g : Nat) {j k : Nat} (h : j ≤ k) : b1N X g j ≤ b1N X g k := by
  unfold b1N
  have : (X.tr g).take j = ((X.tr g).take k).take j := by
    rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact (List.take_sublist _ _).countP_le

/-- A softmax state is of a default-partition thread. -/
theorem sm_default {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : g % L.block < 128 :=
  (cls_inv k _ hk hσ).mp trivial

/-- **A softmax state has a barrier-1 event before it.** -/
theorem sm_b1N (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {k : Nat} {d : Sm.D}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    1 ≤ b1N X g k := by
  obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hS (sm_default hk hσ) k _ hk hσ
  cases hd'
  rw [h]
  simp only [dPh]
  split <;> simp

/-- **The rank does not fall along the trace.** -/
theorem rank_mono_m (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound) {a : Nat} {da : Sm.D}
    (ha : St Q L X g a = some (some (.d (.sm da)))) :
    ∀ b, a ≤ b → b ≤ (X.tr g).length → ∀ {db : Sm.D},
      St Q L X g b = some (some (.d (.sm db))) → da.rank ≤ db.rank := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ db hb
    rw [ha] at hb
    cases hb
    exact le_rfl
  | succ b hab ih =>
    intro hlen db hb
    rcases pred_d hlen hb with ⟨h0, -⟩ | ⟨k0, e, s0, hk0, he, hσ0, hn⟩
    · omega
    · have hk0' : k0 = b := by omega
      subst hk0'
      rcases smNext_sm hn with ⟨d0, rfl, hn'⟩ | ⟨d0, rfl⟩ | ⟨d0, rfl⟩
      · exact le_trans (ih (by omega) hσ0) (next_rank hn')
      · exfalso
        have h1 := sm_b1N hpre hX hS (by omega) ha
        have h2 := b1N_mono X g hab
        obtain ⟨d', hd', h3⟩ := dphase_inv hpre hX hS (sm_default (by omega) ha) k0 _
          (by omega) hσ0
        cases hd'
        simp [dPh] at h3
        omega
      · exfalso
        have h1 := sm_b1N hpre hX hS (by omega) ha
        have h2 := b1N_mono X g hab
        obtain ⟨d', hd', h3⟩ := dphase_inv hpre hX hS (sm_default (by omega) ha) k0 _
          (by omega) hσ0
        cases hd'
        simp only [dPh] at h3
        split at h3 <;> simp at h3 <;> omega

/-! ### The states before a state of higher rank -/

theorem entry_rank (Q : Params) (L : Launch) (g : Nat) (dt : ProA.Dat) :
    (SmEntry.d0 (SmEntry.entOf Q L g dt)).rank = 0 := by
  simp [D.rank, SmEntry.d0, Site.ord]

/-- **`bar23` of iteration `i0 ≥ 1` precedes every softmax state of higher rank.** -/
theorem back23 {i0 : Nat} (hi : 1 ≤ i0) :
    ∀ b, b ≤ (X.tr g).length → ∀ {db : Sm.D}, St Q L X g b = some (some (.d (.sm db))) →
      64 * i0 + 17 < db.rank →
      ∃ b' d', b' < b ∧ St Q L X g b' = some (some (.d (.sm d'))) ∧ d'.site = .bar23 ∧
        d'.i = i0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb db hσ hr
    rcases Sv.pred_sm hb hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · rw [entry_rank] at hr
      omega
    · by_cases h0 : 64 * i0 + 17 < d0.rank
      · obtain ⟨b', d', h1, h2, h3, h4⟩ := ih k0 (by omega) (by omega) hσ0 h0
        exact ⟨b', d', by omega, h2, h3, h4⟩
      · obtain ⟨h1, h2⟩ := cross23 hn (by omega) hr hi
        exact ⟨k0, d0, by omega, hσ0, h1, h2⟩

/-- **`bar21` of iteration `i0` precedes every softmax state of higher rank.** -/
theorem back21 {i0 : Nat} :
    ∀ b, b ≤ (X.tr g).length → ∀ {db : Sm.D}, St Q L X g b = some (some (.d (.sm db))) →
      64 * i0 + 29 < db.rank →
      ∃ b' d', b' < b ∧ St Q L X g b' = some (some (.d (.sm d'))) ∧ d'.site = .bar21 ∧
        d'.i = i0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb db hσ hr
    rcases Sv.pred_sm hb hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · rw [entry_rank] at hr
      omega
    · by_cases h0 : 64 * i0 + 29 < d0.rank
      · obtain ⟨b', d', h1, h2, h3, h4⟩ := ih k0 (by omega) (by omega) hσ0 h0
        exact ⟨b', d', by omega, h2, h3, h4⟩
      · obtain ⟨h1, h2⟩ := cross21 hn (by omega) hr
        exact ⟨k0, d0, by omega, hσ0, h1, h2⟩

/-- **The sites of the rescale test are in iterations `i ≥ 1`.** -/
theorem midOk_state :
    ∀ k, k ≤ (X.tr g).length → ∀ {d : Sm.D}, St Q L X g k = some (some (.d (.sm d))) →
      MidOk d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ
    rcases Sv.pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · intro h
      simp [SmEntry.d0, MidSite] at h
    · exact next_midOk (ih k0 (by omega) (by omega) hσ0) hn

/-! ### The barriers of the loop -/

/-- The barrier sites of the loop. -/
def BarSite : Sm.Site → Prop
  | .bar20 | .bar21 | .bar22 | .bar23 | .bar24 => True
  | _ => False

/-- **A softmax state at a barrier site fires `bar.sync 0, 128`.** -/
theorem bar_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : BarSite d.site) : e = ⟨d.site.pc, .bar 0 (some 128) .sync⟩ := by
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  have hF' := fired_sm hF
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  unfold BarSite at hs
  split at hs
  · exact shape_bar20 hb hF' (by assumption)
  · exact shape_bar21 hb hF' (by assumption)
  · exact shape_bar22 hb hF' (by assumption)
  · exact shape_bar23 hb hF' (by assumption)
  · exact shape_bar24 hb hF' (by assumption)
  · exact hs.elim

/-- **The count of barrier-0 events rises by one over a barrier state.** -/
theorem bar_cnt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {k : Nat} {d : Sm.D} {e : Event} (hg : g < L.threads)
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d (.sm d))))
    (hs : BarSite d.site) :
    cnt (Execution.isBarId 0) X g (k + 1) = cnt (Execution.isBarId 0) X g k + 1 := by
  have h := cnt_succ (Execution.isBarId 0) (X := X) (g := g) (show (X.tr g)[k]? = some e from he)
  rw [bar_event hpre hX hf hg he hσ hs] at h
  simpa [Execution.isBarId] using h

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
