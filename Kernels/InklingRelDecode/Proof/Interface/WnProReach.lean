-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.WnProRank
public import Kernels.InklingRelDecode.Proof.Thread.LpPreSites
public import Kernels.InklingRelDecode.Proof.Interface.LpProReach
public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg

@[expose] public section

/-!
# The prologue's arrival and copies of a preloaded block, backward from `bar18`

For the blocks `j < num_pre` the producers of `kv_ready j` are the prologue's thread 0 (the
arrival) and the threads of warps 0 and 1 that lead their elections (the copies). A thread at or
past the prologue's last state `bar18` has made them:

* `pro_gate`: the gate values of block `j` at every prologue state after the setup of a
  default-partition thread (from `pro_reaches_ptc`);
* `pro_reach_rankq`: backward from a prologue state of `prq` rank at least `R`, a prologue state
  of rank exactly `R`, for every thread (`ProA.rankq_step`; no premise on its elections);
* `arr_of_bar18`: thread 0 of a CTA with a state at `bar18` made the arrival of each block
  `j < num_pre` before it (through `lbA_j`, `ProA.next_into_lbA`, and `v_p177` for thread 0);
* `ptc_of_bar18`: a thread of warp 0 or 1 that leads its elections, with a state at `bar18`, has a
  state at each copy site of each block `j < num_pre` before it (`pro_reach_rank`);
* `ptc_issue`: the event of a prologue state at a copy site `jj` is a tensor copy completing on
  `kv_ready (jj / 4)` of the thread's CTA;
* `back_bar18`: a softmax or epilogue state of a thread follows a state at `bar18`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The gate values of a preloaded block** at every prologue state after the setup. -/
theorem pro_gate (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (hdef : g % L.block < 128) {j : Nat}
    (hb : j < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∀ k (d : ProA.D), St Q L X g k = some (some (.d (.pro d))) →
      d.site.afterSk = true → ProA.v_p53 L g d.dt = true ∧
        (ProA.v_p63 L g d.dt = true → j = 0) ∧ (ProA.v_p72 L g d.dt = true → j ≤ 1) := by
  intro k d hσ hsk
  obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ
  have ha : ProA.ArgsOk L g d.dt.pro := by
    rw [hpro]
    exact DStart.argsOk_inh hpre hg hdef tm
  have hs : d.dt.pro.w71 = Q.splits := by
    have := hpre.splitsRange
    rw [hpro]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨h0, h1, h2⟩ := Mbar.wordsSo_all hpre hX hf k _ hσ
  have hne : d.site ≠ .sMax ∧ d.site ≠ .ldCu0 := by
    constructor <;> (rintro h; rw [h] at hsk; simp [ProA.Site.afterSk] at hsk)
  have hm : ProA.WordsMatch Q (ProA.cta L g .z) d.dt :=
    ⟨h0 hne.1 hne.2, h1 (Or.inl hsk), h2 hsk⟩
  obtain ⟨g53, g63, g72⟩ := ProA.gate_of_numPre hpre hg ha hs hm hb
  refine ⟨g53, fun h => ?_, fun h => ?_⟩
  · by_contra hc
    rw [g63 (by omega)] at h
    cases h
  · by_contra hc
    rw [g72 (by omega)] at h
    cases h

/-- **Backward to a prologue state of a given `prq` rank**, for every thread. -/
theorem pro_reach_rankq {b R : Nat} (hRb : R ≤ 29 + 12 * b)
    (hG : ∀ k (d : ProA.D), St Q L X g k = some (some (.d (.pro d))) →
      d.site.afterSk = true → ProA.v_p53 L g d.dt = true ∧
        (ProA.v_p63 L g d.dt = true → b = 0) ∧ (ProA.v_p72 L g d.dt = true → b ≤ 1)) :
    ∀ k {d : ProA.D}, k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.pro d))) →
      R ≤ ProA.prq d.site →
      ∃ k' d', k' ≤ k ∧ St Q L X g k' = some (some (.d (.pro d'))) ∧
        ProA.prq d'.site = R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hk hσ hr
    by_cases heq : ProA.prq d.site = R
    · exact ⟨k, d, le_refl _, hσ, heq⟩
    have hs : d.site ≠ .sMax := by
      intro h
      rw [h] at hr heq
      simp [ProA.prq] at hr heq
      omega
    obtain ⟨k0, e, d0, rfl, he, hσ0, hn⟩ := pro_pred hk hσ hs
    have hG0 := hG k0 d0 hσ0
    have hst := ProA.rankq_step (b := b) hn (fun h => (hG0 h).1) (fun h => (hG0 h).2.1)
      (fun h => (hG0 h).2.2)
    obtain ⟨k', d', hk', hσ', h'⟩ := ih k0 (by omega) (by omega) hσ0 (by omega)
    exact ⟨k', d', by omega, hσ', h'⟩

theorem kvReadyOf_loc {j : Nat} (hj : j < 3) (c : Nat) :
    (EvD.kvReadyOf j).loc L c = kvReady L c j := by
  interval_cases j <;> rfl

/-- `v_p177` holds for thread 0 of a CTA. -/
theorem p177_zero (hz : g % L.block = 0) (dt : ProA.Dat) : ProA.v_p177 L g dt = true := by
  have ht : ProA.tidOf L g = 0 := hz
  have := ProA.p177_tab (ProA.tidOf L g) (by omega)
  simp only [ProA.v_p177, ProA.v_r27, ProA.v_r1]
  rw [this, ht]
  rfl

/-- **Thread 0 at `bar18` made the arrival of each preloaded block before.** -/
theorem arr_of_bar18 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (hz : g % L.block = 0) {j : Nat}
    (hb : j < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)) {k : Nat} {d : ProA.D}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hs : d.site = .bar18) :
    ∃ k0 pc, k0 < k ∧
      X.get (g, k0) = some ⟨pc, .arrive (kvReady L (g / L.block) j) 65536 1 true .cta⟩ := by
  have hb256 : L.block = 256 := hpre.block
  have hdef : g % L.block < 128 := by omega
  have hj3 : j < 3 := by
    have : ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x) ≤ 3 := by
      unfold ProA.numPre; exact Nat.min_le_right _ _
    omega
  have hr : 19 + 12 * j ≤ ProA.prq d.site := by rw [hs]; simp [ProA.prq]; omega
  obtain ⟨k', d', hk', hσ', hr'⟩ := pro_reach_rankq (b := j) (by omega)
    (pro_gate hpre hX hf hg hdef hb) k hk hσ hr
  have hs' := ProA.prq_lb_inj hj3 hr'
  have hne : d'.site ≠ .sMax := by rw [hs']; interval_cases j <;> decide
  obtain ⟨k0, e, d0, rfl, he, hσ0, hn⟩ := pro_pred (by omega) hσ' hne
  have hs0 : d0.site = ProA.arrSite j := by
    rcases ProA.next_into_lbA hj3 hn hs' with h | h
    · exact h
    · rw [p177_zero hz] at h
      cases h
  have he' : X.get (g, k0) = some e := he
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he' hσ0 (by simp [ExitState])
  have hev := ProA.shape_arr (ProA.sharedOk_of_pre hpre) hj3 (fired_pro hF) hs0
  refine ⟨k0, ProA.evPc d0.site, by omega, ?_⟩
  rw [he', hev, kvReadyOf_loc hj3]

/-- **A leading thread of warps 0 and 1 at `bar18` was at each copy site of each preloaded
block before.** -/
theorem ptc_of_bar18 (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (ht : ProA.tidOf L g < 64)
    (hlead : ElectLead L g (X.tr g)) {jj : Nat} (hj : jj < 12)
    (hb : jj / 4 < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)) {k : Nat} {d : ProA.D}
    (hk : k ≤ (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.pro d))))
    (hs : d.site = .bar18) :
    ∃ k' d', k' < k ∧ St Q L X g k' = some (some (.d (.pro d'))) ∧
      d'.site = ProA.ptcSite jj := by
  have hdef : g % L.block < 128 := by unfold ProA.tidOf at ht; omega
  obtain ⟨hlo, hhi⟩ := ProA.prk_ptc hj
  have hr : ProA.prk (ProA.ptcSite jj) ≤ ProA.prk d.site := by
    rw [hs]
    have := ProA.prk_le (ProA.ptcSite jj)
    show _ ≤ 66
    omega
  obtain ⟨k', d', hk', hσ', hr'⟩ := pro_reach_rank hlead (fun dt => ProA.p59_of_tid dt ht)
    (b := jj / 4) (by omega) hhi (pro_gate hpre hX hf hg hdef hb) k hk hσ hr
  have hs' := ProA.prk_ptc_inj hj hr'
  refine ⟨k', d', ?_, hσ', hs'⟩
  rcases Nat.lt_or_eq_of_le hk' with h | h
  · exact h
  · subst h
    rw [hσ] at hσ'
    simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ'
    subst hσ'
    rw [hs] at hr'
    have h66 : ProA.prk ProA.Site.bar18 = 66 := rfl
    have : jj / 4 ≤ 2 := by omega
    omega

/-- **The event at a copy site** is a tensor copy completing on `kv_ready (jj / 4)`. -/
theorem ptc_issue (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {d : ProA.D}
    (hk : k < (X.tr g).length) (hσ : St Q L X g k = some (some (.d (.pro d)))) {jj : Nat}
    (hj : jj < 12) (hs : d.site = ProA.ptcSite jj) :
    ∃ pc a sp, X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩ ∧
      sp.mbar = kvReady L (g / L.block) (jj / 4) := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k) = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
  obtain ⟨-, tm, -, hpro⟩ := hf.reach hg hσ
  have hev := ProA.ptc_event hpre hj hpro (fired_pro hF) hs
  refine ⟨_, _, _, by rw [he, hev], ?_⟩
  simp only [EvW.kvCopySpec]
  exact kvReadyOf_loc (by omega) _

/-- **A softmax or epilogue state follows a state at `bar18`.** -/
theorem back_bar18 {k : Nat} (hk : k ≤ (X.tr g).length) {s : DComp.St}
    (hσ : St Q L X g k = some (some (.d s)))
    (hs : (∃ d, s = .sm d) ∨ (∃ d, s = .epi d)) :
    ∃ k0 d0, k0 < k ∧ St Q L X g k0 = some (some (.d (.pro d0))) ∧ d0.site = .bar18 := by
  rcases hs with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · obtain ⟨k0, d0, h1, h2, h3⟩ := sm_back_bar18 k hk hσ
    exact ⟨k0, d0, h1, h2, h3⟩
  · obtain ⟨k1, -, d1, hk1, -, hσ1, -⟩ := epi_back k hk hσ
    obtain ⟨k0, d0, h1, h2, h3⟩ := sm_back_bar18 k1 (by omega) hσ1
    exact ⟨k0, d0, by omega, h2, h3⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
