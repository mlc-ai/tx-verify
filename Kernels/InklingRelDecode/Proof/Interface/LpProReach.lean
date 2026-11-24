-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.LpProRank
public import Kernels.InklingRelDecode.Proof.Interface.ClassCopyPage
public import Kernels.InklingRelDecode.Proof.Interface.CopyFacts
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Safety.Tensor
public import Kernels.InklingRelDecode.Proof.Thread.ShapeCopyEvent
public import Kernels.InklingRelDecode.Proof.Result.MmaPremises
public import Kernels.InklingRelDecode.Proof2.Lib.KvBox
public import Kernels.InklingRelDecode.Proof.Interface.RrArrive

@[expose] public section

/-!
# A thread of warps 0 and 1 that led its elections reaches the prologue's copies

Progress backward from the exit for the prologue's K/V copies (row Kk2):

* `pro_pred`: the state before a prologue state other than its first is a prologue state, and the
  step is the prologue machine's;
* `sm_back_bar18`: a softmax state is preceded by the prologue's last state (`bar18`);
* `pro_reach_rank`: backward from a prologue state of rank at least `R`, a prologue state of rank
  exactly `R`, for a thread that led its elections, is of warp 0 or 1 and whose gate values are
  those of block `b` (`ProA.rank_step`);
* `pro_reaches_ptc`: such a thread of a CTA, which exited, has a state at the copy site `j` of every
  block `j / 4 < num_pre`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The state before a prologue state** other than its first. -/
theorem pro_pred {k : Nat} {d : ProA.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hs : d.site ≠ .sMax) :
    ∃ (k0 : Nat) (e : Event) (d0 : ProA.D), k = k0 + 1 ∧ (X.tr g)[k0]? = some e ∧
      St Q L X g k0 = some (some (.d (.pro d0))) ∧ ProA.next L g d0 e = some (some d) := by
  rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
  · cases h0
  · refine ⟨k0, e, ?_⟩
    cases s0 with
    | dstart dd =>
      exfalso
      change DComp.dstartNext L g Q dd e = _ at hn
      unfold DComp.dstartNext at hn
      obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
      split at ha
      · simp only [DComp.St.pro.injEq] at ha
        subst ha
        exact hs rfl
      · cases ha
    | pro dp =>
      change DComp.proNext L g Q dp e = _ at hn
      unfold DComp.proNext at hn
      split at hn
      · split at hn <;> cases hn
      · obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        simp only [DComp.St.pro.injEq] at h
        subst h
        exact ⟨dp, rfl, he, hσ0, ha⟩
    | sm d0 =>
      exfalso
      exact dnext_pre hn trivial
    | epi d0 =>
      exfalso
      exact dnext_pre hn trivial

/-- **A softmax state is preceded by the prologue's last state.** -/
theorem sm_back_bar18 : ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {d : Sm.D},
    St Q L X g k = some (some (.d (.sm d))) →
    ∃ (k0 : Nat) (d0 : ProA.D), k0 < k ∧ St Q L X g k0 = some (some (.d (.pro d0))) ∧
      d0.site = .bar18 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk d hσ
    rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, he, hσ0, hn⟩
    · cases h0
    · cases s0 with
      | pro dp =>
        change DComp.proNext L g Q dp e = _ at hn
        unfold DComp.proNext at hn
        split at hn
        · rename_i hb
          exact ⟨k0, dp, by omega, hσ0, hb⟩
        · obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
          cases h
      | sm d0 =>
        obtain ⟨k1, d1, hk1, hσ1, hs1⟩ := ih k0 (by omega) (by omega) hσ0
        exact ⟨k1, d1, by omega, hσ1, hs1⟩
      | dstart dd =>
        exfalso
        change DComp.dstartNext L g Q dd e = _ at hn
        unfold DComp.dstartNext at hn
        obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
        split at ha <;> cases ha
      | epi de =>
        exfalso
        change (Epi.next de e).map (Option.map DComp.St.epi) = _ at hn
        obtain ⟨a, -, ha⟩ := map_map_eq_some_some hn
        cases ha

/-- **Backward to a prologue state of a given rank.** -/
theorem pro_reach_rank (hlead : ElectLead L g (X.tr g)) (h59 : ∀ dt, ProA.v_p59 L g dt = true)
    {b R : Nat} (hR1 : 1 ≤ R) (hRb : R ≤ 23 + 16 * b + 10)
    (hG : ∀ k (d : ProA.D), St Q L X g k = some (some (.d (.pro d))) →
      d.site.afterSk = true → ProA.v_p53 L g d.dt = true ∧
        (ProA.v_p63 L g d.dt = true → b = 0) ∧ (ProA.v_p72 L g d.dt = true → b ≤ 1)) :
    ∀ k {d : ProA.D}, k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.pro d))) →
      R ≤ ProA.prk d.site →
      ∃ k' d', k' ≤ k ∧ St Q L X g k' = some (some (.d (.pro d'))) ∧
        ProA.prk d'.site = R := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hk hσ hr
    by_cases heq : ProA.prk d.site = R
    · exact ⟨k, d, le_refl _, hσ, heq⟩
    have hs : d.site ≠ .sMax := by
      intro h
      rw [h] at hr
      simp [ProA.prk] at hr
      omega
    obtain ⟨k0, e, d0, rfl, he, hσ0, hn⟩ := pro_pred hk hσ hs
    have hmem : e ∈ X.tr g := List.mem_of_getElem? he
    have hl : ∀ mask inst ld, e.kind = .elect mask inst ld → ld = laneOf L g :=
      fun mask inst ld h => hlead e hmem mask inst ld h
    have hG0 := hG k0 d0 hσ0
    have hst := ProA.rank_step (b := b) hn hl h59 (fun h => (hG0 h).1) (fun h => (hG0 h).2.1)
      (fun h => (hG0 h).2.2)
    obtain ⟨k', d', hk', hσ', h'⟩ := ih k0 (by omega) (by omega) hσ0 (by omega)
    exact ⟨k', d', by omega, hσ', h'⟩

/-- **The prologue's copy sites are reached.** A launched default-partition thread of warp 0 or
1 that led its elections and exited has, for each copy `j < 12` of a block `j / 4 < num_pre`, a
prologue state at the copy site `j` with an event. -/
theorem pro_reaches_ptc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) (ht : ProA.tidOf L g < 64)
    (hex : ∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) (hlead : ElectLead L g (X.tr g))
    {j : Nat} (hj : j < 12)
    (hb : j / 4 < ProA.numPre Q (ProA.cta L g .z) (ProA.cta L g .x)) :
    ∃ k d, k < (X.tr g).length ∧ St Q L X g k = some (some (.d (.pro d))) ∧
      d.site = ProA.ptcSite j := by
  have hdef : g % L.block < 128 := by unfold ProA.tidOf at ht; omega
  have hiters : 0 < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) := by
    unfold ProA.numPre at hb
    omega
  obtain ⟨k1, ds, hσs, -, -, hk1⟩ := Rr.sm_reaches_bar21 hpre hX hf hg hex hdef hiters
  obtain ⟨k2, d2, hk2, hσ2, hs2⟩ := sm_back_bar18 k1 hk1.le hσs
  have hG : ∀ k (d : ProA.D), St Q L X g k = some (some (.d (.pro d))) →
      d.site.afterSk = true → ProA.v_p53 L g d.dt = true ∧
        (ProA.v_p63 L g d.dt = true → j / 4 = 0) ∧
        (ProA.v_p72 L g d.dt = true → j / 4 ≤ 1) := by
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
  obtain ⟨hlo, hhi⟩ := ProA.prk_ptc hj
  have hr : ProA.prk (ProA.ptcSite j) ≤ ProA.prk d2.site := by
    rw [hs2]
    have := ProA.prk_le (ProA.ptcSite j)
    show _ ≤ 66
    omega
  obtain ⟨k', d', hk', hσ', hr'⟩ := pro_reach_rank hlead (fun dt => ProA.p59_of_tid dt ht)
    (b := j / 4) (by omega) hhi hG k2 (by omega) hσ2 hr
  exact ⟨k', d', by omega, hσ', ProA.prk_ptc_inj hj hr'⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
