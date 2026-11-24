-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.LpPre
public import Kernels.InklingRelDecode.Proof.Interface.LpProReach
public import Kernels.InklingRelDecode.Proof.Interface.RsElect
public import Kernels.InklingRelDecode.Proof.Thread.LpPreSites
public import Kernels.InklingRelDecode.Proof.Thread.IpInitStage

@[expose] public section

/-!
# The prologue's events on the KV ring (`Lp.PreRing`)

* `pro_ctor_lt`, `pro_site_unique`: a thread's prologue states are at sites strictly increasing in
  program order (`IpInit.pro_next_lt`), so a thread is at a prologue site at most once;
* `numPre_of_site`: a prologue state at a site of block `b` is of a block below `num_pre` (the gate
  `ProA.Gate`, `ProA.numPre_of_gate`);
* the arrival on `kv_ready s` at a prologue state is at `arr s`, by thread 0 of the CTA (the guard
  `v_p177`); a copy on `kv_ready s` at a prologue state is at `ptc (4 s + m)`, by the lane of
  warp 0 or 1 that its election before the copy returned (`ProA.next_into_ptc`), which led every
  election (`electLead_of_elected`) and is the one such lane of its warp (`electLead_unique`);
* `preRing_of`: the events `pArr`, `pCp` chosen from those states (or dummy indices past the
  thread's trace when they do not exist) are `Lp.PreSlot`s; no completeness is assumed.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Lp
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvReady)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### A thread is at a prologue site at most once -/

theorem not_dstart_of_pro {s0 : DComp.St} {dd : DStart.D} {e : Event}
    (hn : DComp.next L g Q s0 e = some (some (.dstart dd))) : ∃ d0, s0 = .dstart d0 := by
  cases s0 with
  | dstart d0 => exact ⟨d0, rfl⟩
  | pro dp =>
    exfalso
    change DComp.proNext L g Q dp e = _ at hn
    unfold DComp.proNext at hn
    split at hn
    · split at hn <;> cases hn
    · obtain ⟨a, -, h⟩ := map_map_eq_some_some hn
      cases h
  | sm d0 => exact absurd (dnext_pre hn trivial) id
  | epi d0 => exact absurd (dnext_pre hn trivial) id

/-- The states before a common-start state are common-start states. -/
theorem dstart_before : ∀ (k : Nat), k ≤ (X.tr g).length → ∀ {dd : DStart.D},
    St Q L X g k = some (some (.d (.dstart dd))) →
    ∀ k1 ≤ k, ∃ dd1, St Q L X g k1 = some (some (.d (.dstart dd1))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk dd hσ k1 hk1
    by_cases he : k1 = k
    · exact ⟨dd, he ▸ hσ⟩
    rcases pred_d hk hσ with ⟨rfl, -⟩ | ⟨k0, e, s0, rfl, -, hσ0, hn⟩
    · omega
    · obtain ⟨d0, rfl⟩ := not_dstart_of_pro hn
      exact ih k0 (by omega) (by omega) hσ0 k1 (by omega)

/-- No prologue state precedes the prologue's first state. -/
theorem sMax_first {k : Nat} {d : ProA.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) (hs : d.site = .sMax) :
    ∀ k1 < k, ∀ d1 : ProA.D, St Q L X g k1 ≠ some (some (.d (.pro d1))) := by
  intro k1 hk1 d1 h1
  rcases pred_d hk hσ with ⟨rfl, h0⟩ | ⟨k0, e, s0, rfl, -, hσ0, hn⟩
  · omega
  · cases s0 with
    | dstart d0 =>
      obtain ⟨dd1, h⟩ := dstart_before k0 (by omega) hσ0 k1 (by omega)
      rw [h] at h1
      cases h1
    | pro dp =>
      change DComp.proNext L g Q dp e = _ at hn
      unfold DComp.proNext at hn
      split at hn
      · split at hn <;> cases hn
      · obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
        simp only [DComp.St.pro.injEq] at h
        subst h
        have := IpInit.pro_next_lt ha
        rw [hs] at this
        exact Nat.not_lt_zero _ this
    | sm d0 => exact absurd (dnext_pre hn trivial) id
    | epi d0 => exact absurd (dnext_pre hn trivial) id

/-- **A thread's prologue states are at strictly later sites.** -/
theorem pro_ctor_lt : ∀ (k2 : Nat), k2 ≤ (X.tr g).length → ∀ {d2 : ProA.D},
    St Q L X g k2 = some (some (.d (.pro d2))) → d2.site ≠ .sMax →
    ∀ k1 < k2, ∀ {d1 : ProA.D}, St Q L X g k1 = some (some (.d (.pro d1))) →
      d1.site.ctorIdx < d2.site.ctorIdx := by
  intro k2
  induction k2 using Nat.strong_induction_on with
  | _ k2 ih =>
    intro hk d2 hσ hs k1 hk1 d1 h1
    obtain ⟨k0, e, d0, rfl, -, hσ0, hn⟩ := pro_pred hk hσ hs
    have hlt := IpInit.pro_next_lt hn
    by_cases h10 : k1 = k0
    · subst h10
      rw [hσ0] at h1
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at h1
      subst h1
      exact hlt
    · by_cases hs0 : d0.site = .sMax
      · exact absurd h1 (sMax_first (by omega) hσ0 hs0 k1 (by omega) d1)
      · have := ih k0 (by omega) (by omega) hσ0 hs0 k1 (by omega) h1
        omega

/-- **A thread is at a prologue site other than the first at most once.** -/
theorem pro_site_unique {k1 k2 : Nat} {d1 d2 : ProA.D} (hk1 : k1 ≤ (X.tr g).length)
    (hk2 : k2 ≤ (X.tr g).length) (h1 : St Q L X g k1 = some (some (.d (.pro d1))))
    (h2 : St Q L X g k2 = some (some (.d (.pro d2)))) (hs : d1.site = d2.site)
    (hne : d2.site ≠ .sMax) : k1 = k2 := by
  rcases lt_trichotomy k1 k2 with h | h | h
  · have := pro_ctor_lt k2 hk2 h2 hne k1 h h1
    rw [hs] at this
    omega
  · exact h
  · have := pro_ctor_lt k1 hk1 h1 (hs ▸ hne) k2 h h2
    rw [hs] at this
    omega

/-! ### The facts at a prologue state with an event -/

/-- The invariant of a prologue state with an event, and the thread is of the default partition. -/
theorem pro_inv_at (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {e : Event} {d : ProA.D} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.pro d)))) :
    ProA.Inv L g d ∧ g % L.block < 128 := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  exact ⟨hinv.2.1, hinv.1⟩

/-- **A prologue state at a site of block `b` is of a block below `num_pre`.** -/
theorem numPre_of_site (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {d : ProA.D}
    (hσ : St Q L X g k = some (some (.d (.pro d)))) {b : Nat} (hb : d.site ∈ ProA.blkSites b)
    (hsk : d.site.afterSk = true) : b < npOf Q L (g / L.block) := by
  obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ
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
  obtain ⟨hG, -⟩ := pgSo_all hpre hX hf k _ hσ
  rw [npOf_eq]
  exact ProA.numPre_of_gate hpre hg ha hs hm hG hb

theorem kvReady_loc_eq {c c' j s : Nat}
    (h : (EvD.kvReadyOf j).loc L c' = kvReady L c s) : c' = c ∧ j % 3 = s := by
  simp only [EvD.kvReadyOf, EvD.Bar.loc, EvD.Bar.off, kvReady, EvW.barLoc, EvW.kvReadyOff,
    Loc.mk.injEq] at h
  omega

theorem arr_props : ∀ j < 3, ProA.arrSite j ≠ .sMax ∧ (ProA.arrSite j).afterSk = true := by
  decide

theorem arr_guard {j : Nat} (hj : j < 3) (dt : ProA.Dat) :
    ProA.guardVal L g dt (ProA.arrSite j) = ProA.v_p177 L g dt := by
  interval_cases j <;> rfl

theorem ptc_props : ∀ j < 12, ProA.ptcSite j ≠ .sMax ∧ (ProA.ptcSite j).afterSk = true ∧
    ProA.ptcSite j ∈ ProA.ptcSites := by
  decide

theorem ptcSite_inj : ∀ j < 12, ∀ j' < 12, ProA.ptcSite j = ProA.ptcSite j' → j = j' := by
  decide

/-! ### The chosen events -/

open Classical in
/-- The index of thread `t`'s prologue state at site `s` with an event, or `dflt` if it has none. -/
def siteIdx (Q : Params) (L : Launch) (X : Execution) (t : Nat) (s : ProA.Site) (dflt : Nat) :
    Nat :=
  if h : ∃ k d, k < (X.tr t).length ∧ St Q L X t k = some (some (.d (.pro d))) ∧ d.site = s
  then Classical.choose h else dflt

theorem siteIdx_cases (Q : Params) (L : Launch) (X : Execution) (t : Nat) (s : ProA.Site)
    (dflt : Nat) :
    (siteIdx Q L X t s dflt < (X.tr t).length ∧ ∃ d, St Q L X t (siteIdx Q L X t s dflt) =
      some (some (.d (.pro d))) ∧ d.site = s) ∨ siteIdx Q L X t s dflt = dflt := by
  unfold siteIdx
  split
  · rename_i h
    obtain ⟨d, h1, h2, h3⟩ := Classical.choose_spec h
    exact .inl ⟨h1, d, h2, h3⟩
  · exact .inr rfl

theorem siteIdx_eq {t k : Nat} {s : ProA.Site} {dflt : Nat} {d : ProA.D}
    (hk : k < (X.tr t).length) (hσ : St Q L X t k = some (some (.d (.pro d))))
    (hs : d.site = s) (hne : s ≠ .sMax) : siteIdx Q L X t s dflt = k := by
  have hex : ∃ k d, k < (X.tr t).length ∧ St Q L X t k = some (some (.d (.pro d))) ∧
      d.site = s := ⟨k, d, hk, hσ, hs⟩
  unfold siteIdx
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨d', h1, h2, h3⟩ := Classical.choose_spec hex
  exact pro_site_unique h1.le hk.le h2 hσ (h3.trans hs.symm) (hs ▸ hne)

open Classical in
/-- The copying thread of warp `w` of CTA `c`: a thread of the warp that led its elections and
elected, if there is one, else the warp's lane 0. -/
def cpThr (L : Launch) (X : Execution) (c w : Nat) : Nat :=
  if h : ∃ t, SameWarp L (c * L.block + 32 * w) t ∧ ElectLead L t (X.tr t) ∧
      ∃ ld, Elected (X.tr t) ld then Classical.choose h else c * L.block + 32 * w

theorem cpThr_props (hb : L.block = 256) {c w : Nat} (hw : w < 8) :
    cpThr L X c w / L.block = c ∧ cpThr L X c w % L.block / 32 = w := by
  have hth : L.threads = L.grid * L.block := rfl
  unfold cpThr
  split
  · rename_i h
    obtain ⟨⟨⟨-, -, h1⟩, h2⟩, -⟩ := Classical.choose_spec h
    have e1 : (c * L.block + 32 * w) / L.block = c := by rw [hb]; omega
    have e2 : (c * L.block + 32 * w) % L.block / 32 = w := by rw [hb]; omega
    exact ⟨h1.symm.trans e1, h2.symm.trans e2⟩
  · rw [hb]; omega

/-- **The copying thread is the one that elected.** -/
theorem cpThr_eq (hX : Consistent L kernel asms mem0 X) {c t ld : Nat}
    (hw : SameWarp L (c * L.block + 32 * (t % L.block / 32)) t)
    (hl : ElectLead L t (X.tr t)) (he : Elected (X.tr t) ld) :
    cpThr L X c (t % L.block / 32) = t := by
  have hex : ∃ t', SameWarp L (c * L.block + 32 * (t % L.block / 32)) t' ∧
      ElectLead L t' (X.tr t') ∧ ∃ ld, Elected (X.tr t') ld := ⟨t, hw, hl, ld, he⟩
  unfold cpThr
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨hw', hl', ld', he'⟩ := Classical.choose_spec hex
  have hw2 : SameWarp L (Classical.choose hex) t := by
    obtain ⟨⟨a1, a2, a3⟩, a4⟩ := hw'
    obtain ⟨⟨b1, b2, b3⟩, b4⟩ := hw
    exact ⟨⟨a2, b2, by omega⟩, by omega⟩
  exact electLead_unique hX.elect hw2 (electMask_full hX _) (electMask_full hX t) he' he hl' hl

/-- The prologue's arrival on slot `s` of CTA `c`. -/
def pArrOf (Q : Params) (L : Launch) (X : Execution) (c s : Nat) : EvId :=
  (c * L.block, siteIdx Q L X (c * L.block) (ProA.arrSite s) 0)

/-- The prologue's copy `i` on slot `s` of CTA `c`: the copy `4 s + i / 2` of warp `i % 2`. -/
def pCpOf (Q : Params) (L : Launch) (X : Execution) (c s : Nat) (i : Fin 8) : EvId :=
  (cpThr L X c (i.val % 2), siteIdx Q L X (cpThr L X c (i.val % 2))
    (ProA.ptcSite (4 * s + i.val / 2)) ((X.tr (cpThr L X c (i.val % 2))).length + i.val))

theorem tid_eq (L : Launch) (g : Nat) : ProA.tidOf L g = g % L.block := rfl

/-- **`Lp.PreRing`**: the prologue's events on every slot of every CTA. -/
theorem preRing_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) : PreRing Q L X := by
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  intro c hc s hs
  refine ⟨pArrOf Q L X c s, pCpOf Q L X c s, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · -- the arrival
    intro g k pc tx cnt rel sc d he hσ
    have hg : g < L.threads := Frame.lt_of_get hX he
    have hk : k < (X.tr g).length := len_of_get he
    rcases arrive_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, _, _, _, rfl⟩ with
      ⟨d', hσ', j, hj, hsj, hev⟩ | ⟨d', hσ', -⟩ | ⟨d', P, hσ', -⟩
    · rw [hσ] at hσ'
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ'
      subst hσ'
      simp only [Event.mk.injEq, Kind.arrive.injEq] at hev
      obtain ⟨hcg, hjs⟩ := kvReady_loc_eq hev.2.1.symm
      have hjs' : j = s := by omega
      subst hjs'
      obtain ⟨hI, hdef⟩ := pro_inv_at hX hf he hσ
      have hgd := hI.guard
      rw [hsj, arr_guard hj] at hgd
      have ht0 := ProA.tid_of_p177 (by rw [tid_eq]; omega) hgd
      rw [tid_eq] at ht0
      have hgc : g = c * L.block := by
        rw [← hcg]
        have := Nat.div_add_mod g L.block
        rw [ht0] at this
        rw [Nat.mul_comm]
        omega
      subst hgc
      obtain ⟨hne, hsk⟩ := arr_props j hj
      refine ⟨?_, ?_⟩
      · show (c * L.block, k) = (c * L.block, siteIdx Q L X (c * L.block) (ProA.arrSite j) 0)
        rw [siteIdx_eq hk hσ hsj hne]
      · have := numPre_of_site hpre hX hf hg hσ (b := j) (by rw [hsj]; exact ProA.arr_blk j hj)
          (by rw [hsj]; exact hsk)
        rw [hcg] at this
        exact this
    · rw [hσ] at hσ'; cases hσ'
    · rw [hσ] at hσ'; cases hσ'
  · -- the copies
    intro g k pc a sp d he hsp hσ
    have hg : g < L.threads := Frame.lt_of_get hX he
    have hk : k < (X.tr g).length := len_of_get he
    rcases copy_event_state hpre hX hf.sound hf.tracked hf.ldRng hg he ⟨_, _, rfl⟩ with
      ⟨d', hσ', j, hj, hsj, a', s', hev, -, -, hmb, -⟩ | ⟨d', P, hσ', -⟩
    · rw [hσ] at hσ'
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at hσ'
      subst hσ'
      simp only [Event.mk.injEq, Kind.tensorIssue.injEq] at hev
      obtain ⟨-, -, rfl⟩ := hev
      rw [hsp] at hmb
      obtain ⟨hcg, hjs⟩ := kvReady_loc_eq hmb.symm
      have hjs' : j / 4 = s := by omega
      obtain ⟨hI, hdef⟩ := pro_inv_at hX hf he hσ
      obtain ⟨hne, hsk, hmem⟩ := ptc_props j hj
      obtain ⟨k0, e0, d0, hk0, he0, hσ0, hn0⟩ := pro_pred hk.le hσ (by rw [hsj]; exact hne)
      obtain ⟨⟨mask, inst, hel⟩, h59⟩ := ProA.next_into_ptc hn0 (by rw [hsj]; exact hmem)
      have ht := ProA.tid_of_p59 (by rw [tid_eq]; omega) h59
      rw [tid_eq] at ht
      have hel' : Elected (X.tr g) (laneOf L g) :=
        ⟨e0, List.mem_of_getElem? he0, mask, inst, hel⟩
      have hlead := electLead_of_elected hX hel'
      have hwg : SameWarp L (c * L.block + 32 * (g % L.block / 32)) g := by
        refine ⟨⟨?_, hg, ?_⟩, ?_⟩
        · rw [hth, hb] at hg ⊢; rw [hb] at ht; omega
        · rw [hb] at hcg ht ⊢; omega
        · rw [hb] at hcg ht ⊢; omega
      have hthr := cpThr_eq hX hwg hlead hel'
      have hw2 : g % L.block / 32 < 2 := by omega
      refine ⟨⟨⟨2 * (j % 4) + g % L.block / 32, by omega⟩, ?_⟩, ?_⟩
      · have e1 : (2 * (j % 4) + g % L.block / 32) % 2 = g % L.block / 32 := by omega
        have e2 : 4 * s + (2 * (j % 4) + g % L.block / 32) / 2 = j := by omega
        unfold pCpOf
        simp only [e1, e2, hthr]
        rw [siteIdx_eq hk hσ hsj (hsj ▸ hne)]
      · have := numPre_of_site hpre hX hf hg hσ (b := j / 4)
          (by rw [hsj]; exact ProA.ptc_blk j hj) (by rw [hsj]; exact hsk)
        rw [hcg, hjs'] at this
        exact this
    · rw [hσ] at hσ'; cases hσ'
  · -- the arrival's thread
    refine ⟨?_, ?_⟩
    · show c * L.block / L.block = c
      rw [hb]; omega
    · show c * L.block % L.block < 128
      rw [hb]; omega
  · intro i
    obtain ⟨h1, h2⟩ := cpThr_props (X := X) hb (c := c) (w := i.val % 2) (by omega)
    refine ⟨h1, ?_⟩
    show cpThr L X c (i.val % 2) % L.block < 128
    have := Nat.mod_lt (cpThr L X c (i.val % 2)) (by rw [hb]; omega : 0 < L.block)
    have : i.val % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [hb] at h2 ⊢
    omega
  · -- the copies are distinct
    intro i i' h
    unfold pCpOf at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨ht, hk⟩ := h
    have hw := (cpThr_props (X := X) hb (c := c) (w := i.val % 2) (by omega)).2
    have hw' := (cpThr_props (X := X) hb (c := c) (w := i'.val % 2) (by omega)).2
    rw [ht] at hw
    have hm : i.val % 2 = i'.val % 2 := hw.symm.trans hw'
    rw [ht] at hk
    apply Fin.ext
    rcases siteIdx_cases Q L X (cpThr L X c (i'.val % 2)) (ProA.ptcSite (4 * s + i.val / 2))
        ((X.tr (cpThr L X c (i'.val % 2))).length + i.val) with ⟨a1, d1, a2, a3⟩ | a
    · rcases siteIdx_cases Q L X (cpThr L X c (i'.val % 2)) (ProA.ptcSite (4 * s + i'.val / 2))
          ((X.tr (cpThr L X c (i'.val % 2))).length + i'.val) with ⟨b1, d2, b2, b3⟩ | b
      · rw [hk] at a2
        rw [a2] at b2
        simp only [Option.some.injEq, TSt.d.injEq, DComp.St.pro.injEq] at b2
        subst b2
        have := ptcSite_inj _ (by omega) _ (by omega) (a3.symm.trans b3)
        omega
      · rw [hk, b] at a1
        omega
    · rcases siteIdx_cases Q L X (cpThr L X c (i'.val % 2)) (ProA.ptcSite (4 * s + i'.val / 2))
          ((X.tr (cpThr L X c (i'.val % 2))).length + i'.val) with ⟨b1, d2, b2, b3⟩ | b
      · rw [← hk, a] at b1
        omega
      · rw [hk, b] at a
        omega

end
end PTX.Kernels.InklingRelDecode.Proof.Lp
