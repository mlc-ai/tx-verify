-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.Lk5MBar
public import Kernels.InklingRelDecode.Proof.Protocol.BarLanePub

@[expose] public section

/-!
# The scratch words: the order of the stores and the loads

The three orders the reads-from argument of the scratch load needs, each through one generation
of named barrier 0 (`Bar.bar128Causal`) or barrier 1 (`Bar.pub_bar1`):

* `later_after`: the load of iteration `i` (after its `bar23`) is before every `store10` of a later
  iteration. The store's thread has made at least two barrier-0 events since its `bar23` of
  iteration `i` (that `bar23` and its `bar21`), so it passed its arrival of the reader's next count,
  which the reader makes after its load;
* `earlier_before`: a `store10` of iteration `j < i` is before every `store10` of iteration `i`:
  the storing thread's `bar23` of iteration `j` follows its store and is in the generation of the
  other thread's `bar23` of iteration `j`, which precedes its store of iteration `i`;
* `pro_before`: the prologue's stores of `(num_pre, num_iters)` are before every state of the
  softmax region (the prologue's last barrier-1 generation).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Sm PTX.Kernels.InklingRelDecode.Proof.Ledger

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem rank_store10 {d : Sm.D} (hs : d.site = .store10) : d.rank = 64 * d.i + 16 := by
  simp [D.rank, hs, Site.ord]

theorem rank_bar23 {d : Sm.D} (hs : d.site = .bar23) : d.rank = 64 * d.i + 17 := by
  simp [D.rank, hs, Site.ord]

theorem rank_bar21 {d : Sm.D} (hs : d.site = .bar21) : d.rank = 64 * d.i + 29 := by
  simp [D.rank, hs, Site.ord]

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The load after `bar23` of iteration `i` is before every `store10` of a later iteration.** -/
theorem later_after {c i : Nat} (hB : B0At Q L X c i) (hP : B0Pos Q L X c i) (hi1 : 1 ≤ i)
    {g k2 : Nat} {d2 : Sm.D} (hg : g < L.threads) (hgc : g / L.block = c)
    (hσ2 : St Q L X g k2 = some (some (.d (.sm d2)))) (hs2 : d2.site = .bar23) (hi2 : d2.i = i)
    (hpass : k2 + 1 < (X.tr g).length)
    (hrd : ∀ {pc cn m}, X.get (g, k2 + 1) ≠ some ⟨pc, .bar 0 cn m⟩)
    {μ kμ : Nat} {dμ : Sm.D} (hμ : μ < L.threads) (hμc : μ / L.block = c)
    (hσμ : St Q L X μ kμ = some (some (.d (.sm dμ)))) (hkμ : kμ < (X.tr μ).length)
    (hsμ : dμ.site = .store10) (hjμ : i < dμ.i) :
    baseCausality L X (g, k2 + 1) (μ, kμ) := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hgd := sm_default (by omega) hσ2
  have hμd := sm_default (by omega) hσμ
  have hrμ := rank_store10 hsμ
  obtain ⟨a', da', ha'lt, hσa', hsa', hia'⟩ := back23 hi1 kμ (by omega) hσμ (by omega)
  obtain ⟨k'', dk, hk''lt, hσk, hsk, hik⟩ := back21 (i0 := i) kμ (by omega) hσμ (by omega)
  have ha'k : a' < k'' := by
    by_contra hc
    have := rank_mono_m hpre hX hf.sound hσk a' (by omega) (by omega) hσa'
    rw [rank_bar21 hsk, rank_bar23 hsa'] at this
    omega
  have hca' : cnt0 X μ a' = cnt0 X g k2 := hB hμ hg hμc hgc hσa' hσ2 hsa' hs2 hia' hi2
  obtain ⟨ea, hea⟩ : ∃ e, (X.tr μ)[a']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ek, hek⟩ : ∃ e, (X.tr μ)[k'']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have h1 := bar_cnt hpre hX hf hμ hea hσa' (by rw [hsa']; trivial)
  have h2 := bar_cnt hpre hX hf hμ hek hσk (by rw [hsk]; trivial)
  have h3 := cnt_mono (Execution.isBarId 0) (X := X) μ (show a' + 1 ≤ k'' by omega)
  have h4 := cnt_mono (Execution.isBarId 0) (X := X) μ (show k'' + 1 ≤ kμ by omega)
  obtain ⟨y, pcy, cny, hy, hIy, hcy⟩ := nth_bar0 hX hb
    (show cnt0 X g k2 + 1 < cnt0 X μ kμ by simp only [cnt0] at *; omega)
  obtain ⟨-, hP2, hP3⟩ := hP hg hgc hσ2 hs2 hi2 hμ hμc hμd
  have hcny : cny = some 128 := hP2 hIy hcy
  subst hcny
  obtain ⟨-, hQ2, hQ3⟩ := hP hg hgc hσ2 hs2 hi2 hg hgc hgd
  obtain ⟨ag, pcg, cng, hbarg, hordg⟩ := member_of hpre hX hf hIy (by simp only; omega) hμd
    (t := g) (by rw [hgc, hμc]) hgd (fun hx => by have := hQ3 hx; simp only at this ⊢; omega)
  have hordg' : cnt0 X g ag = cnt0 X g k2 + 1 := hordg.trans hcy
  have hcng : cng = some 128 := hQ2 hbarg hordg'
  subst hcng
  obtain ⟨e2, he2⟩ : ∃ e, (X.tr g)[k2]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have h5 := bar_cnt hpre hX hf hg he2 hσ2 (by rw [hs2]; trivial)
  have hlt : k2 + 1 < ag := by
    rcases Nat.lt_or_ge (k2 + 1) ag with h | h
    · exact h
    · exfalso
      rcases Nat.lt_or_ge ag (k2 + 1) with h' | h'
      · have := cnt_mono (Execution.isBarId 0) (X := X) g (show ag ≤ k2 by omega)
        simp only [cnt0] at hordg'
        omega
      · have hag : ag = k2 + 1 := by omega
        subst hag
        exact hrd hbarg
  exact Bar.bar128Causal hpre hX hf.sound hf.tracked hg hμ (by rw [hgc, hμc]) hgd hμd hbarg hIy
    hordg hlt hy hkμ

/-- **A `store10` of iteration `j < i` is before every `store10` of iteration `i`.** -/
theorem earlier_before {c i j : Nat} (hP : B0Pos Q L X c j) {t a1 : Nat} {dt : Sm.D}
    (ht : t < L.threads) (htc : t / L.block = c)
    (hσt : St Q L X t a1 = some (some (.d (.sm dt)))) (ha1 : a1 < (X.tr t).length)
    (hst : dt.site = .store10) (hit : dt.i = i)
    {μ kμ : Nat} {dμ : Sm.D} (hμ : μ < L.threads) (hμc : μ / L.block = c)
    (hσμ : St Q L X μ kμ = some (some (.d (.sm dμ)))) (hkμ : kμ < (X.tr μ).length)
    (hsμ : dμ.site = .store10) (hj : dμ.i = j) (hji : j < i) :
    baseCausality L X (μ, kμ) (t, a1) := by
  have htd := sm_default (by omega) hσt
  have hμd := sm_default (by omega) hσμ
  have hj1 : 1 ≤ j := by
    have := midOk_state kμ (by omega) hσμ (by rw [hsμ]; trivial)
    omega
  have hrt := rank_store10 hst
  obtain ⟨b', db, hb'lt, hσb, hsb, hib⟩ := back23 hj1 a1 (by omega) hσt (by omega)
  obtain ⟨aμ, dm, hσa, hsa, hia, hcnt, hgeta⟩ := member23 hpre hX hf hP ht htc hσb hsb hib
    (by omega) hμ hμc hμd
  have hka : kμ < aμ := by
    by_contra hc
    rcases Nat.lt_or_ge aμ kμ with h | h
    · have := rank_mono_m hpre hX hf.sound hσa kμ (by omega) (by omega) hσμ
      rw [rank_bar23 hsa, rank_store10 hsμ] at this
      omega
    · have hak : aμ = kμ := by omega
      subst hak
      rw [hσa] at hσμ
      simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at hσμ
      subst hσμ
      rw [hsa] at hsμ
      cases hsμ
  obtain ⟨eb, heb⟩ : ∃ e, (X.tr t)[b']? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hevb := bar_event hpre hX hf ht heb hσb (by rw [hsb]; trivial)
  rw [hsb] at hevb
  have hgetb : X.get (t, b') = some ⟨Sm.Site.bar23.pc, .bar 0 (some 128) .sync⟩ := by
    rw [show X.get (t, b') = some eb from heb, hevb]
  exact Bar.bar128Causal hpre hX hf.sound hf.tracked hμ ht (by rw [hμc, htc]) hμd htd hgeta hgetb
    hcnt hka hb'lt ha1

/-- **The prologue's stores are before every state of the softmax region.** -/
theorem pro_before (hR : RoleReads L X) {u kt : Nat} {du : ProA.D} {pc : Nat} {a : Acc}
    {bs : List Byte} (hu : u < L.threads) (hσu : St Q L X u kt = some (some (.d (.pro du))))
    (hgu : X.get (u, kt) = some ⟨pc, .wr a bs⟩) {t a1 : Nat} {dt : Sm.D} (ht : t < L.threads)
    (hσt : St Q L X t a1 = some (some (.d (.sm dt)))) (ha1 : a1 < (X.tr t).length)
    (hc : u / L.block = t / L.block) : baseCausality L X (u, kt) (t, a1) := by
  have hkt : kt ≤ (X.tr u).length := event_le hgu
  have hud : u % L.block < 128 := (cls_inv kt _ hkt hσu).mp trivial
  have hb0 : b1N X u kt = 0 := by
    obtain ⟨d', hd', h⟩ := dphase_inv hpre hX hf.sound hud kt _ hkt hσu
    cases hd'
    rw [h]
    simp only [dPh]
    split <;> rfl
  exact Bar.pub_bar1 hpre hX hf.sound hf.tracked hR (e := (u, kt)) (u := (t, a1)) hgu rfl hb0
    (sm_b1N hpre hX hf.sound ha1.le hσt) ⟨hu, ht, hc⟩ ha1

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
