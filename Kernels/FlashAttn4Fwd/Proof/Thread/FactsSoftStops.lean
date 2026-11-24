-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSt
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAccept0
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAccept1
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAccept2
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftAccept3
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tc

@[expose] public section

/-! # The softmax part of `Cross.NextStopsAtExitOrBadRead`

The softmax machine rejects an event of its site only at its exit, at a load's wait whose run
does not accept the words (`WaitOk`), at a tile's named barrier whose exponentials do not accept
them (`ExpOk0`, `ExpOk1`), and at a statistics poll whose row sum does not accept its operands
(`StatsOk`). The words of the state are the values the current tile's loads returned, or their
selected halves (`Counts.words`); when no load before the event returned a value that is not a
single-precision number (no `BadRead`), the words are such numbers, so are the reference maximum
and the row sum (`Counts.refs`), and the runs accept them (`FactsSoftAccept*`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The softmax machine rejects its site's event only at its exit, a load's wait, the named
barriers `gen 0`, `gen 1` and a statistics poll. -/
theorem soft_next_some {g : Nat} {d : Softmax.D} {e : Event} (hev : Softmax.Ev L g d e)
    (h1 : d.site ≠ .exit) (h2 : ∀ lp c, d.site ≠ .ldW lp c) (h3 : d.site ≠ .gen 0)
    (h4 : d.site ≠ .gen 1) (h5 : ∀ w, d.site ≠ .statsW w) : Softmax.next L g d e ≠ none := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  rcases e with ⟨epc, ek⟩
  simp only at h1 h2 h3 h4 h5
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin3_cases j with rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin2_cases c with rfl | rfl)
  all_goals simp only [Softmax.Ev] at hev
  all_goals repeat' (first | (obtain rfl := hev) | (obtain ⟨_, hev⟩ := hev))
  all_goals simp_all [Softmax.next]
  all_goals split_ifs <;> simp

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **Without a bad read before it, a softmax state's words are single-precision numbers.** -/
theorem soft_words_f32 {g i : Nat} {d : Softmax.D} (hw : warpOf L g < 8)
    (hc : Softmax.Counts L g d ((X.tr g).take i)) (hbad : ∀ j < i, ¬ BadRead L X g j) :
    ∃ R : Nat → Value, (∀ k < 32 * Softmax.chunks d, RTy.Has .f32 (R k)) ∧
      ∀ k < 32 * Softmax.chunks d,
        d.w k = if d.site.halved then Softmax.half R k else R k := by
  obtain ⟨R, hR, hwr⟩ := hc.words
  refine ⟨R, fun k hk => ?_, hwr⟩
  obtain ⟨vals, ⟨kk, pc, hkk, -⟩, hr⟩ := hR (k / 32) (by omega) (k % 32) (Nat.mod_lt _ (by decide))
  have hlt : kk < i := by
    have := (List.getElem?_eq_some_iff.mp hkk).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, kk) =
      some ⟨pc, .tc (.ld (Softmax.tmem L g (32 * (k / 32))) vals .s32x32b)⟩ := by
    have h2 : ((X.tr g).take i)[kk]? = (X.tr g)[kk]? := List.getElem?_take_of_lt hlt
    rw [h2] at hkk
    exact hkk
  obtain ⟨-, -, -, -, -, -, -, -, hl⟩ := soft_tld hpre hX ht hw hget
  have hf : F32s vals := by
    by_contra hn
    exact hbad kk hlt (.inl ⟨pc, _, vals, hget, hn⟩)
  have hk : 32 * (k / 32) + k % 32 = k := Nat.div_add_mod k 32
  rw [hk] at hr
  rw [hr]
  exact hf _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _)

/-- **Without a bad read before it, every load of a softmax thread's trace prefix returned
32 single-precision numbers.** -/
theorem soft_loadsF32_noBad {g i : Nat} (hw : warpOf L g < 8)
    (hbad : ∀ j < i, ¬ BadRead L X g j) :
    Softmax.LoadsF32 ((X.tr g).take i) := by
  intro x hx pc a vals hxe
  subst hxe
  obtain ⟨j, hj, hget⟩ := get_of_mem_take hx
  have hl := (soft_tld hpre hX ht hw hget).choose_spec.choose_spec.choose_spec.2.2.2.2.2
  refine ⟨hl, fun v hv => ?_⟩
  by_contra hn
  exact hbad j hj (.inl ⟨pc, a, vals, hget, fun h => hn (h v hv)⟩)

/-- **The softmax part of `Cross.NextStopsAtExitOrBadRead`.** -/
theorem Cross.NextStops_soft {g i : Nat} {d : Softmax.D} {e : Event}
    (hσ : St L X g i = some (some (.inr (.softmax d)))) (he : X.get (g, i) = some e)
    (hn : (code L g).next (.inr (.softmax d)) e = none) :
    (∃ pc, e = ⟨pc, .exit⟩) ∨ ∃ j ≤ i, BadRead L X g j := by
  have hσ' : Frame.stateAt (code L) X g i = some (some (.inr (.softmax d))) := hσ
  obtain ⟨hev, hc, hi⟩ := soft_ev_at hpre hX ht hσ' he
  have hw := hi.warp
  have hn' : Softmax.next L g d e = none := by
    simp only [code] at hn
    cases h : Softmax.next L g d e with
    | none => rfl
    | some o => rw [h] at hn; cases hn
  by_cases hx : ∃ pc, e = ⟨pc, .exit⟩
  · exact .inl hx
  refine .inr ?_
  by_contra hb
  have hbad : ∀ j < i, ¬ BadRead L X g j := fun j hj h => hb ⟨j, by omega, h⟩
  obtain ⟨R, hR, hwr⟩ := soft_words_f32 hpre hX ht hw hc hbad
  have hsc : Softmax.ScaleOk L := Softmax.scale_ok hpre
  obtain ⟨hH, hRl⟩ := hc.refs (soft_loadsF32_noBad hpre hX ht hw hbad) hsc
  obtain ⟨site, ii, tt, ww, mm, ll⟩ := d
  simp only at hR hwr hev hn' hH hRl
  -- the words of the state, by site
  have hf : ∀ (n : Nat), n ≤ Softmax.chunks ⟨site, ii, tt, ww, mm, ll⟩ →
      site.halved = false → ∀ k < 32 * n, RTy.Has .f32 (ww k) := by
    intro n hnn hh k hk
    rw [hwr k (by omega), hh]
    exact hR k (by omega)
  have hW : Softmax.chunks ⟨site, ii, tt, ww, mm, ll⟩ = 4 → Softmax.WordsF32 ww := by
    intro h4 k hk
    have hR' : Softmax.WordsF32 R := fun k hk => hR k (by omega)
    rw [hwr k (by omega)]
    split
    · rw [Softmax.half_eq hR' hk]
      exact hR' k hk
    · exact hR' k hk
  by_cases hex : site = .exit
  · subst hex
    simp only [Softmax.Ev] at hev
    exact hx ⟨e.pc, by obtain ⟨epc, ek⟩ := e; simp only at hev; rw [hev]⟩
  by_cases hld : ∃ lp c, site = .ldW lp c
  · obtain ⟨lp, c, rfl⟩ := hld
    simp only [Softmax.next] at hn'
    split_ifs at hn' with hok
    apply hok
    have hf' := hf (c.val + 1) (by simp [Softmax.chunks]) rfl
    rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl
    · rw [Softmax.waitOk_lt (by decide)]
      cases lp
      · exact Softmax.packs_ok_F0 (fun k hk => hf' k (by simpa using hk))
      · exact Softmax.packs_ok_T0 (fun k hk => hf' k (by simpa using hk))
    · rw [Softmax.waitOk_lt (by decide)]
      cases lp
      · exact Softmax.packs_ok_F1 (fun k hk => hf' k (by simpa using hk))
      · exact Softmax.packs_ok_T1 (fun k hk => hf' k (by simpa using hk))
    · rw [Softmax.waitOk_lt (by decide)]
      cases lp
      · exact Softmax.packs_ok_F2 (fun k hk => hf' k (by simpa using hk))
      · exact Softmax.packs_ok_T2 (fun k hk => hf' k (by simpa using hk))
    · have h128 : ∀ k < 128, RTy.Has .f32 (ww k) := fun k hk => hf' k (by simpa using hk)
      have hW' := hW (by simp [Softmax.chunks])
      cases lp
      · rw [Softmax.waitOk_max0]
        exact ⟨Softmax.packs_ok_F3 h128, Softmax.accept_1341 h128, Softmax.accept_1455 h128,
          Softmax.accept_1569 h128, Softmax.accept_1683 h128, Softmax.max0T_ok hW'⟩
      · obtain ⟨hm, -⟩ := hRl (.inl rfl)
        rw [Softmax.waitOk_max1]
        exact ⟨Softmax.packs_ok_T3 h128, Softmax.accept_2796 h128 ⟨_, hm⟩,
          Softmax.max1T_ok hsc hm hW'⟩
  by_cases hst : ∃ w, site = .statsW w
  · obtain ⟨w, rfl⟩ := hst
    simp only [Softmax.next] at hn'
    split at hn'
    · split_ifs at hn' with hok hs
      apply hs
      rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl
      · exact Softmax.statsOk_0
      · rw [Softmax.statsOk_1]
        exact Softmax.sumOk0_of hsc (hH rfl) (hW (by simp [Softmax.chunks]))
      · obtain ⟨hm, hl⟩ := hRl (.inl rfl)
        rw [Softmax.statsOk_2]
        exact Softmax.sumOk1_of hsc hm hl (hW (by simp [Softmax.chunks]))
      · exact Softmax.statsOk_3
    · obtain ⟨p, ok, acq, sc, hk⟩ := hev
      rename_i hne
      exact hne _ _ _ _ _ hk
  by_cases hg0 : site = .gen 0
  · subst hg0
    simp only [Softmax.next] at hn'
    split_ifs at hn' with hok
    exact hok (Softmax.expOk0_of hsc (hH rfl) (hW (by simp [Softmax.chunks])))
  by_cases hg1 : site = .gen 1
  · subst hg1
    simp only [Softmax.next] at hn'
    split_ifs at hn' with hok
    obtain ⟨hm, -⟩ := hRl (.inl rfl)
    exact hok (Softmax.expOk1_of hsc hm (hW (by simp [Softmax.chunks])))
  exact soft_next_some hev hex (fun lp c h => hld ⟨lp, c, h⟩) hg0 hg1 (fun w h => hst ⟨w, h⟩) hn'

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
