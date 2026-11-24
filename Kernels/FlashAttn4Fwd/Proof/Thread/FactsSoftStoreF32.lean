-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftStore
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftSt
public import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # The softmax statistics words as single-precision words

A softmax statistics store writes the bytes of the rescale factor's register (`alphaWord`: the
bits `0f3F800000` of `1`, or the number `2 ^ gap`) or of the row sum's (a number) (`soft_wr`):
each is a canonical single-precision word that rebuilds from its bytes (`F32Word`,
`FloatFacts_soft_store_f32`). A statistics arrival of generation `(n + 1) j + t + 1` (`t < n`) is
the named barrier `gen 1` of loop trip `t` or the item's last `gen 2`; the event before it is the
trip's store of the rescale factor or the item's store of the row sum (the only sites stepping to
them), of the same generation (`FloatFacts_soft_arrive_store`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A single-precision payload or a 32-bit pattern that reads as `x` is a canonical word of
`x`. -/
theorem f32Val_of {v : Value} {x : ℝ}
    (hf : (∃ y, v = .float .f32 y) ∨ ∃ b : BitVec 64, v = .bits 32 b ∧ b.toNat < 2 ^ 32)
    (hr : valFloat .f32 v = .ok x) : F32Val v x := by
  refine ⟨?_, hr⟩
  rcases hf with ⟨y, rfl⟩ | h
  · rw [valFloat_float] at hr
    cases hr
    exact .inl rfl
  · exact .inr h

/-- The rescale factor's word is a canonical single-precision word, on payload words and a
reference that is a number. -/
theorem alphaV_f32Val {L : Launch} (hsc : Softmax.ScaleOk L) {d : Softmax.D} {x : ℝ}
    (hm : d.m = .float .f32 x) (hw : Softmax.WordsF32 d.w) :
    F32Val (Softmax.alphaV L d) (Softmax.alpha L d) := by
  refine f32Val_of ?_ (Softmax.alphaV_read hsc hm hw)
  unfold Softmax.alphaV
  split
  · exact .inr ⟨_, rfl, by decide⟩
  · rw [Softmax.gapV_read hsc hm hw, ex2E_fin valFloat_float]
    exact .inl ⟨_, rfl⟩

theorem f32Word_of {v : Value} {x : ℝ} (hv : F32Val v x) : F32Word v.toBytes x := by
  refine ⟨v, rfl, rebuild_scalar (by rw [hv.bytes_eq]; decide) ?_, hv⟩
  rcases hv.1 with rfl | ⟨b, rfl, -⟩ <;> rfl

theorem f32Val_float (x : ℝ) : F32Val (.float .f32 x) x :=
  ⟨.inl rfl, by simp [valFloat, pure, Except.pure]⟩

/-- The sites stepping to the named barriers `gen 1` and `gen 2`. -/
theorem soft_gen_prev_site {L : Launch} {g : Nat} {d d' : Softmax.D} {e : Event}
    (hn : Softmax.next L g d e = some (some d')) :
    (d'.site = .gen 1 → d.site = .alphaSt) ∧ (d'.site = .gen 2 → d.site = .lSt) := by
  obtain ⟨site, i, t, w, m, l⟩ := d
  rcases site with _ | _ | w | lp | ⟨lp, c⟩ | ⟨lp, c⟩ | _ | j | ⟨lp, c⟩ | ⟨lp, c⟩ | lp |
    lp | lp | lp | _ | _ | _
  all_goals (try rcases Softmax.fin4_cases w with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin3_cases j with rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin4_cases c with rfl | rfl | rfl | rfl)
  all_goals (try rcases Softmax.fin2_cases c with rfl | rfl)
  all_goals (try cases lp)
  all_goals simp only [Softmax.next, Softmax.nextItem, Softmax.afterStats,
    Softmax.afterLoad] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try subst hn)
  all_goals simp_all

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **At a statistics store site, after single-precision loads, the reference, the row sum
and the words are single-precision payloads.** -/
theorem stats_f32 {g i : Nat} {d : Softmax.D} (hw : warpOf L g < 8)
    (hc : Softmax.Counts L g d ((X.tr g).take i)) (hs : d.site = .alphaSt ∨ d.site = .lSt)
    (hld : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    (∃ x, d.m = .float .f32 x) ∧ (∃ y, d.l = .float .f32 y) ∧
      (d.site = .alphaSt → Softmax.WordsF32 d.w) := by
  have hF := soft_loadsF32_of hpre hX ht hw hld
  obtain ⟨-, hR⟩ := hc.refs hF (Softmax.scale_ok hpre)
  obtain ⟨hm, hl⟩ := hR (by rcases hs with h | h <;> simp [h, Softmax.Site.inTrip])
  exact ⟨⟨_, hm⟩, ⟨_, hl⟩, fun h =>
    Softmax.words_f32 hc.words hF (by simp [Softmax.chunks, h])⟩

/-- **`FloatFacts.soft_store_f32`**, once the thread's earlier loads returned single-precision
floats. -/
theorem FloatFacts_soft_store_f32 {g i pc : Nat} {a : Acc} {ws : List Byte} (_hg : g < L.threads)
    (hw : warpOf L g < 8) (he : X.get (g, i) = some ⟨pc, .wr a ws⟩)
    (_hs : SoftStore L X g i a true)
    (hld : ∀ k < i, ∀ pc a' (vals' : List Value),
      X.get (g, k) = some ⟨pc, .tc (.ld a' vals' .s32x32b)⟩ → F32s vals') :
    ∃ x, F32Word ws x := by
  obtain ⟨d, -, hc, -, -, -, hs⟩ := soft_wr hpre hX ht hw he
  obtain ⟨⟨xm, hm⟩, ⟨yl, hl⟩, hwf⟩ :=
    stats_f32 hpre hX ht hw hc (hs.imp (·.1) (·.1)) hld
  rcases hs with ⟨hs, rfl⟩ | ⟨-, v, hv, rfl⟩
  · exact ⟨_, f32Word_of (alphaV_f32Val (Softmax.scale_ok hpre) hm (hwf hs))⟩
  · rw [hl, storeValue_of_bytes (by rfl)] at hv
    cases hv
    exact ⟨_, f32Word_of (f32Val_float yl)⟩

/-- A softmax statistics store is a `SoftStore`. -/
theorem soft_softStore {g i pc : Nat} {a : Acc} {ws : List Byte} (hw : warpOf L g < 8)
    (he : X.get (g, i) = some ⟨pc, .wr a ws⟩) : SoftStore L X g i a true := by
  obtain ⟨d, -, -, -, hl, hsz, -⟩ := soft_wr hpre hX ht hw he
  have hb := hpre.block
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcov : a.Covers a.loc := ⟨rfl, rfl, le_rfl, by omega⟩
  have hin : InStatsArea L a.loc := by
    rw [hl]
    simp only [InStatsArea, Softmax.sb, Softmax.tidOf]
    simp only [warpOf] at hw
    refine ⟨by trivial, by omega, by omega⟩
  rcases Facts.Soft.stats_access hpre hX ht hw (.inr (.inl ⟨ws, ⟨pc, he⟩, rfl⟩)) hcov hin with
    ⟨-, h⟩ | ⟨h8, -⟩
  · exact h
  · omega

/-- **`FloatFacts.soft_arrive_store`.** -/
theorem FloatFacts_soft_arrive_store {g y pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (_hg : g < L.threads) (hw : warpOf L g < 8) (he : X.get (g, y) = some ⟨pc, .bar id cnt md⟩)
    (hid : id ≠ 2)
    (hG : ∃ j t, t < kvTiles L ∧ barOrd X g y id = (kvTiles L + 1) * j + t + 1) :
    ∃ i < y, ∃ pc' a ws, X.get (g, i) = some ⟨pc', .wr a ws⟩ ∧ SoftStore L X g i a true ∧
      barOrd X g i id = barOrd X g y id := by
  rcases soft_bar hpre hX ht hw he with ⟨h, -⟩ | ⟨-, -, rfl⟩
  · exact absurd h hid
  obtain ⟨d, t, ins, o, hσ, hc, hi, -, -, -, hev⟩ :=
    soft_state hpre hX ht he hw (fun _ _ h => by cases h) (by simp [Prologue.ProKind])
  obtain ⟨j, tt, htt, hb⟩ := hG
  rw [soft_barOrd_gen hpre hX ht hw hc] at hb
  have hn1 : kvTiles L = Softmax.trips L := rfl
  rw [hn1] at htt hb
  -- the site is `gen 1` or `gen 2`
  have hsite : d.site = .gen 1 ∨ d.site = .gen 2 := by
    have hla := hi.last
    have htr := hi.trip
    have ht0 := hi.tile0
    obtain ⟨site, ii, t', ww, mm, ll⟩ := d
    simp only at hla htr ht0 hb ⊢
    cases site <;> simp only [Softmax.Ev, Kind.bar.injEq, reduceCtorEq, exists_false] at hev
    all_goals (try omega)
    rename_i jj
    rcases Softmax.fin3_cases jj with rfl | rfl | rfl
    · exfalso
      have := ht0 rfl
      simp [Softmax.genPos, Softmax.tileNo, Softmax.Site.tile0, Softmax.Site.afterGen] at hb
      have h1 : ((Softmax.trips L + 1) * ii) % (Softmax.trips L + 1) = 0 := Nat.mul_mod_right _ _
      have h2 : ((Softmax.trips L + 1) * j + tt + 1) % (Softmax.trips L + 1) = tt + 1 := by
        rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hb] at h1
      omega
    · exact .inl rfl
    · exact .inr rfl
  -- the event before it
  obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := by
    rcases y with _ | y'
    · exfalso
      have hst := hc.stats
      simp only [List.take_zero, okPolls, List.countP_nil] at hst
      have hla := hi.last
      obtain ⟨site, ii, t', ww, mm, ll⟩ := d
      simp only at hsite hst hla
      rcases hsite with rfl | rfl <;>
        simp [Softmax.statsPos, Softmax.Site.inItem, Softmax.Site.tile0] at hst <;> omega
    · exact ⟨y', rfl⟩
  have hlen : y' < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp he).1; simp only at this; omega
  obtain ⟨x, hx⟩ : ∃ x, X.get (g, y') = some x := ⟨_, List.getElem?_eq_getElem hlen⟩
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  obtain ⟨D0, hσ0⟩ := Frame.event_state hC hX ht hx
    (fun pc f h => Cross.not_ends_of_lt hX hx he (by omega) (.inl ⟨f, by rw [h]⟩))
  have hstep : Frame.stateAt (code L) X g (y' + 1) = (code L g).next D0 x := by
    have hx' : (X.tr g)[y']? = some x := hx
    rw [Frame.stateAt_succ hx', hσ0]
    rfl
  rw [hσ] at hstep
  replace hstep := hstep.symm
  -- the previous state is a softmax state at the store site
  obtain ⟨d0, rfl, hs0⟩ : ∃ d0 : Softmax.D, D0 = .inr (.softmax d0) ∧
      (d.site = .gen 1 → d0.site = .alphaSt) ∧ (d.site = .gen 2 → d0.site = .lSt) := by
    rcases D0 with p | r
    · exfalso
      simp only [code, Option.map_eq_some_iff] at hstep
      obtain ⟨o, -, ho⟩ := hstep
      cases o with
      | none => cases ho
      | some q =>
        simp only [Option.bind_some] at ho
        rcases q with p' | k
        · simp [handoff] at ho
        · simp only [handoff, Option.map_eq_some_iff] at ho
          obtain ⟨r, hr, hr'⟩ := ho
          injection hr' with hr'
          subst hr'
          cases k <;> simp only [Role.start, Option.some.injEq, reduceCtorEq] at hr
          injection hr with hr
          subst hr
          rcases hsite with h | h <;> simp [Softmax.start] at h
    · cases r with
      | softmax d0 =>
        refine ⟨d0, rfl, ?_⟩
        simp only [code] at hstep
        cases hn0 : Softmax.next L g d0 x with
        | none => rw [hn0] at hstep; cases hstep
        | some o =>
          rw [hn0] at hstep
          cases o with
          | none => simp at hstep
          | some d1 =>
            simp only [Option.map_some, Option.some.injEq, Function.comp, Sum.inr.injEq,
              Role.softmax.injEq] at hstep
            subst hstep
            exact soft_gen_prev_site hn0
      | _ =>
        exfalso
        obtain ⟨r', h1, h2⟩ := code_next_inr hstep
        injection h1 with h1
        subst h1
        simp [Role.kind] at h2
  -- the event before is the store
  obtain ⟨hev0, -, -⟩ := soft_ev_at hpre hX ht hσ0 hx
  have hwr : ∃ pc' a ws, x = ⟨pc', .wr a ws⟩ := by
    have hs0' : d0.site = .alphaSt ∨ d0.site = .lSt := by
      rcases hsite with h | h
      · exact .inl (hs0.1 h)
      · exact .inr (hs0.2 h)
    unfold Softmax.Ev at hev0
    rcases hs0' with h | h <;> rw [h] at hev0 <;>
      obtain ⟨sz, acq, rel, sc, el, rx, bs, hk⟩ := hev0 <;>
      exact ⟨x.pc, _, bs, by cases x with | mk xp xk => simp only at hk; subst hk; rfl⟩
  obtain ⟨pc', a, ws, rfl⟩ := hwr
  refine ⟨y', by omega, pc', a, ws, hx, soft_softStore hpre hX ht hw hx, ?_⟩
  unfold barOrd
  have hx' : (X.tr g)[y']? = some ⟨pc', .wr a ws⟩ := hx
  rw [List.take_add_one, hx', Option.toList_some, List.countP_append]
  simp [Execution.isBarId]

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
