-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemSite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemAccSite
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemWait
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' Tensor Memory operations, on their traces

A load (`corr_ld`) reads columns of one stage's accumulator with `pArr = q ≥ 1` P-full arrivals of
the stage before it, and its `wait::ld` is the lane's next event (`corr_ld_wait'`). A store
(`corr_st`) writes 16 columns of one stage's accumulator with `q ≥ 1` arrivals; every later event of
the lane that is not a `tcgen05` event comes after a `wait::st` with the same arrivals
(`corr_st_wait`). A load of a cell comes before a store of the cell with the same arrivals
(`corr_ld_st`), and a cell is stored once per credit (`corr_st_one`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The correction state a Tensor Memory load or store is fired from. -/
theorem role_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hk : (∃ a vals sh, e.kind = .tc (.ld a vals sh)) ∨ ∃ a vals sh, e.kind = .tc (.st a vals sh)) :
    ∃ d n r ℓ, Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) ∧
      RefQ p L g d (CorrWarp.rc n) r ℓ ∧ Ev p L g d e := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    rintro f hf
    rcases hk with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [h] at hf <;> cases hf
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n, -, -, -, hin, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · exfalso
    have hx : exit L g s = none := hin.2
    obtain ⟨site, x1, x2, x3⟩ := s
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    rcases hk with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> cases site
    case inl.enter | inr.enter => simp [exit] at hx
    case inl.sh j | inr.sh j => fin_cases j <;> simp [Startup.Ev] at hev
    all_goals simp [Startup.Ev] at hev
  · obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, -⟩ := hR h0
    rcases hev.data_or_vote with h | ⟨_,_,hv⟩
    · exact ⟨d, n, r, ℓ, hσ, hQ, h⟩
    · rcases hk with ⟨_,_,_,hk⟩ | ⟨_,_,_,hk⟩ <;> rw [hk] at hv <;> cases hv

set_option maxHeartbeats 8000000 in
/-- **A load is fired at a rescale or a final load**, not at an implicit wait. -/
theorem ld_site {d : D} {pc a : Nat} {vals : List Value} {sh : TcShape}
    (hev : Ev p L g d ⟨pc, .tc (.ld a vals sh)⟩) :
    (∃ st c, d.site = .rld st c) ∨ (∃ st j, d.site = .fld st j) ∨ ∃ st c, d.site = .rldw st c := by
  obtain ⟨s, v, kk⟩ := d
  cases s
  case rld st c => exact .inl ⟨st, c, rfl⟩
  case fld st j => exact .inr (.inl ⟨st, j, rfl⟩)
  case rldw st c => exact .inr (.inr ⟨st, c, rfl⟩)
  all_goals exfalso
  all_goals simp only [Ev] at hev
  all_goals first
    | (unfold Epilogue.Ev at hev; split at hev <;> simp_all [Epilogue.isStore]; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [rdOrUb]

/-- The chunk a load or store site accesses, as its columns. -/
theorem corr_ld_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TLd (g, k) a vals sh) :
    ∃ d n r ℓ, Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) ∧
      RefQ p L g d (CorrWarp.rc n) r ℓ ∧ sh = .s32x32b ∧ ∃ st : Fin 2,
        (∃ c : Fin 8, d.site = .rld st c ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧
          vals.length = 16) ∨
        ∃ c : Fin 16, d.site = .fld st c ∧ a % 65536 = 256 + 128 * st.val + 8 * c.val ∧
          vals.length = 8 := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, r, ℓ, hσ, hQ, hev⟩ := role_state hp hX hFw hw hw1 he (.inl ⟨_, _, _, rfl⟩)
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨site, v, kk⟩ := d
  rcases ld_site hev with ⟨st, c, hs⟩ | ⟨st, c, hs⟩ | ⟨st, c, hs⟩ <;>
    change site = _ at hs <;> subst hs
  · obtain ⟨h1, h2, h3⟩ := rld_col hat hc hf rfl
    exact ⟨_, n, r, ℓ, hσ, hQ, h1, st, .inl ⟨c, rfl, h2, h3⟩⟩
  · obtain ⟨h1, h2, h3⟩ := fld_col hat hc hf rfl
    exact ⟨_, n, r, ℓ, hσ, hQ, h1, st, .inr ⟨c, rfl, h2, h3⟩⟩
  · exfalso
    have hk1 : kk = 1 := by have := hQ.sub rfl; simpa [kIn, Control.D.scheduler] using this
    subst hk1
    have := rldw_wait hat hc hf
    cases this

/-- **A load of a correction lane** reads columns of one stage's accumulator. -/
theorem corr_ld (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TLd (g, k) a vals sh) :
    sh = .s32x32b ∧ ∃ st < 2, 256 + 128 * st ≤ a % 65536 ∧
      a % 65536 + vals.length ≤ 384 + 128 * st ∧ 1 ≤ Tm.pArr L X g st k := by
  obtain ⟨d, n, r, ℓ, hσ, hQ, hsh, st, h⟩ := corr_ld_state hp hX hFw hw hw1 hl
  refine ⟨hsh, st.val, st.isLt, ?_⟩
  rcases h with ⟨c, hs, h1, h2⟩ | ⟨c, hs, h1, h2⟩
  · have := site_arr hσ hQ (st := st) (.inl ⟨c, hs⟩)
    have := c.isLt
    omega
  · have := site_arr hσ hQ (st := st) (.inr (.inr ⟨c, hs⟩))
    have := c.isLt
    omega

/-- The state of a store, with its chunk. -/
theorem corr_st_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TSt (g, k) a vals sh) :
    ∃ d n r ℓ, Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) ∧
      RefQ p L g d (CorrWarp.rc n) r ℓ ∧ sh = .s32x32b ∧ ∃ (st : Fin 2) (c : Fin 8),
        d.site = .rst st c ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16 := by
  obtain ⟨pc, he⟩ := hl
  obtain ⟨d, n, r, ℓ, hσ, hQ, hev⟩ := role_state hp hX hFw hw hw1 he (.inr ⟨_, _, _, rfl⟩)
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨st, c, hs⟩ := corr_st_site hev
  obtain ⟨site, v, kk⟩ := d
  change site = _ at hs
  subst hs
  obtain ⟨h1, h2, h3⟩ := rst_col hat hc hf rfl
  exact ⟨_, n, r, ℓ, hσ, hQ, h1, st, c, rfl, h2, h3⟩

/-- **A store of a correction lane** writes 16 columns of one stage's accumulator. -/
theorem corr_st (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TSt (g, k) a vals sh) :
    sh = .s32x32b ∧ ∃ st < 2, 256 + 128 * st ≤ a % 65536 ∧
      a % 65536 + vals.length ≤ 384 + 128 * st ∧ 1 ≤ Tm.pArr L X g st k := by
  obtain ⟨d, n, r, ℓ, hσ, hQ, hsh, st, c, hs, h1, h2⟩ := corr_st_state hp hX hFw hw hw1 hl
  have := site_arr hσ hQ (st := st) (.inr (.inl ⟨c, hs⟩))
  have := c.isLt
  exact ⟨hsh, st.val, st.isLt, by omega, by omega, by omega⟩

/-- **The event after a correction lane's load is its `wait::ld`**. -/
theorem corr_ld_wait' (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    {k a : Nat} {vals : List Value} {sh : TcShape} (hl : X.TLd (g, k) a vals sh)
    {q : Nat} {ev : Event} (hq : k < q) (hget : X.get (g,q) = some ev)
    (hub : ∀ f, ev.kind ≠ .ub f) : ∃ pc, X.get (g, k + 1) = some ⟨pc, .tc .waitLd⟩ := by
  have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[q]? = _ from hget)).1
  have hlt : k + 1 < (X.tr g).length := by omega
  obtain ⟨d, n, r, ℓ, hσ, hQ, -, st, hs⟩ := corr_ld_state hp hX hFw hw hw1 hl
  obtain ⟨pc, he⟩ := hl
  have hg := Frame.lt_of_get hX he
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k + 1) = some e1 := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hu : ∀ f, e1.kind ≠ .ub f := by
    rcases Nat.eq_or_lt_of_le hq with h | h
    · rw [← h] at hget
      rw [he1] at hget
      cases hget
      exact hub
    · exact Frame.noUbBefore_of_get hX hget _ h _ he1
  have hst : Frame.stateAt (thread p L) X g (k + 1) =
      ((Control.code p L g).next d ⟨pc, .tc (.ld a vals sh)⟩).map
        (Option.map fun d' => CorrWarp.cinj p L g d' (Code.bump (Proof.cls L g) n
          ⟨pc, .tc (.ld a vals sh)⟩)) := by
    rw [Frame.stateAt_succ (show (X.tr g)[k]? = _ from he), hσ]
    exact CorrWarp.next_cinj d n _
  suffices h : e1.kind = .tc .waitLd by
    obtain ⟨pc1, kd⟩ := e1
    simp only at h
    subst h
    exact ⟨pc1, he1⟩
  obtain ⟨s, v, kk⟩ := d
  rcases hs with ⟨c, hs, -⟩ | ⟨c, hs, -⟩ <;> change s = _ at hs <;> subst hs
  · have hk0 : kk = 0 := by have := hQ.sub rfl; simpa [kIn, Control.D.scheduler] using this
    subst hk0
    simp only [Control.code, Control.succ, Option.map_some] at hst
    obtain ⟨t,ins,o,hat,_,hc,hf⟩ :=
      Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he1 hst hu
    exact rldw_wait hat hc hf
  · simp only [Control.code, Control.succ, Option.map_some] at hst
    exact (CorrWarp.fired_both hp hX he1 hst hu).1

/-! ### After a store -/

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- The states after a store: the stage's loop up to its P-full arrival, at position
`k + 23 - 3 c`. -/
theorem after_store {k : Nat} {d : Control.D} {n : Cls → Nat} {st : Fin 2} {c : Fin 8}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hs : d.site = .rst st c) {Q : Nat} {ev : Event} (hQ : X.get (g, Q) = some ev)
    (hub : ∀ f, ev.kind ≠ .ub f) :
    ∀ i, k ≤ i → i ≤ Q → i + 3 * c.val ≤ k + 23 → ∃ d n,
      Frame.stateAt (thread p L) X g i = some (some (CorrWarp.cinj p L g d n)) ∧
      stPos st d.site = 3 * c.val + 3 + (i - k) ∧
      ∀ e, X.get (g, i) = some e → Ev p L g d e ∧ ∀ f, e.kind ≠ .ub f := by
  have hnub : ∀ u, u ≤ Q → ∀ e, X.get (g, u) = some e → ∀ f, e.kind ≠ .ub f := by
    intro u hu e he f hf
    rcases Nat.eq_or_lt_of_le hu with rfl | hlt
    · rw [hQ] at he; cases he; exact hub f hf
    obtain ⟨σ, n', hσ', h0⟩ : ∃ σ n', Frame.stateAt (thread p L) X g Q = some (some (σ, n')) ∧
        n' .ub = 0 := by
      rcases CorrWarp.open_ev hp hX hFw hw hw1 hQ hub with ⟨s, n', h, h0, -⟩ | ⟨d', n', h, h0, -⟩
      · exact ⟨_, _, h, h0⟩
      · exact ⟨_, _, h, h0⟩
    have hc := count hσ' .ub
    rw [h0, List.countP_eq_zero] at hc
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    refine hc ⟨pc, .ub f⟩ (List.mem_of_getElem? (i := u) ?_) (by simp [Proof.cls])
    rw [List.getElem?_take, ite_eq_left hlt]; exact he
  intro i hki
  induction i, hki using Nat.le_induction with
  | base =>
    intro _ _
    exact ⟨d, n, hσ, by rw [hs]; simp [stPos], fun e he =>
      ⟨stPos_shape (st := st) (d := d) (by rw [hs]; simp [stPos])
        (CorrWarp.fired_both hp hX he hσ (hnub k (by omega) e he)).1, hnub k (by omega) e he⟩⟩
  | succ i hki ih =>
    intro hiQ hiA
    obtain ⟨d0, n0, h0, hpos, hev⟩ := ih (by omega) (by omega)
    have hil : i + 1 < (X.tr g).length := by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr g)[Q]? = _ from hQ)).1
      omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, i) = some e :=
      ⟨_, List.getElem?_eq_getElem (show i < (X.tr g).length by omega)⟩
    obtain ⟨e', he'⟩ : ∃ e, X.get (g, i + 1) = some e := ⟨_, List.getElem?_eq_getElem hil⟩
    have hst : Frame.stateAt (thread p L) X g (i + 1) = ((Control.code p L g).next d0 e).map
        (Option.map fun d' => CorrWarp.cinj p L g d' (Code.bump (Proof.cls L g) n0 e)) := by
      rw [Frame.stateAt_succ (show (X.tr g)[i]? = _ from he), h0]
      exact CorrWarp.next_cinj d0 n0 _
    have hsome : ∃ σ, Frame.stateAt (thread p L) X g (i + 1) = some (some σ) := by
      rcases CorrWarp.open_ev hp hX hFw hw hw1 he' (hnub (i + 1) hiQ e' he') with
        ⟨s, n', h, -⟩ | ⟨d', n', h, -⟩ <;> exact ⟨_, h⟩
    obtain ⟨σ, hσ'⟩ := hsome
    rw [hσ'] at hst
    cases hn : (Control.code p L g).next d0 e with
    | none => rw [hn] at hst; cases hst
    | some o =>
      cases o with
      | none => rw [hn] at hst; cases hst
      | some d' =>
        rw [hn] at hst
        simp only [Option.map_some, Option.some.injEq] at hst
        subst hst
        have hp' := stPos_next_control (st := st) (by omega) (by omega) hn
        exact ⟨d', _, hσ', by rw [hp', hpos]; omega, fun e he =>
          ⟨stPos_shape (st := st) (d := d') (by rw [hp', hpos]; omega)
            (CorrWarp.fired_both hp hX he hσ' (hnub _ hiQ e he)).1, hnub (i + 1) hiQ e he⟩⟩

/-- The event of the P-full arrival after a store. -/
theorem after_store_arr {k : Nat} {d : Control.D} {n : Cls → Nat} {st : Fin 2} {c : Fin 8}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hs : d.site = .rst st c) {Q : Nat} {ev : Event} (hQ : X.get (g, Q) = some ev)
    (hub : ∀ f, ev.kind ≠ .ub f) (hA : k + 23 < Q + 3 * c.val) :
    Tm.pArr L X g st k + 1 ≤ Tm.pArr L X g st Q := by
  have hc := c.isLt
  obtain ⟨d', n', hσ', hpos, hev⟩ := after_store hp hX hFw hw hw1 hσ hs hQ hub
    (k + 23 - 3 * c.val) (by omega) (by omega) (by omega)
  obtain ⟨e, he⟩ : ∃ e, X.get (g, k + 23 - 3 * c.val) = some e :=
    ⟨_, List.getElem?_eq_getElem (show k + 23 - 3 * c.val < (X.tr g).length by
      have := (List.getElem?_eq_some_iff.mp (show (X.tr g)[Q]? = _ from hQ)).1
      omega)⟩
  obtain ⟨hev1, hub1⟩ := hev e he
  change stPos st d'.scheduler.site = _ at hpos
  have harr := (stPos_ev (d := d'.scheduler) (st := st) (by omega) hev1 hub1).2.2 (by omega)
  unfold Tm.pArr arrivals
  have h1 : ((X.tr g).take (k + 23 - 3 * c.val + 1)).countP
      (arrivesOn (Tm.pFull L (g / L.block) st)) =
      ((X.tr g).take (k + 23 - 3 * c.val)).countP
        (arrivesOn (Tm.pFull L (g / L.block) st)) + 1 := by
    rw [List.take_add_one, show (X.tr g)[k + 23 - 3 * c.val]? = some e from he,
      Option.toList_some, List.countP_append]
    simp [harr]
  have h2 : ((X.tr g).take k).countP (arrivesOn (Tm.pFull L (g / L.block) st)) ≤
      ((X.tr g).take (k + 23 - 3 * c.val)).countP (arrivesOn (Tm.pFull L (g / L.block) st)) :=
    (List.take_prefix_take_left (show k ≤ k + 23 - 3 * c.val by omega)).sublist.countP_le
  have h3 : ((X.tr g).take (k + 23 - 3 * c.val + 1)).countP
      (arrivesOn (Tm.pFull L (g / L.block) st)) ≤
      ((X.tr g).take Q).countP (arrivesOn (Tm.pFull L (g / L.block) st)) :=
    (List.take_prefix_take_left (show k + 23 - 3 * c.val + 1 ≤ Q by omega)).sublist.countP_le
  omega

/-- **A store is waited for with its credit** before every later event of its lane that is not a
`tcgen05` event. -/
theorem corr_st_wait {k a st : Nat} {vals : List Value} {sh : TcShape}
    (hl : X.TSt (g, k) a vals sh) (hst : st < 2) (hcol : 256 + 128 * st ≤ a % 65536)
    (hcol' : a % 65536 < 384 + 128 * st) {e : Nat} (hne : Tm.NonTcAfter X g k e) :
    ∃ w pc, k < w ∧ w < e ∧ X.get (g, w) = some ⟨pc, .tc .waitSt⟩ ∧
      Tm.pArr L X g st w = Tm.pArr L X g st k := by
  obtain ⟨d, n, r, ℓ, hσ, hQ, -, st', c, hs, h1, -⟩ := corr_st_state hp hX hFw hw hw1 hl
  have hc := c.isLt
  have hst' := st'.isLt
  obtain rfl : st = st'.val := by omega
  obtain ⟨hke, ev, hget, htc, hub⟩ := hne
  have hel := (List.getElem?_eq_some_iff.mp (show (X.tr g)[e]? = _ from hget)).1
  have hA : k + 23 ≤ e + 3 * c.val := by
    by_contra hlt
    obtain ⟨d', n', -, hpos, hev⟩ := after_store hp hX hFw hw hw1 hσ hs hget hub e hke.le le_rfl
      (by omega)
    change stPos st' d'.scheduler.site = _ at hpos
    obtain ⟨tk, h⟩ := (stPos_ev (d := d'.scheduler) (st := st')
      (by omega) (hev ev hget).1 hub).1 (by omega)
    exact htc tk h
  have hev : ∀ i, k ≤ i → i + 3 * c.val ≤ k + 22 → ∀ e', X.get (g, i) = some e' →
      (∃ tk, e'.kind = .tc tk) ∧ (i + 3 * c.val = k + 22 → e'.kind = .tc .waitSt) := by
    intro i hki hi e' he'
    obtain ⟨d', n', -, hpos, hev⟩ := after_store hp hX hFw hw hw1 hσ hs hget hub i hki (by omega)
      (by omega)
    change stPos st' d'.scheduler.site = _ at hpos
    obtain ⟨q1, q2, -⟩ := stPos_ev (d := d'.scheduler) (st := st')
      (by omega) (hev e' he').1 (hev e' he').2
    exact ⟨q1 (by omega), fun h => q2 (by omega)⟩
  obtain ⟨e', he'⟩ : ∃ e', X.get (g, k + 22 - 3 * c.val) = some e' :=
    ⟨_, List.getElem?_eq_getElem (show k + 22 - 3 * c.val < (X.tr g).length by omega)⟩
  have hkd := (hev (k + 22 - 3 * c.val) (by omega) (by omega) e' he').2 (by omega)
  obtain ⟨pc, kd⟩ := e'
  simp only at hkd
  subst hkd
  refine ⟨k + 22 - 3 * c.val, pc, by omega, by omega, he', ?_⟩
  unfold Tm.pArr arrivals
  refine Tm.countP_take_eq (by omega) (by omega) fun i e' hki hi he' => ?_
  obtain ⟨tk, h⟩ := (hev i hki (by omega) e' he').1
  obtain ⟨pc', kd⟩ := e'
  simp only at h
  subst h
  rfl

/-- **A load of a cell comes before the store of the cell with the same credit.** -/
theorem corr_ld_st {k k' a a' j j' st : Nat} {vals vals' : List Value} {sh sh' : TcShape}
    (hl : X.TLd (g, k) a vals sh) (hs : X.TSt (g, k') a' vals' sh') (hst : st < 2)
    (hcol : 256 + 128 * st ≤ a % 65536) (hcol' : a % 65536 < 384 + 128 * st)
    (hj : j < vals.length) (hj' : j' < vals'.length) (hc : a % 65536 + j = a' % 65536 + j')
    (hq : Tm.pArr L X g st k = Tm.pArr L X g st k') : k < k' := by
  by_contra hle
  have hle := Nat.le_of_not_lt hle
  obtain ⟨d, n, r, ℓ, hσ, -, -, st1, hsd⟩ := corr_ld_state hp hX hFw hw hw1 hl
  obtain ⟨d', n', r', ℓ', hσ', -, -, st2, c2, hs2, e2, l2⟩ := corr_st_state hp hX hFw hw hw1 hs
  obtain ⟨pc, he⟩ := hl
  have h1 := st1.isLt
  have h2 := st2.isLt
  have h3 := c2.isLt
  have hst1 : st1.val = st := by
    rcases hsd with ⟨c, -, e1, l1⟩ | ⟨c, -, e1, l1⟩ <;> have := c.isLt <;> omega
  have hst2 : st2.val = st := by
    rcases hsd with ⟨c, -, e1, l1⟩ | ⟨c, -, e1, l1⟩ <;> have := c.isLt <;> omega
  obtain rfl : st1 = st2 := Fin.ext (by omega)
  subst hst1
  by_cases hA : k' + 23 < k + 3 * c2.val
  · have := after_store_arr hp hX hFw hw hw1 hσ' hs2 he (by intro f h; cases h) hA
    omega
  · obtain ⟨d2, n2, hσ2, hpos, -⟩ := after_store hp hX hFw hw hw1 hσ' hs2 he
      (by intro f h; cases h) k hle le_rfl (by omega)
    rw [hσ] at hσ2
    simp only [CorrWarp.cinj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and] at hσ2
    obtain ⟨rfl, -⟩ := hσ2
    rcases hsd with ⟨c, hs1, e1, l1⟩ | ⟨c, hs1, e1, l1⟩ <;> rw [hs1] at hpos <;>
      simp only [stPos, ↓reduceIte] at hpos <;> omega

/-- **A correction lane stores each cell once per credit.** -/
theorem corr_st_one {k k' a a' j j' st : Nat} {vals vals' : List Value} {sh sh' : TcShape}
    (hl : X.TSt (g, k) a vals sh) (hs : X.TSt (g, k') a' vals' sh') (hst : st < 2)
    (hcol : 256 + 128 * st ≤ a % 65536) (hcol' : a % 65536 < 384 + 128 * st)
    (hj : j < vals.length) (hj' : j' < vals'.length) (hc : a % 65536 + j = a' % 65536 + j')
    (hq : Tm.pArr L X g st k = Tm.pArr L X g st k') : k = k' := by
  have key : ∀ {k k' a a' j j' : Nat} {vals vals' : List Value} {sh sh' : TcShape},
      X.TSt (g, k) a vals sh → X.TSt (g, k') a' vals' sh' → 256 + 128 * st ≤ a % 65536 →
      a % 65536 < 384 + 128 * st → j < vals.length → j' < vals'.length →
      a % 65536 + j = a' % 65536 + j' → Tm.pArr L X g st k = Tm.pArr L X g st k' → ¬ k < k' := by
    intro k k' a a' j j' vals vals' sh sh' hl hs hcol hcol' hj hj' hc hq hlt
    obtain ⟨d, n, r, ℓ, hσ, -, -, st1, c1, hs1, e1, l1⟩ := corr_st_state hp hX hFw hw hw1 hl
    obtain ⟨d', n', r', ℓ', hσ', -, -, st2, c2, hs2, e2, l2⟩ := corr_st_state hp hX hFw hw hw1 hs
    obtain ⟨pc, he⟩ := hs
    have h1 := st1.isLt
    have h2 := st2.isLt
    have h3 := c2.isLt
    have h4 := c1.isLt
    obtain rfl : st1 = st2 := Fin.ext (by omega)
    obtain rfl : c1 = c2 := Fin.ext (by omega)
    obtain rfl : st = st1.val := by omega
    by_cases hA : k + 23 < k' + 3 * c1.val
    · have := after_store_arr hp hX hFw hw hw1 hσ hs1 he (by intro f h; cases h) hA
      omega
    · obtain ⟨d2, n2, hσ2, hpos, -⟩ := after_store hp hX hFw hw hw1 hσ hs1 he
        (by intro f h; cases h) k' hlt.le le_rfl (by omega)
      rw [hσ'] at hσ2
      simp only [CorrWarp.cinj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq,
        heq_eq_eq, true_and] at hσ2
      obtain ⟨rfl, -⟩ := hσ2
      rw [hs2] at hpos
      simp only [stPos, ↓reduceIte] at hpos
      omega
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact absurd h (key hl hs hcol hcol' hj hj' hc hq)
  · exact h
  · refine absurd h (key hs hl ?_ ?_ hj' hj hc.symm hq.symm)
    all_goals
      obtain ⟨d, n, r, ℓ, hσ, -, -, st1, c1, hs1, e1, l1⟩ := corr_st_state hp hX hFw hw hw1 hl
      obtain ⟨d', n', r', ℓ', hσ', -, -, st2, c2, hs2, e2, l2⟩ := corr_st_state hp hX hFw hw hw1 hs
      have h1 := st1.isLt
      have h2 := st2.isLt
      have h3 := c2.isLt
      have h4 := c1.isLt
      omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
