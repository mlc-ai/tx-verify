-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Soft.CurDefs
import Kernels.InklingRelDecode.Proof.Softmax.BiasAt
import Kernels.InklingRelDecode.Proof.Softmax.PollStep
import Kernels.InklingRelDecode.Proof.Softmax.InvNext

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
open PTX PTX.Proof PTX.Flow Control Data

variable {Q : Params} {L : Launch} {g : Nat} {ent : Control.Entry}

theorem rec_keep {d : Data.D} {e : Event} {s : Site} (h : Plain d.c.site = true) :
    (record L d e s).cur = d.v.cur ∧ (record L d e s).ld = d.v.ld := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  cases s0 <;> try (simp [Plain] at h; done)
  all_goals (unfold record; dsimp only; repeat' split)
  all_goals first | exact ⟨rfl, rfl⟩ | contradiction

theorem next_plain {d dn : Control.D} {ev : Event} (h : Plain d.site = true)
    (step : Control.next ent L g d ev = some (some dn)) :
    dn.i = d.i ∧ postNxt dn.site = true := by
  obtain ⟨s, i, v⟩ := d
  cases s <;> try (simp [Plain] at h; done)
  all_goals simp only [Control.next] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals refine ⟨rfl, ?_⟩
  all_goals rfl


/-! ### The control step from the special sites -/

theorem loopSite_cases (e : Control.Entry) (t i : Nat) :
    (loopSite e t i = .epilogue ∧ i = e.limit) ∨ (loopSite e t i = .nxt 0 ∧ i ≠ e.limit) ∨
      (loopSite e t i = .waitS ∧ i ≠ e.limit ∧ nextEnabled e t i = false) := by
  unfold loopSite
  by_cases h1 : i = e.limit
  · simp [h1]
  · by_cases h2 : nextEnabled e t i = true <;> simp [h1, h2]

private theorem next_bar0 {d dn : Control.D} {ev : Event} (hs : d.site = .bar0)
    (step : Control.next ent L g d ev = some (some dn)) :
    (preEnabled ent (g % L.block) = true ∧ dn = {d with site := .pre 0}) ∨
      (preEnabled ent (g % L.block) = false ∧
        dn = {d with site := loopSite ent (g % L.block) d.i}) := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  split at step
  · cases step; exact .inl ⟨by assumption, rfl⟩
  · cases step; exact .inr ⟨by simp_all, rfl⟩

private theorem next_pre {d dn : Control.D} {ev : Event} {j : Fin 64} (hs : d.site = .pre j)
    (step : Control.next ent L g d ev = some (some dn)) :
    (∃ h : j.val + 1 < 64, dn = {d with site := .pre ⟨j.val + 1, h⟩}) ∨
      (j.val = 63 ∧ dn = {d with site := loopSite ent (g % L.block) d.i}) := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  split at step
  · cases step; exact .inl ⟨by assumption, rfl⟩
  · cases step; exact .inr ⟨by omega, rfl⟩

private theorem next_nxt {d dn : Control.D} {ev : Event} {j : Fin 64} (hs : d.site = .nxt j)
    (step : Control.next ent L g d ev = some (some dn)) :
    (∃ h : j.val + 1 < 64, dn = {d with site := .nxt ⟨j.val + 1, h⟩}) ∨
      (j.val = 63 ∧ dn = {d with site := .waitS}) := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  split at step
  · cases step; exact .inl ⟨by assumption, rfl⟩
  · cases step; exact .inr ⟨by omega, rfl⟩

private theorem next_bar21 {d dn : Control.D} {ev : Event} (hs : d.site = .bar21)
    (step : Control.next ent L g d ev = some (some dn)) :
    dn = {d with site := .arrive} ∨ dn = advance ent (g % L.block) d := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  split at step
  · cases step; exact .inl rfl
  · cases step; exact .inr rfl

private theorem next_arrive {d dn : Control.D} {ev : Event} (hs : d.site = .arrive)
    (step : Control.next ent L g d ev = some (some dn)) :
    dn = advance ent (g % L.block) d := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  cases step; rfl


/-! ### Transfer lemmas -/

theorem cur_vac {c : Control.D} {v : Vals} (h : c.site = .setMaxReg ∨ c.site = .bar0 ∨
    c.site = .epilogue) : CurOk Q L g ent ⟨c, v⟩ := by
  intro _
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rcases h with h | h | h <;> simp [h, loopLike, postNxt]

theorem cur_pre0 {c : Control.D} {v : Vals} (h : c.site = .pre 0) : CurOk Q L g ent ⟨c, v⟩ := by
  intro _
  refine ⟨fun j hj j' hj' => ?_, fun hl => ?_, fun j hj => ?_, fun hp => ?_⟩
  · rw [h] at hj
    cases hj
    exact absurd hj' (by simp)
  · simp [h, loopLike] at hl
  · simp [h] at hj
  · simp [h, postNxt] at hp

theorem cur_same {old : Data.D} {c' : Control.D} {v' : Vals} (hp : postNxt c'.site = true)
    (hi : c'.i = old.c.i) (hc : v'.cur = old.v.cur) (hl : v'.ld = old.v.ld)
    (ho : postNxt old.c.site = true) (h : CurOk Q L g ent old) : CurOk Q L g ent ⟨c', v'⟩ := by
  intro hv
  obtain ⟨-, h2, -, h4⟩ := h hv
  refine ⟨fun j hj => absurd hj (postNxt.not_pre hp j), fun _ j' hj' => ?_, fun j hj => absurd hj
    (postNxt.not_nxt hp j), fun _ hlt j' hj' => ?_⟩
  · simp only [hc, hi]
    exact h2 (postNxt.loop ho) j' hj'
  · simp only [hl, hi] at hlt ⊢
    exact h4 ho hlt j' hj'

/-- A state at the site the loop's control picks has the bias words its loads left. -/
theorem cur_loop {c : Control.D} {v : Vals} (hs : c.site = loopSite ent (g % L.block) c.i)
    (hcur : validRow ent (g % L.block) = true → c.site ≠ .epilogue →
      ∀ j' < 64, BW (v.cur j') (Lib.laneBias Q L g c.i j'))
    (hld : validRow ent (g % L.block) = true → c.site = .waitS → c.i + 1 < ent.limit →
      ∀ j' < 64, BW (v.ld j') (Lib.laneBias Q L g (c.i + 1) j')) : CurOk Q L g ent ⟨c, v⟩ := by
  rcases loopSite_cases ent (g % L.block) c.i with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩ <;> rw [← hs] at h
  · exact cur_vac (Or.inr (Or.inr h))
  · intro hv
    refine ⟨fun j hj => by simp_all, fun _ => hcur hv (by simp [h]), fun j hj j' hj' => ?_,
      fun hp => by simp [h, postNxt] at hp⟩
    rw [h] at hj
    cases hj
    exact absurd hj' (by simp)
  · intro hv
    exact ⟨fun j hj => by simp_all, fun _ => hcur hv (by simp [h]), fun j hj => by simp_all,
      fun _ hlt => hld hv h hlt⟩

/-! ### The loads of the bias sites -/

theorem bias_kind {old : Data.D} {e : Event} (hf : Fired ent L g old e)
    (hu : ∀ f, e.kind ≠ .ub f) (hs : (∃ j, old.c.site = .pre j) ∨ ∃ j, old.c.site = .nxt j) :
    ∃ a bs, e.kind = .rd a bs := by
  obtain ⟨t, ins, o, -, hc, fire⟩ := hf
  rcases hs with ⟨j, hj⟩ | ⟨j, hj⟩
  · have pcs : old.c.site.pc = 680 + 2 * j.val := by rw [hj]; rfl
    rw [pcs] at hc fire
    rcases Lib.global_load_kind hc (bias_pre_load j) fire with h | ⟨f, hf⟩
    · exact h
    · exact absurd hf (hu f)
  · have pcs : old.c.site.pc = 1124 + 2 * j.val := by rw [hj]; rfl
    rw [pcs] at hc fire
    rcases Lib.global_load_kind hc (bias_nxt_load j) fire with h | ⟨f, hf⟩
    · exact h
    · exact absurd hf (hu f)

theorem load_word {X : Execution} {k : Nat} {old : Data.D} {e : Event} {a : Acc}
    {bs : List (Option Byte)} {j : Fin 64} (hB : Lib.BiasEv Q L g X)
    (he : X.get (g, k) = some e) (pc : e.pc = old.c.site.pc) (hk : e.kind = .rd a bs)
    (hl : Led X g k old) :
    (old.c.site = .pre j → old.c.i = 0 →
      Lib.loadWord bs = .float .bf16 (Lib.laneBias Q L g 0 j.val)) ∧
    (old.c.site = .nxt j →
      Lib.loadWord bs = .float .bf16 (Lib.laneBias Q L g (old.c.i + 1) j.val)) := by
  obtain ⟨p, kd⟩ := e
  change kd = _ at hk
  subst hk
  change p = _ at pc
  have h := hB k p a bs j.val j.isLt he
  unfold Led at hl
  constructor
  · intro hs hi
    have := h.1 (by rw [pc, hs]; rfl)
    rw [hl, hs, hi] at this
    simp only [Site.afterS, Bool.toNat_false, Nat.add_zero] at this
    rw [Lib.loadWord, this]; rfl
  · intro hs
    have := h.2 (by rw [pc, hs]; rfl)
    rw [hl, hs] at this
    simp only [Site.afterS, Bool.toNat_false, Nat.add_zero] at this
    rw [Lib.loadWord, this]; rfl

/-! ### The words the special sites record -/

private theorem rec_bar0 {d : Data.D} {e : Event} {s : Site} (hs : d.c.site = .bar0) :
    (loopB s → (record L d e s).cur = (fun _ => dflt) ∧ (record L d e s).ld = fun _ => dflt) ∧
    (¬ loopB s → (record L d e s).cur = d.v.cur ∧ (record L d e s).ld = fun _ => dflt) := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  change s0 = _ at hs
  subst hs
  constructor <;> intro h <;> simp [record, h]

private theorem rec_pre {d : Data.D} {e : Event} {s : Site} {j : Fin 64} {a : Acc}
    {bs : List (Option Byte)} (hs : d.c.site = .pre j) (hk : e.kind = .rd a bs) :
    (loopB s → (record L d e s).cur = Function.update d.v.ld j.val (Lib.loadWord bs) ∧
      (record L d e s).ld = fun _ => dflt) ∧
    (¬ loopB s → (record L d e s).cur = d.v.cur ∧
      (record L d e s).ld = Function.update d.v.ld j.val (Lib.loadWord bs)) := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  change s0 = _ at hs
  subst hs
  constructor <;> intro h <;> simp [record, h, hk]

private theorem rec_nxt {d : Data.D} {e : Event} {s : Site} {j : Fin 64} {a : Acc}
    {bs : List (Option Byte)} (hs : d.c.site = .nxt j) (hk : e.kind = .rd a bs) :
    (record L d e s).cur = d.v.cur ∧
      (record L d e s).ld = Function.update d.v.ld j.val (Lib.loadWord bs) := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  change s0 = _ at hs
  subst hs
  simp [record, hk]

private theorem rec_bar21 {d : Data.D} {e : Event} {s : Site}
    (hs : d.c.site = .bar21 ∨ d.c.site = .arrive) :
    (s = .arrive → (record L d e s).cur = d.v.cur ∧ (record L d e s).ld = d.v.ld) ∧
    (s ≠ .arrive → (record L d e s).cur = d.v.ld ∧ (record L d e s).ld = fun _ => dflt) := by
  obtain ⟨⟨s0, i, hh⟩, v⟩ := d
  change s0 = _ ∨ s0 = _ at hs
  rcases hs with rfl | rfl <;> constructor <;> intro h <;> simp [record, h]

/-! ### One step -/

private theorem loopB_loopSite (e : Control.Entry) (t i : Nat) : loopB (loopSite e t i) := by
  rcases loopSite_cases e t i with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [loopB, h]

private theorem loopSite_ne_arrive (e : Control.Entry) (t i : Nat) :
    loopSite e t i ≠ .arrive := by
  rcases loopSite_cases e t i with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

private theorem next_setMax {d dn : Control.D} {ev : Event} (hs : d.site = .setMaxReg)
    (step : Control.next ent L g d ev = some (some dn)) : dn.site = .bar0 := by
  obtain ⟨s, i, v⟩ := d
  cases hs
  simp only [Control.next] at step
  cases step
  rfl

/-- The step from the end of a round to the next one. -/
private theorem cur_adv {old : Data.D} {c' : Control.D} {e : Event}
    (E : EntSp Q L g ent) (ok : ent.Ok) (hs : old.c.site = .bar21 ∨ old.c.site = .arrive)
    (hc : c' = advance ent (g % L.block) old.c) (hi' : Control.Inv ent (g % L.block) c')
    (h : CurOk Q L g ent old) (hne : c'.site ≠ .arrive) :
    CurOk Q L g ent ⟨c', record L old e c'.site⟩ := by
  obtain ⟨hcr, hld⟩ := (rec_bar21 (L := L) (d := old) (e := e) (s := c'.site) hs).2 hne
  have hsite : c'.site = loopSite ent (g % L.block) c'.i := by rw [hc]; rfl
  have hold : postNxt old.c.site = true := by rcases hs with hs | hs <;> simp [hs, postNxt]
  have hi1 : c'.i = old.c.i + 1 := by rw [hc]; rfl
  refine cur_loop hsite (fun hv hn j' hj' => ?_) (fun hv hw hlt j' hj' => ?_)
  · rw [hcr, hi1]
    rcases loopSite_cases ent (g % L.block) c'.i with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1, -⟩
    · exact absurd (hsite.trans h1) hn
    all_goals
      have hb := hi'.bound
      exact (h hv).post hold (by omega) j' hj'
  · rw [hld]
    rcases loopSite_cases ent (g % L.block) c'.i with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩
    · rw [hsite] at hw; rw [h1] at hw; cases hw
    · rw [hsite] at hw; rw [h1] at hw; cases hw
    · exact bw_zero (zero_next E ok hv hlt h1) j' hj'

private theorem classes (s : Site) (h : Plain s = false) :
    s = .setMaxReg ∨ s = .bar0 ∨ (∃ j, s = .pre j) ∨ (∃ j, s = .nxt j) ∨ s = .bar21 ∨
      s = .arrive ∨ s = .epilogue := by
  cases s <;> simp_all [Plain]

/-- **A step keeps the bias words.** -/
theorem cur_step {X : Execution} {k : Nat} {old y : Data.D} {e : Event}
    (hB : Lib.BiasEv Q L g X) (E : EntSp Q L g ent) (ok : ent.Ok)
    (he : X.get (g, k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (hf : Fired ent L g old e)
    (pc : e.pc = old.c.site.pc) (hn : succ ent L g old e = some (some y)) (hl : Led X g k old)
    (hi : Control.Inv ent (g % L.block) old.c) (h : CurOk Q L g ent old) :
    CurOk Q L g ent y := by
  obtain ⟨c', hnc, rfl⟩ := succ_inv hn
  have hi' := inv_next hi hnc
  by_cases hp : Plain old.c.site = true
  · obtain ⟨hi1, hp1⟩ := next_plain hp hnc
    obtain ⟨hc, hl'⟩ := rec_keep (L := L) (e := e) (s := c'.site) hp
    exact cur_same hp1 hi1 hc hl' (Plain.post hp) h
  rw [Bool.not_eq_true] at hp
  rcases classes _ hp with hs | hs | ⟨j, hs⟩ | ⟨j, hs⟩ | hs | hs | hs
  · exact cur_vac (Or.inr (Or.inl (next_setMax hs hnc)))
  · -- the barrier before the preloads
    rcases next_bar0 hs hnc with ⟨-, h1⟩ | ⟨hpe, h1⟩
    · exact cur_pre0 (by rw [h1])
    · have hi0 : old.c.i = 0 := hi.init (Or.inr hs)
      have hsite : c'.site = loopSite ent (g % L.block) c'.i := by rw [h1]
      have hci : c'.i = 0 := by rw [h1]; exact hi0
      obtain ⟨hcur, hld⟩ := (rec_bar0 (L := L) (d := old) (e := e) (s := c'.site) hs).1
        (by rw [hsite]; exact loopB_loopSite _ _ _)
      refine cur_loop hsite (fun hv hn j' hj' => ?_) (fun hv hw hlt j' hj' => ?_)
      · rw [hcur, hci]
        rcases loopSite_cases ent (g % L.block) c'.i with ⟨h1, -⟩ | ⟨-, h1⟩ | ⟨-, h1, -⟩
        · exact absurd (hsite.trans h1) hn
        all_goals
          have := zero_first E ok hv (by omega) hpe
          exact bw_zero this j' hj'
      · rw [hld]
        rcases loopSite_cases ent (g % L.block) c'.i with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩
        · rw [hsite, h1] at hw; cases hw
        · rw [hsite, h1] at hw; cases hw
        · exact bw_zero (zero_next E ok hv hlt h1) j' hj'
  · -- a preload
    obtain ⟨a, bs, hk⟩ := bias_kind hf hu (.inl ⟨j, hs⟩)
    have hi0 := (hi.pre j hs).1
    have word := (load_word hB he pc hk hl (j := j)).1 hs hi0
    have hi1 : c'.i = old.c.i := by
      rcases next_pre hs hnc with ⟨_, h1⟩ | ⟨_, h1⟩
      · rw [h1]
      · rw [h1]
    rcases next_pre hs hnc with ⟨hj, h1⟩ | ⟨hj, h1⟩
    · obtain ⟨-, hld⟩ := (rec_pre (L := L) (d := old) (e := e) (s := c'.site) hs hk).2
        (by rw [h1]; simp [loopB])
      intro hv
      refine ⟨fun j2 hj2 j' hj' => ?_, fun hl => by simp [h1, loopLike] at hl,
        fun j2 hj2 => by simp [h1] at hj2, fun hp => by simp [h1, postNxt] at hp⟩
      rw [h1] at hj2
      have e2 : j2 = ⟨j.val + 1, hj⟩ := by simpa using hj2.symm
      subst e2
      rw [hld]
      by_cases hjj : j' = j.val
      · rw [hjj, Function.update_self, word]
      · rw [Function.update_of_ne hjj]
        exact (h hv).pre j hs j' (by simp at hj'; omega)
    · obtain ⟨hcur, hld⟩ := (rec_pre (L := L) (d := old) (e := e) (s := c'.site) hs hk).1
        (by have := loopB_loopSite ent (g % L.block) old.c.i; rw [h1]; exact this)
      have hsite : c'.site = loopSite ent (g % L.block) c'.i := by rw [h1]
      refine cur_loop hsite (fun hv hn j' hj' => ?_) (fun hv hw hlt j' hj' => ?_)
      · rw [hcur, hi1, hi0]
        by_cases hjj : j' = j.val
        · exact .inl (by rw [hjj, Function.update_self, word])
        · exact .inl (by
            rw [Function.update_of_ne hjj]
            exact (h hv).pre j hs j' (by omega))
      · rw [hld]
        rcases loopSite_cases ent (g % L.block) c'.i with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, -, h1⟩
        · rw [hsite, h1] at hw; cases hw
        · rw [hsite, h1] at hw; cases hw
        · exact bw_zero (zero_next E ok hv hlt h1) j' hj'
  · -- a load of the loop
    obtain ⟨a, bs, hk⟩ := bias_kind hf hu (.inr ⟨j, hs⟩)
    have word := (load_word hB he pc hk hl (j := j)).2 hs
    obtain ⟨hcur, hld⟩ := rec_nxt (L := L) (d := old) (e := e) (s := c'.site) hs hk
    have hi1 : c'.i = old.c.i := by
      rcases next_nxt hs hnc with ⟨_, h1⟩ | ⟨_, h1⟩
      · rw [h1]
      · rw [h1]
    have hlp : loopLike old.c.site = true := by simp [hs, loopLike]
    intro hv
    rcases next_nxt hs hnc with ⟨hj, h1⟩ | ⟨hj, h1⟩
    · refine ⟨fun j2 hj2 => by simp [h1] at hj2, fun _ j' hj' => ?_, fun j2 hj2 j' hj' => ?_,
        fun hp => by simp [h1, postNxt] at hp⟩
      · rw [hcur, hi1]
        exact (h hv).cur hlp j' hj'
      · rw [h1] at hj2
        have e2 : j2 = ⟨j.val + 1, hj⟩ := by simpa using hj2.symm
        subst e2
        rw [hld, hi1]
        by_cases hjj : j' = j.val
        · rw [hjj, Function.update_self, word]
        · rw [Function.update_of_ne hjj]
          exact (h hv).nxt j hs j' (by simp at hj'; omega)
    · refine ⟨fun j2 hj2 => by simp [h1] at hj2, fun _ j' hj' => ?_,
        fun j2 hj2 => by simp [h1] at hj2, fun _ hlt j' hj' => ?_⟩
      · rw [hcur, hi1]
        exact (h hv).cur hlp j' hj'
      · rw [hld, hi1]
        by_cases hjj : j' = j.val
        · exact .inl (by rw [hjj, Function.update_self, word])
        · exact .inl (by
            rw [Function.update_of_ne hjj]
            exact (h hv).nxt j hs j' (by omega))
  · -- the end of the round
    rcases next_bar21 hs hnc with h1 | h1
    · obtain ⟨hc, hl'⟩ := (rec_bar21 (L := L) (d := old) (e := e) (s := c'.site)
        (Or.inl hs)).1 (by rw [h1])
      exact cur_same (by rw [h1]; rfl) (by rw [h1]) hc hl' (by simp [hs, postNxt]) h
    · exact cur_adv E ok (Or.inl hs) h1 hi' h (by rw [h1]; exact (loopSite_ne_arrive _ _ _))
  · exact cur_adv E ok (Or.inr hs) (next_arrive hs hnc) hi' h
      (by rw [next_arrive hs hnc]; exact (loopSite_ne_arrive _ _ _))
  · simp [Control.next, hs] at hnc

/-- **The bias words of the value state along the trace**, given the bias loads of the lane. -/
theorem soft_cur {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hB : Lib.BiasEv Q L g X) :
    ∀ k, k ≤ (X.tr g).length → ∀ s, Frame.stateAt (threadD Q L) X g k = some (some s) →
      Frame.NoUbBefore X g k → ∀ w ent y n, s = softDState w ent y n → ent.Ok →
        EntSp Q L g ent → CurOk Q L g ent y := by
  intro k hk s hs nub w ent y n hsd ok E
  obtain ⟨-, -, key⟩ := (soft_ind hp hX (fun ent _ y => EntSp Q L g ent → CurOk Q L g ent y)
    (fun ent _ _ _ _ => cur_vac (Or.inl rfl))
    (fun k ent old y e ok he hu hf pc hn hl hi J E => cur_step hB E ok he hu hf pc hn hl hi (J E))
    k hk s hs nub).2 w ent y n hsd ok
  exact key E

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Soft
