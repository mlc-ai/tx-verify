-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.RefNext

@[expose] public section

/-! # The index warp's reference invariant: the step

`ref_step`, by the site: the set-up's loads keep the zero ring (`body_zero`), the loops' loads,
shuffles, stores and the barrier keep the block (`body_same`, `body_keeps`), the polls and the
arrivals count on the ring (`body_poll`, `body_arrive`, `RefNext.lean`); the loops' counters of
each transition are `RefLoop.lean`'s. -/

/-! # The index warp's stores per block: the steps

`StEq` (`StCount.lean`) is kept by every step of the machine: an event that is no shared write
keeps the count and the state's stores (`stEq_const`, `stEq_ofC`); a coordinate pair's element
counts one store and advances the element (`stEq_pair`); the pair's last element leads to the
validity byte (lanes `0 mod 4`) or the arrival (`stEq_afterPair`); the validity byte leads to the
arrival (`stEq_byte`); the arrival starts the next block with no store made (`stEq_arrive`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The element of a coordinate pair's store is below its two. -/
theorem elems_pair {s : IxSite} (h : s = .stA ∨ s = .stB) : s.elems = 2 := by
  rcases h with rfl | rfl <;> rfl

/-- An event that stores nothing, a state with the same stores and a legal element. -/
theorem stEq_const {d d' : D} {n : Cnt → Nat} {e : Event} {i : Nat}
    (hk : kindOf e ≠ some .st) (h : StEq L g d n i)
    (hd : stDone L g d'.site d'.el = stDone L g d.site d.el) (he : d'.el < d'.site.elems)
    (hb : (d'.site = .bA ∨ d'.site = .bB) → ixSkipB L g = false) :
    StEq L g d' (Code.bump cls n e) i := by
  obtain ⟨h1, -, -⟩ := h
  exact ⟨by rw [bump_eq hk, h1, hd], he, hb⟩

/-- A state at a site's first element before any store of its block, after an event that
stores nothing. -/
theorem stEq_ofC {p : IxSite × IxCtl} {d : D} {n : Cnt → Nat} {e : Event} {i : Nat}
    (hk : kindOf e ≠ some .st) (h : StEq L g d n i) (hd : stDone L g d.site d.el = 0)
    (hz : incW p.1 = 0) : StEq L g (ofC p) (Code.bump cls n e) i := by
  refine stEq_const hk h ?_ (IxSite.elems_pos _) ?_
  · show stDone L g p.1 0 = _
    rw [hd, stDone_incW hz]
  · intro hb
    rcases hb with hb | hb <;> (change p.1 = _ at hb; rw [hb] at hz; exact absurd hz (by decide))

/-- A shared write of a coordinate pair's store: the next element, or the validity byte (lanes
`0 mod 4`) or the arrival. -/
theorem stEq_pair {site : IxSite} {el : Nat} {ac : List Value} {c : IxCtl} {d' : D}
    {n : Cnt → Nat} {e : Event} {i : Nat} {b a : IxSite} (hin : inRole e = true)
    (hk : kindOf e = some .st) (h : StEq L g ⟨site, el, ac, c⟩ n i)
    (hba : site = .stA ∧ b = .bA ∧ a = .arrA ∨ site = .stB ∧ b = .bB ∧ a = .arrB)
    (hs : stNext ⟨site, el, ac, c⟩ (ofC (afterSt L g b a, c)) = d') :
    StEq L g d' (Code.bump cls n e) i := by
  obtain ⟨h1, h2, -⟩ := h
  have hsite : site = .stA ∨ site = .stB := by
    rcases hba with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have he := elems_pair hsite
  simp only [he] at h2
  have hd : ∀ x, stDone L g site x = x := by intro x; rcases hsite with rfl | rfl <;> rfl
  rw [hd] at h1
  unfold stNext at hs
  dsimp only at hs
  split at hs
  · subst hs
    refine ⟨by rw [bump_self hin hk, h1]; dsimp only; rw [hd]; omega, by simp [he]; omega, ?_⟩
    rintro (h | h) <;> (rcases hsite with rfl | rfl <;> simp at h)
  · subst hs
    have hel : el = 1 := by omega
    subst hel
    unfold afterSt
    split
    · rename_i hk2
      have hs0 : sgB L g = 0 := by simp [sgB, hk2]
      rcases hba with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
        refine ⟨by rw [bump_self hin hk, h1]; simp [stDone, hs0], by simp [IxSite.elems],
          by simp⟩
    · rename_i hk2
      rcases hba with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
        refine ⟨by rw [bump_self hin hk, h1]; simp [stDone], by simp [IxSite.elems],
          by simpa using hk2⟩

/-- A quiet event between two sites of one element, with no store made. -/
theorem stEq_site {d : D} {s : IxSite} {n : Cnt → Nat} {e : Event} {i : Nat}
    (hk : kindOf e ≠ some .st) (h : StEq L g d n i) (h1 : d.site.elems = 1) (h2 : 0 < s.elems)
    (hd : stDone L g d.site 0 = 0) (hz : stDone L g s 0 = 0) (hb : s ≠ .bA ∧ s ≠ .bB) :
    StEq L g { d with site := s } (Code.bump cls n e) i := by
  have hel : d.el = 0 := by have := h.2.1; omega
  refine stEq_const hk h ?_ ?_ ?_
  · show stDone L g s d.el = _
    rw [hel, hd, hz]
  · show d.el < s.elems
    rw [hel]; exact h2
  · intro h; simp only at h; rcases h with h | h <;> simp [h] at hb

/-- The validity byte's store leads to the arrival, on a lane that stores the byte. -/
theorem stEq_byte {site : IxSite} {el : Nat} {ac : List Value} {c : IxCtl} {n : Cnt → Nat}
    {e : Event} {i : Nat} {a : IxSite} (hin : inRole e = true) (hk : kindOf e = some .st)
    (h : StEq L g ⟨site, el, ac, c⟩ n i) (hsite : site = .bA ∧ a = .arrA ∨ site = .bB ∧ a = .arrB) :
    StEq L g { (⟨site, el, ac, c⟩ : D) with site := a } (Code.bump cls n e) i := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : ixSkipB L g = false := h3 (by rcases hsite with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp)
  have hs : sgB L g = 1 := by simp [sgB, hb]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hsite
  all_goals
    refine ⟨?_, ?_, by simp⟩
    · rw [bump_self hin hk, h1]; simp [stDone, hs]
    · simp only [IxSite.elems] at h2 ⊢; exact h2

/-- The arrival starts the next block, with no store made. -/
theorem stEq_arrive {site : IxSite} {el : Nat} {ac : List Value} {c : IxCtl} {n : Cnt → Nat}
    {e : Event} {i : Nat} {p : IxSite × IxCtl} (hk : kindOf e ≠ some .st)
    (h : StEq L g ⟨site, el, ac, c⟩ n i) (hsite : site = .arrA ∨ site = .arrB)
    (hz : incW p.1 = 0) : StEq L g (ofC p) (Code.bump cls n e) (i + 1) := by
  obtain ⟨h1, -, -⟩ := h
  have hd : stDone L g site el = 2 + sgB L g := by rcases hsite with rfl | rfl <;> rfl
  refine ⟨?_, IxSite.elems_pos _, ?_⟩
  · rw [bump_eq hk, h1, hd]; show _ = _ + stDone L g p.1 0
    rw [stDone_incW hz]; ring
  · intro hb
    rcases hb with hb | hb <;> (change p.1 = _ at hb; rw [hb] at hz; exact absurd hz (by decide))

/-- A load of an index pair: its next element. -/
theorem stEq_load {site : IxSite} {el : Nat} {ac : List Value} {c : IxCtl} {d' : D}
    {n : Cnt → Nat} {e : Event} {i : Nat} (hk : kindOf e ≠ some .st)
    (h : StEq L g ⟨site, el, ac, c⟩ n i) (hl : isLd site = true) (hs : d'.site = site)
    (he : d'.el = el + 1) (hlt : el + 1 < 2) : StEq L g d' (Code.bump cls n e) i := by
  refine stEq_const hk h ?_ ?_ ?_
  · rw [hs]; cases site <;> simp [isLd] at hl <;> rfl
  · rw [hs, he]; cases site <;> simp [isLd] at hl <;> exact hlt
  · intro hb; rw [hs] at hb; cases site <;> simp [isLd] at hl hb

/-- An element of an index pair: the next element of the same site, or the state `nx`. -/
theorem pair_cases' {d d' : D} {nx : BitVec 64 → BitVec 64 → D} {e : Event}
    (hs : ncPair e d nx = some (some d')) :
    (d'.site = d.site ∧ d'.c = d.c ∧ d'.el = d.el + 1 ∧ d.el + 1 < 2) ∨
      ∃ y0 y1, d' = nx y0 y1 := by
  obtain ⟨y, rfl⟩ := ncPair_some hs
  unfold ldNext; split
  · exact .inl ⟨rfl, rfl, rfl, by assumption⟩
  · exact .inr ⟨_, _, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A set-up result, after a quiet event in block 0. -/
theorem body_zero {p : IxSite × IxCtl} {n : Cnt → Nat} {e : Event} (hz : Zero p)
    (hq : ∀ l, kindOf e ≠ some (.acq l) ∧ kindOf e ≠ some (.arrive l))
    (hc : RingCounts L g n 0 0) (hct : Ctr P L g p.1 p.2 0)
    (hst : StEq L g (ofC p) (Code.bump cls n e) 0) : Body P L g (ofC p) (Code.bump cls n e) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine body_quiet hq (fun _ => rfl) (by show p.2.slot = _; rw [h1]; rfl)
    (by show p.2.par = _; rw [h2]; rfl) ?_ hct hst
  show RingCounts L g n 0 (incW p.1); rw [h3]; exact hc

/-- A loop transition that keeps the ring, after a quiet event in block `i`. -/
theorem body_keeps {c : IxCtl} {p : IxSite × IxCtl} {n : Cnt → Nat} {e : Event} {i : Nat}
    (hk : Keeps c p) (hq : ∀ l, kindOf e ≠ some (.acq l) ∧ kindOf e ≠ some (.arrive l))
    (hsl : c.slot = MbarRow.slot4 i) (hpa : c.par = decide (i / 4 % 2 = 1))
    (hc : RingCounts L g n i 0) (hct : Ctr P L g p.1 p.2 i)
    (hst : StEq L g (ofC p) (Code.bump cls n e) i) : Body P L g (ofC p) (Code.bump cls n e) := by
  obtain ⟨h1, h2, h3, h4⟩ := hk
  refine body_quiet hq (by show preSite p.1 = true → _; simp [h4]) (h1.trans hsl) (h2.trans hpa)
    ?_ hct hst
  show RingCounts L g n i (incW p.1); rw [h3]; exact hc

/-- A state at the same site and words, after a quiet event. -/
theorem body_same {d d' : D} {n : Cnt → Nat} {e : Event} {i : Nat} (hs : d'.site = d.site)
    (hcc : d'.c = d.c) (hq : ∀ l, kindOf e ≠ some (.acq l) ∧ kindOf e ≠ some (.arrive l))
    (hpre : preSite d.site = true → i = 0) (hsl : d.c.slot = MbarRow.slot4 i)
    (hpa : d.c.par = decide (i / 4 % 2 = 1)) (hc : RingCounts L g n i (incW d.site))
    (hct : Ctr P L g d.site d.c i) (hst : StEq L g d' (Code.bump cls n e) i) :
    Body P L g d' (Code.bump cls n e) := by
  refine body_quiet hq (by rw [hs]; exact hpre) (by rw [hcc]; exact hsl) (by rw [hcc]; exact hpa)
    (by rw [hs]; exact hc) (by rw [hs, hcc]; exact hct) hst

/-- A load of an index pair: its next element, or the state `nx`. -/
theorem pair_cases {d d' : D} {nx : BitVec 64 → BitVec 64 → D} {e : Event}
    (hs : ncPair e d nx = some (some d')) :
    d'.site = d.site ∧ d'.c = d.c ∨ ∃ y0 y1, d' = nx y0 y1 := by
  obtain ⟨y, rfl⟩ := ncPair_some hs
  exact ldNext_cases _ _ _

/-- **The invariant is kept by every step** the machine follows. -/
theorem ref_step (hp : Pre P L m) {d d' : D} {n : Cnt → Nat} {e : Event} (hR : Ref P L g d n)
    (hev : Ev P L g d e) (hs : succ P L g d e = some (some d')) :
    Ref P L g d' (Code.bump cls n e) := by
  obtain ⟨site, el, ac, c⟩ := d
  obtain ⟨hpc, hk⟩ := hev
  have hx : site ≠ .exit := by rintro rfl; simp [succ] at hs
  have hin : inRole e = true := by
    have := site_inRole site hx
    simp only [inRole, hpc, decide_eq_true_eq]; exact this
  by_cases hu : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hu; exact ref_ub hin hf
  have hnu : kindOf e ≠ some .ub := by
    unfold kindOf; split <;> simp_all
  intro hu0
  rw [bump_eq hnu] at hu0
  obtain ⟨i, hpre, hsl, hpa, hc, hct, hst⟩ := hR hu0
  dsimp only at hpre hsl hpa hc hct
  obtain ⟨pc, kd⟩ := e
  dsimp only at hk hu hs hin
  cases site with
  | exit => exact absurd rfl hx
  | lenA | lenB =>
    rcases hk with ⟨a, bs, rfl⟩ | ⟨f, rfl⟩
    · simp only [succ, lenNext] at hs
      obtain ⟨x, rfl⟩ := ncNext_some hs
      obtain rfl := hpre rfl
      have h1 : c.slot = 0 := hsl.trans rfl
      have h2 : c.par = false := hpa.trans rfl
      first
        | exact body_zero (zero_afterA P (c := { c with l0 := x }) h1 h2)
            (fun l => by simp [kindOf]) hc (ctr_afterA P _)
            (stEq_ofC (by simp [kindOf]) hst rfl
              (zero_afterA P (c := { c with l0 := x }) h1 h2).2.2)
        | exact body_zero (zero_lens (c := { c with l1 := x }) h1 h2)
            (fun l => by simp [kindOf]) hc (ctr_lens _)
            (stEq_ofC (by simp [kindOf]) hst rfl (zero_lens (c := { c with l1 := x }) h1 h2).2.2)
    · exact absurd ⟨f, rfl⟩ hu
  | pre =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · dsimp only at hk; subst hk
      simp only [succ] at hs
      rcases pair_cases' hs with ⟨h1, h2, h3, h4⟩ | ⟨y0, y1, rfl⟩
      · exact body_same h1 h2 (fun l => by simp [kindOf]) hpre hsl hpa hc hct
          (stEq_load (by simp [kindOf]) hst rfl h1 h3 h4)
      · obtain rfl := hpre rfl
        exact body_zero (zero_afterPre { c with m0 := y0, m1 := y1 }) (fun l => by simp [kindOf])
          hc (ctr_afterPre (c := { c with m0 := y0, m1 := y1 }) hct)
          (stEq_ofC (by simp [kindOf]) hst rfl (zero_afterPre { c with m0 := y0, m1 := y1 }).2.2)
    · exact absurd ⟨f, hk⟩ hu
  | pf | xpf =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · dsimp only at hk; subst hk
      simp only [succ] at hs
      rcases pair_cases' hs with ⟨h1, h2, h3, h4⟩ | ⟨y0, y1, rfl⟩
      · exact body_same h1 h2 (fun l => by simp [kindOf]) hpre hsl hpa hc hct
          (stEq_load (by simp [kindOf]) hst rfl h1 h3 h4)
      · exact body_quiet (fun l => by simp [kindOf]) (by simp [preSite]) hsl hpa hc hct.1
          (stEq_ofC (by simp [kindOf]) hst rfl rfl)
    · exact absurd ⟨f, hk⟩ hu
  | xpre =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · dsimp only at hk; subst hk
      simp only [succ] at hs
      rcases pair_cases' hs with ⟨h1, h2, h3, h4⟩ | ⟨y0, y1, rfl⟩
      · exact body_same h1 h2 (fun l => by simp [kindOf]) hpre hsl hpa hc hct
          (stEq_load (by simp [kindOf]) hst rfl h1 h3 h4)
      · exact body_keeps (keeps_afterXpre { c with e0 := y0, e1 := y1 })
          (fun l => by simp [kindOf]) hsl hpa hc
          (ctr_afterXpre (c := { c with e0 := y0, e1 := y1 }) hct)
          (stEq_ofC (by simp [kindOf]) hst rfl
            (keeps_afterXpre { c with e0 := y0, e1 := y1 }).2.2.1)
    · exact absurd ⟨f, hk⟩ hu
  | wA | wB =>
    rcases hk with ⟨ok, rfl⟩ | ⟨f, rfl⟩
    · simp only [succ, poll, Option.some.injEq] at hs
      subst hs
      cases ok
      · exact body_quiet (fun l => by simp [kindOf]) hpre hsl hpa hc hct
          (stEq_const (by simp [kindOf]) hst rfl hst.2.1 (fun h => hst.2.2 h))
      · refine body_poll hin ?_ rfl hsl hpa rfl hc hct
          (stEq_site (by simp [kindOf]) hst rfl (by decide) rfl rfl (by simp))
        simp only [kindOf, free_loc hp, hsl]
    · exact absurd ⟨f, rfl⟩ hu
  | sA1 | sA2 | sB1 | sB2 =>
    rcases hk with ⟨a, b, c', r, ok, rfl⟩ | ⟨f, rfl⟩
    · simp only [succ] at hs
      obtain ⟨r, rfl⟩ := shflNext_some hs
      exact body_quiet (fun l => by simp [kindOf]) (by simp [preSite]) hsl hpa hc hct
        (stEq_site (by simp [kindOf]) hst rfl (by decide) rfl rfl (by simp))
    · exact absurd ⟨f, rfl⟩ hu
  | stA | stB =>
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    · simp only [succ, Option.some.injEq] at hs
      subst hs
      first
        | have hst' := stEq_pair (b := .bA) (a := .arrA) hin (by simp [kindOf]) hst
            (Or.inl ⟨rfl, rfl, rfl⟩) rfl
        | have hst' := stEq_pair (b := .bB) (a := .arrB) hin (by simp [kindOf]) hst
            (Or.inr ⟨rfl, rfl, rfl⟩) rfl
      rcases stNext_cases ⟨_, el, ac, c⟩ (ofC (afterSt L g _ _, c)) with ⟨h1, h2⟩ | h
      · exact body_same h1 h2 (fun l => by simp [kindOf]) hpre hsl hpa hc hct hst'
      · rw [h] at hst'
        rw [h]
        have hcs : ∀ b a : IxSite, Ctr P L g b c i → Ctr P L g a c i →
            Ctr P L g (afterSt L g b a) c i :=
          fun b a h1 h2 => by
            rcases afterSt_cases (L := L) (g := g) b a with h' | h' <;> rw [h'] <;> assumption
        have hr : ∀ b a : IxSite, incW b = 1 → incW a = 1 → preSite b = false →
            preSite a = false → incW (afterSt L g b a) = 1 ∧ preSite (afterSt L g b a) = false :=
          fun b a h1 h2 h3 h4 => by
            rcases afterSt_cases (L := L) (g := g) b a with h' | h' <;> rw [h'] <;> simp [*]
        first
          | obtain ⟨hw, hpr⟩ := hr .bA .arrA rfl rfl rfl rfl
            exact body_quiet (fun l => by simp [kindOf]) (by simp [hpr]) hsl hpa
              (by show RingCounts L g n i (incW (afterSt L g .bA .arrA)); rw [hw]; exact hc)
              (hcs .bA .arrA hct hct) hst'
          | obtain ⟨hw, hpr⟩ := hr .bB .arrB rfl rfl rfl rfl
            exact body_quiet (fun l => by simp [kindOf]) (by simp [hpr]) hsl hpa
              (by show RingCounts L g n i (incW (afterSt L g .bB .arrB)); rw [hw]; exact hc)
              (hcs .bB .arrB hct hct) hst'
    · exact absurd ⟨f, rfl⟩ hu
  | bA | bB =>
    rcases hk with ⟨a, bs, rfl, -⟩ | ⟨f, rfl⟩
    · simp only [succ, Option.some.injEq] at hs
      subst hs
      exact body_quiet (fun l => by simp [kindOf]) (by simp [preSite]) hsl hpa hc hct
        (stEq_byte hin (by simp [kindOf]) hst
          (by first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩))
    · exact absurd ⟨f, rfl⟩ hu
  | arrA =>
    simp only [EvK] at hk
    subst hk
    simp only [succ, Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := keeps_mainEnd c
    refine body_arrive hin ?_ h4 ?_ ?_ h3 hc (ctr_mainEnd hct)
      (stEq_arrive (by simp [kindOf]) hst (Or.inl rfl) h3)
    · simp only [kindOf, ready_loc hp, hsl]
    · exact h1.trans (by show c.slot + 1 = _; rw [hsl, slot_succ])
    · exact h2.trans (by show ixParNext c.par c.slot = _; rw [hpa, hsl, par_succ])
  | arrB =>
    simp only [EvK] at hk
    subst hk
    simp only [succ, Option.some.injEq] at hs
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := keeps_xEnd c
    refine body_arrive hin ?_ h4 ?_ ?_ h3 hc (ctr_xEnd hct)
      (stEq_arrive (by simp [kindOf]) hst (Or.inr rfl) h3)
    · simp only [kindOf, ready_loc hp, hsl]
    · exact h1.trans (by show c.slot + 1 = _; rw [hsl, slot_succ])
    · exact h2.trans (by show ixParNext c.par c.slot = _; rw [hpa, hsl, par_succ])
  | bar =>
    simp only [EvK] at hk
    subst hk
    simp only [succ, Option.some.injEq] at hs
    subst hs
    exact body_quiet (fun l => by simp [kindOf]) (by simp [preSite]) hsl hpa hc hct
      (stEq_site (by simp [kindOf]) hst rfl (by decide) rfl rfl (by simp))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
