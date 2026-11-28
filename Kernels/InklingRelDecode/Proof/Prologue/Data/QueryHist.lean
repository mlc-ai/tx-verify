-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryAll
public import Kernels.InklingRelDecode.Proof.Lib.QueryCoord

@[expose] public section

/-! # The history of the query halves

A half of the value machine is the zero half or a bf16 number, and every half of a group that is
on and that the site has passed is a number: the load of an on group fires, a group before the
first load or between two loads is off. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow Control

/-- The halves a site has passed: those below a load, all at a store. -/
def qpast : Site → Nat
  | .ldq j => j.val
  | .stq _ _ => 64
  | _ => 0

/-- The x coordinate of the CTA of a thread. -/
abbrev ctaX (L : Launch) (g : Nat) : Nat := (L.ctaidOf (g / L.block)).get .x

/-- The sites that go to the first query site. -/
def entry : Site → Bool
  | .bar2 | .pel _ 3 | .ptc _ 3 => true
  | _ => false

structure QHist (Q : Params) (L : Launch) (g : Nat) (d : D) : Prop where
  half : ∀ j : Fin 64, d.v.q j = .bits 16 0 ∨ ∃ x, d.v.q j = .float .bf16 x
  loaded : ∀ j : Fin 64, j.val < qpast d.c.site → queryOn (g % L.block) (j.val / 16) d.c = true →
    d.v.q j = .float .bf16 (Lib.qElem Q L g j.val)

theorem qHist_init (Q : Params) (L : Launch) (g : Nat) : QHist Q L g {} :=
  ⟨fun _ => .inl rfl, fun _ h _ => absurd h (Nat.not_lt_zero _)⟩

theorem qpast_qSiteAt {n : Nat} (h : n ≤ 64) : qpast (qSiteAt n) = n := by
  unfold qSiteAt
  split_ifs with h1
  · rfl
  · show 64 = n
    omega

theorem qpast_succ : ∀ s : Site, ∀ s' ∈ succs s, qpast s' = 0 ∨ isQ s = true ∨ entry s = true := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

theorem qpast_bare : ∀ s : Site, Bare s → qpast s = 0 := by
  intro s
  cases s <;> repeat' (rename_i j; revert j)
  all_goals decide +kernel

/-- **The first query site** is the first group that is on; the groups before it are off. -/
theorem entry_off {Q L g} {d c : Control.D} {e : Event}
    (hn : Control.next Q L g d e = some (some c)) (he : entry d.site = true) :
    ∀ n : Fin 64, n.val < qpast c.site → queryOn (g % L.block) (n.val / 16) c = false := by
  have key : qpast c.site = 0 ∨ (c.site = querySite (g % L.block) d 0 ∧
      ∀ n, queryOn (g % L.block) n c = queryOn (g % L.block) n d) := by
    cases hs : d.site <;> simp only [entry, hs, reduceCtorEq] at he
    case bar2 =>
      simp only [Control.next, hs, Option.some.injEq] at hn
      rw [← hn]
      split_ifs
      · exact .inr ⟨rfl, fun _ => rfl⟩
      · exact .inl rfl
    case pel b j =>
      fin_cases j <;> try (simp at he; done)
      simp only [Control.next, hs] at hn
      split at hn
      · obtain rfl := Option.some.inj (Option.some.inj hn)
        split_ifs
        · exact .inl rfl
        · rcases afterCopy3 d (g % L.block) (preload Q.splits (ctaX L g) d) b with
        ⟨b', hb', -⟩ | ⟨hq', -, -⟩
          · exact .inl ((congrArg qpast hb').trans rfl)
          · exact .inr ⟨hq', fun _ => rfl⟩
      · cases hn
    case ptc b j =>
      fin_cases j <;> try (simp at he; done)
      simp only [Control.next, hs, Option.some.injEq] at hn
      rw [← hn]
      rcases afterCopy3 d (g % L.block) (preload Q.splits (ctaX L g) d) b with
        ⟨b', hb', -⟩ | ⟨hq', -, -⟩
      · exact .inl ((congrArg qpast hb').trans rfl)
      · exact .inr ⟨hq', fun _ => rfl⟩
  rcases key with h | ⟨hsite, hq⟩
  · exact fun n hn => absurd (h ▸ hn) (Nat.not_lt_zero _)
  · obtain ⟨hi, h64, -, hs, hoff, -⟩ := querySite_spec (g % L.block) d 0 (by omega)
    intro n hn
    rw [hq, hoff n (Nat.zero_le _) ?_]
    rw [hsite, hs, qpast_qSiteAt h64] at hn
    exact hn

theorem isQ_cases : ∀ s, isQ s = true → (∃ j, s = .ldq j) ∨ ∃ i j, s = .stq i j := by
  intro s
  cases s <;> simp [isQ]

theorem record_q {d : D} {e : Event} (h : ∀ j, d.c.site ≠ .ldq j) : (record d e).q = d.v.q := by
  unfold record
  split
  · rfl
  · rename_i heq _
    exact absurd heq (h _)
  · rfl

/-- **The history of the halves is kept by a step.** A query load is on and returns a number. -/
theorem qHist_next {Q L g} {d d' : D} {e : Event} (h : succ Q L g d e = some (some d'))
    (hd : QHist Q L g d)
    (hon : ∀ j, d.c.site = .ldq j → queryOn (g % L.block) (j.val / 16) d.c = true)
    (rd : ∀ j, d.c.site = .ldq j →
      ∃ a bs, e.kind = .rd a bs ∧ rebuild 3 bs = .ok (.float .bf16 (Lib.qElem Q L g j.val))) :
    QHist Q L g d' := by
  obtain ⟨c, hn, rfl⟩ := succ_split h
  by_cases hq : ∃ j, d.c.site = .ldq j
  · obtain ⟨j, hs⟩ := hq
    obtain ⟨a, bs, hk, hx⟩ := rd j hs
    have hrec : record d e =
        ⟨d.v.pay, Function.update d.v.q j (.float .bf16 (Lib.qElem Q L g j.val))⟩ := by
      have : loadVal bs = .float .bf16 (Lib.qElem Q L g j.val) := by
        simp [loadVal, hx, Except.toOption]
      simp [record, hs, hk, this]
    have hcc : c = {d.c with site := afterQuery d.c (g % L.block) j} := by
      simp only [Control.next, hs, Option.some.injEq] at hn
      exact hn.symm
    obtain ⟨hi, h64, hjh, hsite, hoff, -⟩ := after_site d.c (g % L.block) j (hon j hs)
    have hc' : c.site = qSiteAt hi := by rw [hcc]; exact hsite
    rw [hrec]
    refine ⟨fun k => ?_, fun k hk1 hk2 => ?_⟩
    · by_cases hk : k = j
      · subst hk
        exact .inr ⟨Lib.qElem Q L g k.val, by simp⟩
      · simpa [Function.update, hk] using hd.half k
    · change k.val < qpast c.site at hk1
      rw [hc', qpast_qSiteAt h64] at hk1
      by_cases hkj : k = j
      · subst hkj
        simp
      · have ne : j.val ≠ k.val := fun e => hkj (Fin.ext e.symm)
        by_cases hlt : k.val < j.val
        · have hy := hd.loaded k (by rw [hs]; exact hlt) (by rw [hcc] at hk2; exact hk2)
          simpa [Function.update, hkj] using hy
        · have := hoff k.val (by omega) hk1
          have hk2' : queryOn (g % L.block) (k.val / 16) d.c = true := by
            rw [hcc] at hk2
            exact hk2
          rw [this] at hk2'
          exact absurd hk2' (by simp)
  · have hnl : ∀ j, d.c.site ≠ .ldq j := fun j e => hq ⟨j, e⟩
    have hv : (record d e).q = d.v.q := record_q hnl
    refine ⟨fun k => ?_, fun k hk1 hk2 => ?_⟩
    · exact hv ▸ hd.half k
    · show (record d e).q k = _
      rw [hv]
      by_cases hst : ∃ i j, d.c.site = .stq i j
      · obtain ⟨i, j, hs⟩ := hst
        have hcc : c = {d.c with site := Control.afterStore i j} := by
          simp only [Control.next, hs, Option.some.injEq] at hn
          exact hn.symm
        exact hd.loaded k (by rw [hs]; exact k.isLt) (by rw [hcc] at hk2; exact hk2)
      · exfalso
        by_cases hb : Bare d.c.site
        · have := qpast_bare _ (bare_next Q L g hb hn)
          change k.val < qpast c.site at hk1
          omega
        · obtain ⟨hm, -⟩ := next_succ Q L g hb hn
          rcases qpast_succ _ _ hm with h0 | hQ | he
          · change k.val < qpast c.site at hk1
            omega
          · rcases isQ_cases _ hQ with ⟨j, hj⟩ | ⟨i, j, hj⟩
            · exact hnl j hj
            · exact hst ⟨i, j, hj⟩
          · have := entry_off hn he k hk1
            rw [this] at hk2
            exact absurd hk2 (by simp)

/-- **A packed word of a query store** is the pair of the two query elements it packs when its
group is on (the halves of a pair are in one group), and zero otherwise. -/
theorem qw_word {Q L g} {d : D} (hd : QHist Q L g d) {i : Fin 8} {j : Fin 4}
    (hs : d.c.site = .stq i j) (k : Fin 4) :
    (queryOn (g % L.block) (i.val / 2) d.c = true ∧ Tag.val Q L g d (.qw i k) =
      .pair (.float .bf16 (Lib.qElem Q L g (8 * i.val + 2 * k.val)))
        (.float .bf16 (Lib.qElem Q L g (8 * i.val + 2 * k.val + 1)))) ∨
    (queryOn (g % L.block) (i.val / 2) d.c = false ∧ Tag.val Q L g d (.qw i k) = .bits 32 0) := by
  have h0 := i.isLt
  have h1 := k.isLt
  have g1 : (8 * i.val + 2 * k.val + 1) / 16 = (8 * i.val + 2 * k.val) / 16 := by omega
  have g2 : (8 * i.val + 2 * k.val) / 16 = i.val / 2 := by omega
  have lt : ∀ n : Fin 64, n.val < qpast d.c.site := fun n => by rw [hs]; exact n.isLt
  simp only [Tag.val, qv, g1, g2]
  by_cases on : queryOn (g % L.block) (i.val / 2) d.c = true
  · have hx := hd.loaded ⟨8 * i.val + 2 * k.val, by omega⟩ (lt _) (g2 ▸ on)
    have hy := hd.loaded ⟨8 * i.val + 2 * k.val + 1, by omega⟩ (lt _) (g1 ▸ g2 ▸ on)
    refine .inl ⟨on, ?_⟩
    simp only [on, ↓reduceIte, hx, hy]
    rfl
  · refine .inr ⟨Bool.eq_false_iff.mpr on, ?_⟩
    simp only [on, joinValue]
    rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
