-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiSegs
public import Kernels.InklingRelDecode.Proof.Thread.EpiSteps0

@[expose] public section

/-! # The stores of `LsePart` and `OPart`

The `LsePart` store (`@%p174 st.global.b32`, pc 2682, by the lane whose bit 4 is clear) and the
64 stores of `OPart` (`@%p175 st.global.b32`, pcs `stPc k`, word `k` is the half of product pair
`k / 2`) are event instructions whose guards hold at the sites of the machine (`stLse`, `stO k`:
the row is valid, the lane is the storing lane). A store continues at the next instruction: for an
even word the next store follows at once, after an odd word the unpack of the next pair
(`seg_unpack_facts`), after the last word the barrier. For a lane that does not store `LsePart`
(`%p174` false) the guarded store is skipped; for an invalid row (`%p175` false) every guarded
store is skipped (`seg_skip_from`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {t u : TState} {e : Event} {ins : Instr}

/-- The instruction at `pc` is a global store of one source guarded by `@p`. -/
def storeAt (pc p : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (q, neg), .mem a⟩ =>
    q == p && !neg && a.kind == .store && a.srcs.length == 1 && !(Op.mem a).isLocal
  | _ => false

theorem storeAt_all : ∀ k < 64, storeAt (stPc k) 175 = true := by decide +kernel

theorem storeAt_lse : storeAt 2682 174 = true := by decide +kernel

theorem storeAt_spec {pc p : Nat} (h : storeAt pc p = true) :
    ∃ a : MemAccess, kernel.code[pc]? = some ⟨some (p, false), .mem a⟩ ∧ a.kind = .store ∧
      a.srcs.length = 1 ∧ (Op.mem a).isLocal = false := by
  unfold storeAt at h
  split at h
  · rename_i q neg a hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hq, hn⟩, hk⟩, hl⟩, hloc⟩ := h
    subst hq; subst hn
    exact ⟨a, hc, hk, hl, hloc⟩
  · cases h

/-! ### The facts between the stores -/

theorem st_even_live : ∀ q < 32, ∀ r ∈ Flow.live (2752 + 3 * q), r ∈ Flow.live (2751 + 3 * q) := by
  decide +kernel

theorem st_odd_live : ∀ q < 31, ∀ r ∈ Flow.live (2750 + 3 * (q + 1)),
    r ∈ Flow.live (2752 + 3 * q) := by
  decide +kernel

theorem st_last_live : ∀ r ∈ Flow.live 2846, r ∈ Flow.live 2845 := by decide +kernel

theorem st_guard_live : ∀ k < 64, 175 ∈ Flow.live (stPc k) := by decide +kernel

theorem st_guard_live_lse : 174 ∈ Flow.live 2682 := by decide +kernel

theorem at_cast {t : TState} {pc pc' : Nat} {d : D} (h : At t pc (factsAt pc d)) (e : pc = pc') :
    At t pc' (factsAt pc' d) := e ▸ h

/-- A guarded store of one source continues at the next instruction. -/
theorem store_next {pc p : Nat} {F : List (Nat × Value)} (hs : storeAt pc p = true)
    (hc : kernel.code[pc]? = some ins) (h : At t pc F)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) : u = PTX.next t := by
  obtain ⟨a, hca, hk, hlen, -⟩ := storeAt_spec hs
  obtain rfl := Option.some.inj (hc.symm.trans hca)
  obtain ⟨r, bs, -, hu⟩ := fires_st hk hf
  have hns : ¬ (t.sub + 1 < a.srcs.length) := by omega
  rw [hu, afterStore_last hns]
  obtain ⟨pc0, sub0, acc0, f0, regs0⟩ := t
  obtain ⟨-, hsub, -⟩ := h
  simp only at hsub
  simp [PTX.next, hsub]

/-! ### The steps of the stores of `OPart` -/

theorem inv_stNext {d : D} (hi : Inv d) (hs : ∃ k, d.site = .stO k) (k : Fin 64) :
    Inv (stNext d k) := by
  obtain ⟨k0, hk0⟩ := hs
  have hl : LoadedSite d.site := by rw [hk0]; trivial
  have hr : StoreSite d.site := by rw [hk0]; trivial
  unfold stNext
  split_ifs with hk
  · exact inv_site hi _ (fun _ hsk => hi.len hl hsk) (fun h => by cases h <;> simp_all)
      (fun _ => hi.rv hr) (fun h => by cases h)
  · exact inv_site hi _ (fun h => absurd h (by simp [LoadedSite]))
      (fun h => by rcases h with h | h | h <;> cases h)
      (fun h => absurd h (by simp [StoreSite])) (fun h => by cases h)

/-- **A store of `OPart`**: word `k` is stored; the machine continues at the next store (after
the unpack of the next pair when `k` is odd), or at the barrier after the last. -/
theorem step_stO (k : Fin 64) (pr : Prm) (o : List Value) (sk : Bool)
    (hi : Inv ⟨.stO k, pr, o, sk⟩) (h : At t (Site.stO k).pc (facts ⟨.stO k, pr, o, sk⟩))
    (hc : kernel.code[(Site.stO k).pc]? = some ins)
    (hf : Fires (Site.stO k).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.stO k, pr, o, sk⟩ e u := by
  have hu := store_next (storeAt_all k.val k.isLt) hc h hf
  subst hu
  have hinv := inv_stNext hi ⟨k, rfl⟩ k
  by_cases h63 : k.val + 1 < 64
  · have hd' : stNext (⟨.stO k, pr, o, sk⟩ : D) k = ⟨.stO ⟨k.val + 1, h63⟩, pr, o, sk⟩ := by
      simp [stNext, h63]
    rw [hd'] at hinv
    rcases Nat.even_or_odd' k.val with ⟨q, hq | hq⟩
    · have e1 : stPc k.val = 2751 + 3 * q := by simp [stPc, hq]; omega
      have e2 : stPc (k.val + 1) = 2752 + 3 * q := by simp [stPc, hq]; omega
      refine .inl (.inr ⟨⟨.stO ⟨k.val + 1, h63⟩, pr, o, sk⟩, PTX.next t,
        by simp [next, hd'], .refl, ?_, hinv⟩)
      exact at_next_live (pc := stPc k.val) (pc' := stPc (k.val + 1)) h (by omega) rfl
        (by rw [e1, e2]; exact st_even_live q (by omega))
    · have e1 : stPc k.val = 2752 + 3 * q := by simp [stPc, hq]; omega
      have e2 : stPc (k.val + 1) = 2751 + 3 * (q + 1) := by simp [stPc, hq]; omega
      have hq31 : q < 31 := by omega
      have hs := at_next_live (pc := stPc k.val) (pc' := 2750 + 3 * (q + 1)) h (by omega) rfl
        (d' := (⟨.stO k, pr, o, sk⟩ : D)) (by rw [e1]; exact st_odd_live q hq31)
      obtain ⟨t', hr, ht'⟩ := (seg_unpack_facts (L := L) (g := g)
        (⟨.stO k, pr, o, sk⟩ : D) (q := q + 1) (by omega)).rtg hs
      refine .inl (.inr ⟨⟨.stO ⟨k.val + 1, h63⟩, pr, o, sk⟩, t', by simp [next, hd'], hr, ?_, hinv⟩)
      exact at_cast (d := ⟨.stO ⟨k.val + 1, h63⟩, pr, o, sk⟩) ht' e2.symm
  · have hk : k.val = 63 := by omega
    have hd' : stNext (⟨.stO k, pr, o, sk⟩ : D) k = ⟨.bar1, pr, o, sk⟩ := by simp [stNext, h63]
    rw [hd'] at hinv
    refine .inl (.inr ⟨⟨.bar1, pr, o, sk⟩, PTX.next t, by simp [next, hd'], .refl, ?_, hinv⟩)
    exact at_next_live (pc := stPc k.val) (pc' := 2846) h (by simp [stPc, hk]) rfl
      (by simp only [stPc, hk]; exact st_last_live)

/-! ### The store of `LsePart` -/

/-- **The store of `LsePart`**, then the addresses of the `OPart` words and the unpack of the
first pair, to the first store of `OPart`. -/
theorem step_stLse (pr : Prm) (o : List Value) (sk : Bool) (hi : Inv ⟨.stLse, pr, o, sk⟩)
    (h : At t (Site.stLse).pc (facts ⟨.stLse, pr, o, sk⟩))
    (hc : kernel.code[(Site.stLse).pc]? = some ins)
    (hf : Fires (Site.stLse).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.stLse, pr, o, sk⟩ e u := by
  have hu := store_next storeAt_lse hc h hf
  subst hu
  obtain ⟨t', hr, ht'⟩ := (seg_addr (L := L) (g := g) (⟨.stLse, pr, o, sk⟩ : D) hi.ok).rtg
    (At.next h)
  refine .inl (.inr ⟨⟨.stO 0, pr, o, sk⟩, t', by simp [next], hr, ht', ?_⟩)
  exact inv_site hi _ (fun _ hsk => hi.len trivial hsk) (fun h => by cases h <;> simp_all)
    (fun _ => hi.rv trivial) (fun h => by cases h)

/-! ### Skipping the stores of an invalid row -/

theorem skip_live2 : ∀ q < 32, ∀ r ∈ Flow.live (2753 + 3 * q), r ∈ Flow.live (2752 + 3 * q) := by
  decide +kernel

theorem SegE.cast_end {s b b' : Nat} {F G : List (Nat × Value)} (h : SegE L g s F b G)
    (e : b = b') : SegE L g s F b' G := e ▸ h

/-- Both guarded stores of pair `q` are skipped when `%p175` is false. -/
theorem seg_skip_pair (d : D) (hrv : d.pr.rv = false) {q : Nat} (hq : q < 32) :
    SegE L g (2751 + 3 * q) (factsAt (2751 + 3 * q) d) (2753 + 3 * q)
      (factsAt (2753 + 3 * q) d) := by
  have hv176 : valueOf d 175 = .pred false := by
    have : valueOf d 175 = .pred d.pr.rv := rfl
    rw [this, hrv]
  have e1 : stPc (2 * q) = 2751 + 3 * q := by simp [stPc]; omega
  have e2 : stPc (2 * q + 1) = 2752 + 3 * q := by simp [stPc]; omega
  obtain ⟨a1, hc1, -, -, -⟩ := storeAt_spec (storeAt_all (2 * q) (by omega))
  obtain ⟨a2, hc2, -, -, -⟩ := storeAt_spec (storeAt_all (2 * q + 1) (by omega))
  rw [e1] at hc1
  rw [e2] at hc2
  have m1 : (175, Value.pred false) ∈ factsAt (2751 + 3 * q) d := by
    have := Flow.mem_factsFrom (val := valueOf d) (e1 ▸ st_guard_live (2 * q) (by omega))
    rwa [hv176] at this
  have m2 : (175, Value.pred false) ∈ factsAt (2752 + 3 * q) d := by
    have := Flow.mem_factsFrom (val := valueOf d) (e2 ▸ st_guard_live (2 * q + 1) (by omega))
    rwa [hv176] at this
  refine SegE.comp (p := 2752 + 3 * q) (G := factsAt (2752 + 3 * q) d) ?_ ?_
  · exact ((SegE.of_seg (seg_off (L := L) (g := g) hc1 m1)).weaken_end fun R hR =>
      Flow.holds_factsFrom_mono hR (st_even_live q hq)).cast_end (by omega)
  · exact ((SegE.of_seg (seg_off (L := L) (g := g) hc2 m2)).weaken_end fun R hR =>
      Flow.holds_factsFrom_mono hR (skip_live2 q hq)).cast_end (by omega)

/-- Pair `q` (its two stores and the unpack of the next pair) is skipped. -/
theorem seg_skip_step (d : D) (hrv : d.pr.rv = false) {q : Nat} (hq : q < 31) :
    SegE L g (2751 + 3 * q) (factsAt (2751 + 3 * q) d) (2751 + 3 * (q + 1))
      (factsAt (2751 + 3 * (q + 1)) d) := by
  have hskip := seg_skip_pair (L := L) (g := g) d hrv (q := q) (by omega)
  have e : 2753 + 3 * q = 2750 + 3 * (q + 1) := by omega
  rw [e] at hskip
  exact hskip.comp (seg_unpack_facts d (q := q + 1) (by omega))

/-- **Every guarded store is skipped** for an invalid row: from pair `31 - m` to the barrier. -/
theorem seg_skip_from (d : D) (hrv : d.pr.rv = false) :
    ∀ m, m ≤ 31 → SegE L g (2751 + 3 * (31 - m)) (factsAt (2751 + 3 * (31 - m)) d) 2846
      (factsAt 2846 d) := by
  intro m
  induction m with
  | zero => exact fun _ => seg_skip_pair (L := L) (g := g) d hrv (q := 31) (by omega)
  | succ m ih =>
    intro hm
    have h1 := seg_skip_step (L := L) (g := g) d hrv (q := 31 - (m + 1)) (by omega)
    have e : 31 - (m + 1) + 1 = 31 - m := by omega
    rw [e] at h1
    exact h1.comp (ih (by omega))

/-! ### The wait of the load -/

/-- `%p174` is false where the lane does not store `LsePart` or the row is invalid. -/
theorem p175_off (d : D) (h : (d.pr.lead && d.pr.rv) = false) :
    (174, Value.pred false) ∈ factsAt 2682 d := by
  have hm := Flow.mem_factsFrom (val := valueOf d) st_guard_live_lse
  have : valueOf d 174 = .pred (d.pr.lead && d.pr.rv) := rfl
  rwa [this, h] at hm

/-- The first store of `OPart` is reached from pc 2682 by skipping the `LsePart` store. -/
theorem seg_skipLse (d : D) (hok : d.pr.Ok) (h : (d.pr.lead && d.pr.rv) = false) :
    SegE L g 2682 (factsAt 2682 d) 2751 (factsAt 2751 d) := by
  obtain ⟨a, hc, -, -, -⟩ := storeAt_spec storeAt_lse
  exact (SegE.of_seg (seg_off (L := L) (g := g) hc (p175_off d h))).comp (seg_addr d hok)

/-- **The wait of the load**, then the packs and products and the code to the first store. -/
theorem step_waitLd (pr : Prm) (o : List Value) (sk : Bool) (hi : Inv ⟨.waitLd, pr, o, sk⟩)
    (h : At t (Site.waitLd).pc (facts ⟨.waitLd, pr, o, sk⟩))
    (hc : kernel.code[(Site.waitLd).pc]? = some ins)
    (hf : Fires (Site.waitLd).pc (eventTmpl asms L g t ins.op) e (some u)) :
    Step L g ⟨.waitLd, pr, o, sk⟩ e u := by
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
  obtain rfl := fires_async_next (show AsyncAdvancesOp .tcWaitLd from trivial) hf
  have hsk : sk = false := hi.pre (Or.inr (Or.inr rfl))
  have hpm := pm_run (L := L) (g := g) (t := PTX.next t) (⟨.waitLd, pr, o, sk⟩ : D) hsk
    (At.next h)
  cases hok : (⟨.waitLd, pr, o, sk⟩ : D).loadOk
  · exact .inr ⟨by simp [next, hok], hpm.2 hok⟩
  · obtain ⟨t', hr, ht'⟩ := hpm.1 hok
    obtain ⟨t2, hr2, ht2⟩ := (seg_w4 (L := L) (g := g) (⟨.waitLd, pr, o, sk⟩ : D) hi.ok).rtg ht'
    have hrt1 : Relation.ReflTransGen (Tau kernel asms L g) (PTX.next t) t2 :=
      (run_rtg hr).trans hr2
    have hlen : sk = false → o.length = 64 := hi.len trivial
    cases hrv : pr.rv with
    | false =>
      obtain ⟨t3, hr3, ht3⟩ := (seg_skipLse (L := L) (g := g) (⟨.waitLd, pr, o, sk⟩ : D) hi.ok
        (by simp [hrv])).rtg ht2
      obtain ⟨t4, hr4, ht4⟩ := (seg_skip_from (L := L) (g := g) (⟨.waitLd, pr, o, sk⟩ : D) hrv 31
        (by omega)).rtg ht3
      refine .inl (.inr ⟨⟨.bar1, pr, o, sk⟩, t4, by simp [next, hok, D.stores, hrv],
        hrt1.trans (hr3.trans hr4), ht4, ?_⟩)
      exact inv_site hi _ (fun h => absurd h (by simp [LoadedSite]))
        (fun h => by rcases h with h | h | h <;> cases h)
        (fun h => absurd h (by simp [StoreSite])) (fun h => by cases h)
    | true =>
      cases hl : pr.lead with
      | false =>
        obtain ⟨t3, hr3, ht3⟩ := (seg_skipLse (L := L) (g := g)
          (⟨.waitLd, pr, o, sk⟩ : D) hi.ok (by simp [hl])).rtg ht2
        refine .inl (.inr ⟨⟨.stO 0, pr, o, sk⟩, t3, by simp [next, hok, D.stores, hrv, hl],
          hrt1.trans hr3, ht3, ?_⟩)
        exact inv_site hi _ (fun _ hsk => hlen hsk)
          (fun h => by rcases h with h | h | h <;> cases h) (fun _ => hrv)
          (fun h => by cases h)
      | true =>
        refine .inl (.inr ⟨⟨.stLse, pr, o, sk⟩, t2, by simp [next, hok, D.stores, hrv, hl],
          hrt1, ht2, ?_⟩)
        exact inv_site hi _ (fun _ hsk => hlen hsk)
          (fun h => by rcases h with h | h | h <;> cases h) (fun _ => hrv) (fun _ => hl)

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
