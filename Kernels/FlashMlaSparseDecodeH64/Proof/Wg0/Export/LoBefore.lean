-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SegEvent
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.StepInto
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Machine
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SldSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.SldCol
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceBase

@[expose] public section

/-! # The low half is loaded before the peer stores

The events before a peer store `k` of a lane (pc `403 + 10 k`) are the stores `k - 1 .. 0`, the
valid-mask read (pc 289), the fence (287), the load wait (286) and the two score loads
(`w0_lo_before_pst`): the low half's load (pc 280 or 283) is in the block in progress, and it is
the block's last such load, so the block's low words are its words. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.Proof MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

private theorem succOk_vm {c c' : Control.D} (h : succOk c c' = true) (hs : c'.site = .pst 0) :
    c.site = .vm := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem succOk_tcfb {c c' : Control.D} (h : succOk c c' = true) (hs : c'.site = .vm) :
    c.site = .tcfb := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem succOk_sldw {c c' : Control.D} (h : succOk c c' = true) (hs : c'.site = .tcfb) :
    c.site = .sldw := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem succOk_sld1 {c c' : Control.D} (h : succOk c c' = true) (hs : c'.site = .sldw) :
    c.site = .sld false 1 ∨ c.site = .sld true 1 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))

private theorem succOk_sld0t {c c' : Control.D} (h : succOk c c' = true)
    (hs : c'.site = .sld true 1) : c.site = .sld true 0 := by
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := c
  obtain ⟨s', el', a0', l0', l1', cnt', bi', vs', pv', sl', ps', vt'⟩ := c'
  dsimp only at h hs ⊢
  subst hs
  cases s <;> simp [succOk] at h ⊢
  all_goals (try (rename_i k'; fin_cases k' <;> simp at h ⊢))
  all_goals (try simp_all)

/-- **The step into an event, by the sites' successor relation**: the event before an event at a
site `s'` (a pc that names `s'` alone) is at the pc of the site `s` the chain comes from. -/
private theorem w0_prev_gen (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j : Nat} {e' : Event}
    (he' : X.get (g, j + 1) = some e') (hub : ∀ u, e'.kind ≠ .ub u) (hge : 103 ≤ e'.pc) {B : Nat}
    (hB : j + 1 ≤ B)
    (hv0 : W0Valid P.scale ((X.tr g).take B)) {s' : Site} {Q : Nat → Prop}
    (hs' : ∀ x : Site, x.pc = e'.pc → x = s') (hin : innerSite s' = true)
    (hne : s' ≠ .bar0 ∧ s' ≠ .ebar0)
    (hsucc : ∀ c c' : Control.D, succOk c c' = true → c'.site = s' → Q c.site.pc) :
    ∃ f, X.get (g, j) = some f ∧ Q f.pc := by
  obtain ⟨f, c, d, hf, hcpc, hs, hsc, hc⟩ := w0_step_into_hub hp hX hFw hw he' hub hge
    (W0Valid.take_le hv0 hB) hs' hin
  refine ⟨f, hf, ?_⟩
  rcases hc with hc | hc
  · rcases Control.succ_arrS hsc hc with h | h <;> rw [hs] at h
    · exact absurd h hne.1
    · exact absurd h hne.2
  · rw [← hcpc]
    exact hsucc c d.c hc hs


private structure SitePcs (x : Site) : Prop where
  vm : x.pc = 289 → x = .vm
  tcfb : x.pc = 287 → x = .tcfb
  sldw : x.pc = 286 → x = .sldw
  sld1 : x.pc = 285 → x = .sld true 1
  pst0 : x.pc = 403 → x = .pst 0

private theorem site_pcs (x : Site) : SitePcs x := by
  cases x
  all_goals repeat' (rename_i y; fin_cases y)
  all_goals exact ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- **The chain back from the first peer store**: the events before it are the valid-mask read
(pc 289), the fence (287), the load wait (286) and the score loads, the second the low half's
(pc 280, arm 0) or the first (pc 283, arm 1). -/
private theorem back_chain (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4)
    {B j0 : Nat} (hv0 : W0Valid P.scale ((X.tr g).take B)) (hB : j0 ≤ B) {f0 : Event}
    (hf0 : X.get (g, j0) = some f0) (hu0 : ∀ u, f0.kind ≠ .ub u) (hpc0 : f0.pc = 403) :
    ∃ i f, i < j0 ∧ X.get (g, i) = some f ∧ (f.pc = 280 ∨ f.pc = 283) ∧
      ∀ q, i < q → q < j0 → ∃ f', X.get (g, q) = some f' ∧ 283 < f'.pc ∧ f'.pc < 403 := by
  have hnf : ∀ {j : Nat} {f : Event}, X.get (g, j) = some f → (∀ u, f.kind ≠ .ub u) →
      103 ≤ f.pc → f.pc < 1842 → ∃ j', j = j' + 1 := fun {j f} hf hu h1 h2 => by
    cases j with
    | zero => exact (w0_not_first hp hX hFw hf hu ⟨h1, h2⟩).elim
    | succ j' => exact ⟨j', rfl⟩
  obtain ⟨j1, rfl⟩ := hnf hf0 hu0 (by omega) (by omega)
  have hal := noUbBefore_of_get hX hf0
  obtain ⟨f1, hf1, hp1⟩ := Wg0.w0_prev_gen hp hX hFw hw hf0 hu0 (by omega) (by omega) hv0
    (s' := .pst 0) (Q := (· = 289)) (fun x hx => (site_pcs x).pst0 (by omega)) (by decide)
    (by decide) (fun c c' h hs => by rw [Wg0.succOk_vm h hs]; rfl)
  have hu1 : ∀ u, f1.kind ≠ .ub u := hal.ne (Nat.lt_succ_self _) hf1
  obtain ⟨j2, rfl⟩ := hnf hf1 hu1 (by omega) (by omega)
  obtain ⟨f2, hf2, hp2⟩ := Wg0.w0_prev_gen hp hX hFw hw hf1 hu1 (by omega) (by omega) hv0
    (s' := .vm) (Q := (· = 287)) (fun x hx => (site_pcs x).vm (by omega)) (by decide)
    (by decide) (fun c c' h hs => by rw [Wg0.succOk_tcfb h hs]; rfl)
  have hu2 : ∀ u, f2.kind ≠ .ub u := hal.ne (by omega) hf2
  obtain ⟨j3, rfl⟩ := hnf hf2 hu2 (by omega) (by omega)
  obtain ⟨f3, hf3, hp3⟩ := Wg0.w0_prev_gen hp hX hFw hw hf2 hu2 (by omega) (by omega) hv0
    (s' := .tcfb) (Q := (· = 286)) (fun x hx => (site_pcs x).tcfb (by omega)) (by decide)
    (by decide) (fun c c' h hs => by rw [Wg0.succOk_sldw h hs]; rfl)
  have hu3 : ∀ u, f3.kind ≠ .ub u := hal.ne (by omega) hf3
  obtain ⟨j4, rfl⟩ := hnf hf3 hu3 (by omega) (by omega)
  obtain ⟨f4, hf4, hp4⟩ := Wg0.w0_prev_gen hp hX hFw hw hf3 hu3 (by omega) (by omega) hv0
    (s' := .sldw) (Q := fun p => p = 280 ∨ p = 285) (fun x hx => (site_pcs x).sldw (by omega))
    (by decide) (by decide) (fun c c' h hs => by
      rcases Wg0.succOk_sld1 h hs with h | h <;> rw [h] <;> simp [Wg0.Site.pc])
  rcases hp4 with hp4 | hp4
  · refine ⟨j4, f4, by omega, hf4, .inl hp4, fun q h1 h2 => ?_⟩
    have : q = j4 + 1 ∨ q = j4 + 2 ∨ q = j4 + 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact ⟨f3, hf3, by omega, by omega⟩
    · exact ⟨f2, hf2, by omega, by omega⟩
    · exact ⟨f1, hf1, by omega, by omega⟩
  · have hu4 : ∀ u, f4.kind ≠ .ub u := hal.ne (by omega) hf4
    obtain ⟨j5, rfl⟩ := hnf hf4 hu4 (by omega) (by omega)
    obtain ⟨f5, hf5, hp5⟩ := Wg0.w0_prev_gen hp hX hFw hw hf4 hu4 (by omega) (by omega) hv0
      (s' := .sld true 1) (Q := (· = 283)) (fun x hx => (site_pcs x).sld1 (by omega))
      (by decide) (by decide) (fun c c' h hs => by rw [Wg0.succOk_sld0t h hs]; rfl)
    refine ⟨j5, f5, by omega, hf5, .inr hp5, fun q h1 h2 => ?_⟩
    have : q = j5 + 1 ∨ q = j5 + 2 ∨ q = j5 + 3 ∨ q = j5 + 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨f4, hf4, by omega, by omega⟩
    · exact ⟨f3, hf3, by omega, by omega⟩
    · exact ⟨f2, hf2, by omega, by omega⟩
    · exact ⟨f1, hf1, by omega, by omega⟩

/-- **The chain of stores back to the first**: the store `k0` is `k0` events after the store 0,
all the events between at pcs 403 to 473. -/
private theorem pst_chain (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {B : Nat}
    (hv0 : W0Valid P.scale ((X.tr g).take B)) :
    ∀ k0, k0 < 8 → ∀ {j : Nat} {e : Event}, j ≤ B → X.get (g, j) = some e →
      (∀ u, e.kind ≠ .ub u) → e.pc = 403 + 10 * k0 →
      ∃ j0 f0, j0 + k0 = j ∧ X.get (g, j0) = some f0 ∧ f0.pc = 403 ∧
        ∀ q, j0 ≤ q → q ≤ j → ∃ f, X.get (g, q) = some f ∧ 403 ≤ f.pc ∧ f.pc ≤ 473 := by
  intro k0
  induction k0 with
  | zero =>
    intro _ j e _ he _ hpc
    exact ⟨j, e, rfl, he, hpc, fun q h1 h2 => ⟨e, by obtain rfl : q = j := by omega
                                                     exact he, by omega, by omega⟩⟩
  | succ k ih =>
    intro hk j e hjB he hu hpc
    have hnf : ∃ j', j = j' + 1 := by
      cases j with
      | zero => exact (w0_not_first hp hX hFw he hu ⟨by omega, by omega⟩).elim
      | succ j' => exact ⟨j', rfl⟩
    obtain ⟨j', rfl⟩ := hnf
    obtain ⟨f, hf, hpf⟩ := w0_prev_pst hp hX hFw hw (by omega) he hu hpc
      (W0Valid.take_le hv0 (by omega))
    obtain ⟨j0, f0, h1, h2, h3, h4⟩ := ih (by omega) (by omega) hf
      ((noUbBefore_of_get hX he).ne (Nat.lt_succ_self _) hf) hpf
    refine ⟨j0, f0, by omega, h2, h3, fun q hq1 hq2 => ?_⟩
    by_cases hq : q = j' + 1
    · subst hq
      exact ⟨e, he, by omega, by omega⟩
    · exact h4 q hq1 (by omega)

end Wg0

/-- Events after a cut: the block in progress of an extended list. -/
theorem w0Scan_snd_extend (l ex : List Event) (h : ∀ e ∈ ex, e.pc ≠ w0ArrSPc) :
    (w0Scan (l ++ ex)).2 = (w0Scan l).2 ++ ex := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex e ih =>
    rw [← List.append_assoc, w0Scan_snoc]
    have h1 : e.pc ≠ w0ArrSPc := h e (by simp)
    simp only [h1, ite_false]
    rw [ih (fun x hx => h x (by simp [hx])), List.append_assoc]

/-- The last event at pcs of a list with a tail of other pcs. -/
theorem w0Last_append_other {α : Type} (f : Event → Option α) (pcs : List Nat) (seg ex : List Event)
    (h : ∀ e ∈ ex, e.pc ∉ pcs) : w0Last f pcs (seg ++ ex) = w0Last f pcs seg := by
  induction ex using List.reverseRecOn with
  | nil => simp
  | append_singleton ex e ih =>
    rw [← List.append_assoc, Wg0.Data.w0Last_snoc]
    simp only [h e (by simp), ite_false]
    exact ih (fun x hx => h x (by simp [hx]))

/-- **The closed blocks of two prefixes agree** when no event between them closes a block. -/
theorem w0Closed_take_between {i j : Nat} (hij : i ≤ j)
    (h : ∀ q, i ≤ q → q < j → ∃ f, (X.tr g)[q]? = some f ∧ f.pc ≠ w0ArrSPc) :
    w0Closed ((X.tr g).take i) = w0Closed ((X.tr g).take j) := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    obtain ⟨f, hf, hne⟩ := h j hij (by omega)
    rw [ih (fun q h1 h2 => h q h1 (by omega)), List.take_add_one, hf]
    unfold w0Closed
    simp [List.countP_append, hne]

/-- **The low half is loaded before a peer store**: the store `k0` (pc `403 + 10 k0`) at index
`j` has before it, in its block, the low half's load (pc 280 or 283) at index `i`, and the
block's low words at the store are its words. -/
theorem w0_lo_before_pst (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4)
    {j k0 : Nat} {e : Event} (hv0 : W0Valid P.scale ((X.tr g).take j)) (hk0 : k0 < 8)
    (he : X.get (g, j) = some e) (hub : ∀ u, e.kind ≠ .ub u)
    (hpc : e.pc = 403 + 10 * k0) :
    ∃ i a vals sh pc', i < j ∧ X.get (g, i) = some ⟨pc', .tc (.ld a vals sh)⟩ ∧
      (pc' = 280 ∨ pc' = 283) ∧ w0Closed ((X.tr g).take i) = w0Closed ((X.tr g).take j) ∧
      (w0Words (w0Fin ((X.tr g).take j)).2).lo = vals := by
  obtain ⟨j0, f0, hj0, hf0, hp0, hch⟩ := Wg0.pst_chain hp hX hFw hw hv0 k0 hk0 le_rfl he hub hpc
  have hal := noUbBefore_of_get hX he
  have hu0 : ∀ u, f0.kind ≠ .ub u := by
    by_cases hjj : j0 = j
    · subst hjj
      obtain rfl := Option.some.inj (hf0.symm.trans he)
      exact hub
    · exact hal.ne (by omega) hf0
  obtain ⟨i, f, hi0, hfi, hlo, hmid⟩ := Wg0.back_chain hp hX hFw hw hv0 (by omega) hf0 hu0 hp0
  obtain ⟨a, vals, hkind, -, -⟩ := wg0_sldKind hp hX hFw hfi (hal.ne (by omega) hfi) (by omega)
  obtain ⟨pc', kd⟩ := f
  simp only at hkind hlo
  subst hkind
  have hij : i < j := by omega
  have hmid' : ∀ q, i < q → q < j → ∃ f', X.get (g, q) = some f' ∧ 283 < f'.pc ∧ f'.pc < 1122 := by
    intro q h1 h2
    by_cases hq : q < j0
    · obtain ⟨f', hf', h3, h4⟩ := hmid q h1 hq
      exact ⟨f', hf', h3, by omega⟩
    · obtain ⟨f', hf', h3, h4⟩ := hch q (by omega) (by omega)
      exact ⟨f', hf', by omega, by omega⟩
  have hnc : ∀ q, i ≤ q → q < j → ∃ f', (X.tr g)[q]? = some f' ∧ f'.pc ≠ w0ArrSPc := by
    intro q h1 h2
    by_cases hq : q = i
    · subst hq
      exact ⟨_, hfi, by simp only [w0ArrSPc]; omega⟩
    · obtain ⟨f', hf', h3, h4⟩ := hmid' q (by omega) h2
      exact ⟨f', hf', by simp only [w0ArrSPc]; omega⟩
  refine ⟨i, a, vals, .s32x32b, pc', hij, hfi, hlo, w0Closed_take_between hij.le hnc, ?_⟩
  rw [w0Fin_snd]
  have hfi' : (X.tr g)[i]? = some ⟨pc', .tc (.ld a vals .s32x32b)⟩ := hfi
  have hil : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hfi').1
  have hl : i < ((X.tr g).take j).length := by
    simp only [List.length_take]; omega
  have hsplit : (X.tr g).take j = (X.tr g).take i ++ ((X.tr g).take j).drop i := by
    conv_lhs => rw [← List.take_append_drop i ((X.tr g).take j), List.take_take,
      Nat.min_eq_left hij.le]
  have hel : ((X.tr g).take j)[i] = ⟨pc', .tc (.ld a vals .s32x32b)⟩ := by
    have := hfi'
    rw [List.getElem?_eq_getElem hil] at this
    simp only [List.getElem_take]
    exact Option.some.inj this
  have hdrop : ((X.tr g).take j).drop i =
      ⟨pc', .tc (.ld a vals .s32x32b)⟩ :: ((X.tr g).take j).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons hl, hel]
  have hrest : ∀ e' ∈ ((X.tr g).take j).drop (i + 1), e'.pc ≠ w0ArrSPc ∧ 283 < e'.pc := by
    intro e' he'
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he'
    simp only [List.getElem_drop, List.getElem_take] at *
    have hn' : i + 1 + n < j := by simp only [List.length_drop, List.length_take] at hn; omega
    obtain ⟨f', hf', h3, h4⟩ := hmid' (i + 1 + n) (by omega) hn'
    have hf'' : (X.tr g)[i + 1 + n]? = some f' := hf'
    have : f' = (X.tr g)[i + 1 + n]'(List.getElem?_eq_some_iff.mp hf'').1 := by
      rw [List.getElem?_eq_getElem (List.getElem?_eq_some_iff.mp hf'').1] at hf''
      exact (Option.some.inj hf'').symm
    rw [← this]
    exact ⟨by simp only [w0ArrSPc]; omega, h3⟩
  have hall : ∀ e' ∈ ((X.tr g).take j).drop i, e'.pc ≠ w0ArrSPc := by
    intro e' he'
    rw [hdrop] at he'
    rcases List.mem_cons.mp he' with rfl | h
    · simp only [w0ArrSPc]; omega
    · exact (hrest e' h).1
  rw [hsplit, w0Scan_snd_extend _ _ hall, hdrop]
  rw [← List.singleton_append, ← List.append_assoc]
  unfold w0Words
  simp only
  rw [w0Last_append_other _ _ _ _ (fun e' he' => by
    have := (hrest e' he').2
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega), Wg0.Data.w0Last_snoc]
  rcases hlo with rfl | rfl <;> simp [w0TcVals]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
