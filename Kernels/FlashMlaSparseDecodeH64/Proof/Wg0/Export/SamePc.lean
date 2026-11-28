-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.ValidSnoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Sound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine
import Lemmas.Kernel.SameAccPc

@[expose] public section

/-! # Two elements of one vector access of warpgroup 0 are at one pc

The machine's successor keeps the site while the element is nonzero (`succ_el_pos`), so two
consecutive events of one vector access (`SameAccess`) have one pc (`w0_sameAccess_pc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

namespace Wg0.Control

private theorem succ_el_zero {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {d d' : D}
    {e : Event} (h0 : d.el = 0) (hnv : (∀ k, d.site ≠ .pld k) ∧ (∀ k, d.site ≠ .ost k) ∧
      ∀ c k, d.site ≠ .ost2 c k)
    (h : succ P L g w d e = some (some d')) : d'.el = 0 := by
  obtain ⟨hp, ho, ho2⟩ := hnv
  unfold succ at h
  split at h <;> try first
    | (exfalso; apply hp; assumption)
    | (exfalso; apply ho; assumption)
    | (exfalso; apply ho2; assumption)
  all_goals
    try simp only [afterSmr, afterSink, afterA, finish, loopEntry, advance, afterObar, nextChunk,
      afterEld, ncWord, dataRd, poll, tcLoad] at h
  all_goals repeat' split at h
  all_goals first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; simp [h0])

/-- **A successor with a nonzero element is at the site of its predecessor.** -/
private theorem succ_el_pos {P : Params} {L : Launch} {g : Nat} {w : BitVec 64} {d d' : D}
    {e : Event} (hi : d.el < elems d.site) (h : succ P L g w d e = some (some d'))
    (hne : d'.el ≠ 0) : d'.site = d.site := by
  by_cases hv : (∀ k, d.site ≠ .pld k) ∧ (∀ k, d.site ≠ .ost k) ∧ ∀ c k, d.site ≠ .ost2 c k
  · exfalso
    obtain ⟨hp, ho, ho2⟩ := hv
    have h0 : d.el = 0 := by
      have : elems d.site = 1 := by
        cases hs : d.site <;> simp_all [elems]
      omega
    exact hne (succ_el_zero h0 ⟨hp, ho, ho2⟩ h)
  · have hs : (∃ k, d.site = .pld k) ∨ (∃ k, d.site = .ost k) ∨ ∃ c k, d.site = .ost2 c k := by
      by_contra hc
      apply hv
      refine ⟨fun k hk => hc (.inl ⟨k, hk⟩), fun k hk => hc (.inr (.inl ⟨k, hk⟩)),
        fun c k hk => hc (.inr (.inr ⟨c, k, hk⟩))⟩
    unfold succ at h
    rcases hs with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨c, k, hk⟩
    · rw [hk] at h
      dsimp only at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact hk.symm
        · simp only [Option.some.injEq] at h
          subst h
          exact absurd rfl hne
      · cases h
    · rw [hk] at h
      dsimp only at h
      simp only [Option.some.injEq, elemNext] at h
      split at h
      · subst h
        rfl
      · subst h
        exact absurd rfl hne
    · rw [hk] at h
      dsimp only at h
      simp only [Option.some.injEq, elemNext] at h
      split at h
      · subst h
        rfl
      · subst h
        exact absurd rfl hne


variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Two consecutive events of one vector access of warpgroup 0 are at one pc**: the second is
at a pc of the role's code, and the lane has no undefined behaviour before it. -/
theorem w0_sameAccess_pc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g j : Nat} (hal : LaneUbFree X g (j + 1)) (hw : warp L g < 4)
    {e e' : Event} (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hs : SameAccess X (g, j) (g, j + 1)) (hr : 103 ≤ e'.pc ∧ e'.pc < 1842) :
    e.pc = e'.pc := by
  obtain ⟨a, a', hA, hA', -⟩ := Frame.sameAccess_elem he he' hs
  obtain ⟨σ0, hσ0, -, hi0, -, -⟩ := ev_at hp hX hFw he (Frame.acc_kind_ne_ub hA)
  obtain ⟨σ', hσ', hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he' (Frame.acc_kind_ne_ub hA')
  obtain ⟨d', n', rfl, -, -, -⟩ := wg0_state hJ hi hev hpc hr
  have hg := Frame.lt_of_get hX he'
  have hlen : j + 1 ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he').1.le
  refine Frame.sameAccess_pc (C := thread P L) (fun _ _ => thread_sound hp) hX he he' hs hσ0
    hσ' ?_
  intro hne
  rcases wg0_pred_pre hFw hal hw hg hlen hσ' with ⟨t', ht', d, n, e0, he0, hσ, hS⟩ | hsmr
  · obtain rfl : t' = j := by omega
    rw [hσ] at hσ0
    obtain rfl := Option.some.inj (Option.some.inj hσ0)
    exact (congrArg Site.pc (succ_el_pos hi0 hS hne)).symm.symm
  · exfalso
    have h1 : d'.el < elems d'.site := hi
    rw [hsmr] at h1
    exact hne (by simp [elems] at h1; exact h1)


/-- The pcs of the P tile's stores and of the output staging's stores are quiet. -/
theorem w0Quiet_of_range {f : Event}
    (h : (704 ≤ f.pc ∧ f.pc ≤ 707) ∨ (1331 ≤ f.pc ∧ f.pc ≤ 1338) ∨ (1491 ≤ f.pc ∧ f.pc ≤ 1498) ∨
      (1649 ≤ f.pc ∧ f.pc ≤ 1656) ∨ (1806 ≤ f.pc ∧ f.pc ≤ 1813)) : W0Quiet f := by
  have ho : f.pc ∉ w0OPcs := by
    simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ho⟩, ?_⟩
  all_goals first
    | (intro k hk; omega)
    | (refine ⟨?_, ?_⟩ <;> simp only [w0ArrSPc, w0ArrLPc] <;> omega)
    | (refine ⟨?_, ?_⟩ <;> omega)
    | omega

/-- A site with two or more elements is a peer read's or a quiet one's. -/
private theorem pc_class {f : Event} {s : Site} (h2 : 2 ≤ elems s) (hpc : f.pc = s.pc) :
    (∃ k0, k0 < 8 ∧ f.pc = 477 + 5 * k0) ∨ W0Quiet f := by
  cases s <;> simp only [elems] at h2 <;> try omega
  · rename_i k
    exact Or.inl ⟨k.val, k.2, by rw [hpc]; rfl⟩
  · rename_i k
    refine Or.inr (w0Quiet_of_range (Or.inl ?_))
    simp only [Site.pc] at hpc
    have := k.2
    omega
  · rename_i c k
    have hc : ost2Base c = 1331 ∨ ost2Base c = 1491 ∨ ost2Base c = 1649 ∨ ost2Base c = 1806 := by
      fin_cases c <;> simp [ost2Base]
    have := k.2
    simp only [Site.pc] at hpc
    exact Or.inr (w0Quiet_of_range (by omega))

/-- Quietness depends on the pc only. -/
private theorem quiet_congr {f f' : Event} (h : f.pc = f'.pc) (q : W0Quiet f') : W0Quiet f := by
  obtain ⟨pc, k⟩ := f
  obtain ⟨pc', k'⟩ := f'
  simp only at h
  subst h
  obtain ⟨⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨c8, c9⟩, c10⟩ := q
  exact ⟨⟨c1, c2, c3, c4, c5, c6, c7⟩, ⟨c8, c9⟩, c10⟩

/-- An event outside the role's pcs is quiet. -/
private theorem quiet_of_out {f : Event} (h : ¬ (103 ≤ f.pc ∧ f.pc < 1842)) : W0Quiet f := by
  have ho : f.pc ∉ w0OPcs := by
    simp only [w0OPcs, List.mem_cons, List.not_mem_nil, or_false]; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ho⟩, ?_⟩
  all_goals first
    | (intro k hk; omega)
    | (refine ⟨?_, ?_⟩ <;> simp only [w0ArrSPc, w0ArrLPc] <;> omega)
    | (refine ⟨?_, ?_⟩ <;> omega)
    | omega

/-- **The events of a vector access of warpgroup 0**: two consecutive elements are at one pc,
which is a peer read's or a quiet one (the P tile's and the staging's stores). -/
theorem w0_sameAccess_vec (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g j : Nat} (hal : LaneUbFree X g (j + 1)) (hw : warp L g < 4)
    {e e' : Event} (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hs : SameAccess X (g, j) (g, j + 1)) (hr : 103 ≤ e'.pc ∧ e'.pc < 1842) :
    e.pc = e'.pc ∧ ((∃ k0, k0 < 8 ∧ e'.pc = 477 + 5 * k0) ∨ (W0Quiet e ∧ W0Quiet e')) := by
  have hpc := w0_sameAccess_pc hp hX hFw hal hw he he' hs hr
  refine ⟨hpc, ?_⟩
  obtain ⟨a, a', hA, hA', -⟩ := Frame.sameAccess_elem he he' hs
  obtain ⟨σ', hσ', hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he' (Frame.acc_kind_ne_ub hA')
  obtain ⟨d', n', rfl, -, -, -⟩ := wg0_state hJ hi hev hpc' hr
  have hne : d'.el ≠ 0 :=
    Frame.sameAccess_sub (C := thread P L) (fun _ _ => thread_sound hp) hX he he' hs hσ'
  have h1 : d'.el < elems d'.site := hi
  have h2 : 2 ≤ elems d'.site := by omega
  rcases pc_class h2 (hpc' : e'.pc = Site.pc d'.site) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨quiet_congr hpc h, h⟩

/-- **Two consecutive events of one vector access of warpgroup 0**: the first is at a pc of the
role's code. -/
theorem w0_sameAccess_first (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g j : Nat} {e e' : Event} (he : X.get (g, j) = some e)
    (he' : X.get (g, j + 1) = some e') (hs : SameAccess X (g, j) (g, j + 1))
    (hr : 103 ≤ e.pc ∧ e.pc < 1842) :
    e.pc = e'.pc ∧ ((∃ k0, k0 < 8 ∧ e.pc = 477 + 5 * k0) ∨ W0Quiet e) := by
  obtain ⟨a, a', hA, hA', -⟩ := Frame.sameAccess_elem he he' hs
  obtain ⟨σ0, hσ0, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he (Frame.acc_kind_ne_ub hA)
  obtain ⟨σ', hσ', -, hi', -, hpc'⟩ := ev_at hp hX hFw he' (Frame.acc_kind_ne_ub hA')
  obtain ⟨d, n, rfl, -, -, -⟩ := wg0_state hJ hi hev hpc hr
  have hne := Frame.sameAccess_sub (C := thread P L) (fun _ _ => thread_sound hp) hX he he' hs hσ'
  have hstep := Frame.stateAt_succ (C := thread P L) (X := X) (g := g) (k := j) he
  rw [hσ0, hσ'] at hstep
  have hnx : (thread P L g).next (.inr ⟨.inl .wg0, d⟩, n) e = some (some σ') := hstep.symm
  rw [next_frag] at hnx
  rcases hq : (frag P L g .wg0).next d e with _ | _ | d1 <;> rw [hq] at hnx <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hnx
  subst hnx
  have hq' : succ P L g (warpW L g) d e = some (some d1) := hq
  have hne' : d1.el ≠ 0 := hne
  have hsite := succ_el_pos hi hq' hne'
  have h1 : d1.el < elems d1.site := hi'
  have h2 : 2 ≤ elems d.site := by rw [← hsite]; omega
  have hpe : e.pc = Site.pc d.site := hpc
  refine ⟨?_, pc_class h2 hpe⟩
  have : e'.pc = Site.pc d1.site := hpc'
  rw [this, hsite]; exact hpe

/-- **Two consecutive events of one vector access of warpgroup 0** are at one pc, a peer read's
or a quiet one, or both are at pcs outside the role's code. -/
theorem w0_vec_pair (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g j : Nat} (hal : LaneUbFree X g (j + 1)) (hw : warp L g < 4)
    {e e' : Event} (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hs : SameAccess X (g, j) (g, j + 1)) :
    ((∃ k0, k0 < 8 ∧ e.pc = 477 + 5 * k0 ∧ e'.pc = e.pc) ∨ (W0Quiet e ∧ W0Quiet e')) := by
  by_cases h' : 103 ≤ e'.pc ∧ e'.pc < 1842
  · obtain ⟨hpc, hc⟩ := w0_sameAccess_vec hp hX hFw hal hw he he' hs h'
    rcases hc with ⟨k0, hk0, hk⟩ | ⟨hq, hq'⟩
    · exact Or.inl ⟨k0, hk0, hpc.trans hk, hpc.symm⟩
    · exact Or.inr ⟨hq, hq'⟩
  · by_cases h : 103 ≤ e.pc ∧ e.pc < 1842
    · obtain ⟨hpc, hc⟩ := w0_sameAccess_first hp hX hFw he he' hs h
      rcases hc with ⟨k0, hk0, hk⟩ | hq
      · exact Or.inl ⟨k0, hk0, hk, hpc.symm⟩
      · exact Or.inr ⟨hq, quiet_of_out h'⟩
    · exact Or.inr ⟨quiet_of_out h, quiet_of_out h'⟩

end Wg0.Control

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
