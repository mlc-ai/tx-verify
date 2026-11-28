-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarSite

@[expose] public section

/-! # Warpgroup 0's barrier ordinals

-- domain: consistent

`barOrd_wg0` (the field `barOrdWg0` of `Top.Inputs`, `BarInputs.wg0`): two lanes of one warp of
warpgroup 0 whose barrier events have the same number of barrier events before them are at one
pc. A lane of warps 0–3 passes exactly one barrier event of the startup (below pc 103: at least
one, `bar0_before`; at most one, `bar_first`), and every later barrier event is warpgroup 0's
(`wg0_barRole`) on barriers 9 to 12, counted by the role's ledger; so the count before a barrier
event of warpgroup 0 is one plus the state's ordinal (`Wg0.BarOk`). Both lanes are in one CTA and
so have one block count (`blocksOf`), and a barrier site is fixed by its ordinal
(`Wg0.bar_ord_pc`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A list's barrier events split into those below pc 103 and those of the role. -/
private theorem count_split (l : List Event)
    (h : ∀ f ∈ l, Execution.isBar f = true → f.pc < 103 ∨ Wg0.inRole f = true) :
    l.countP Execution.isBar = l.countP (fun f => Execution.isBar f && decide (f.pc < 103)) +
      l.countP (fun f => Execution.isBar f && Wg0.inRole f) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    simp only [List.countP_cons]
    rw [ih fun f hf => h f (List.mem_cons_of_mem _ hf)]
    cases hb : Execution.isBar f
    · simp
    · have hf := h f List.mem_cons_self hb
      simp only [Wg0.inRole, decide_eq_true_eq] at hf
      simp only [Wg0.inRole]
      rcases hf with hlt | ⟨h1, h2⟩
      · simp [hlt, show ¬ 103 ≤ f.pc by omega]
        omega
      · simp [h1, h2, show ¬ f.pc < 103 by omega]
        omega

/-- A role event's barrier indicator is the sum of its indicators on barriers 9 to 12. -/
private theorem ind_bar (f : Event)
    (h : Execution.isBar f = true → Wg0.inRole f = true →
      ∃ i, Wg0.kindOf f = some (.bar i) ∧ (i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12)) :
    (if (Execution.isBar f && Wg0.inRole f) = true then 1 else 0) =
      Wg0.barTot fun c => if Wg0.cls c f = true then 1 else 0 := by
  obtain ⟨pc, kd⟩ := f
  simp only [Wg0.barTot, Wg0.cls]
  by_cases hr : Wg0.inRole ⟨pc, kd⟩ = true
  swap
  · simp [hr]
  cases kd with
  | bar i c md =>
    obtain ⟨i', hk, hi⟩ := h rfl hr
    simp only [Wg0.kindOf, Option.some.injEq, Wg0.Cnt.bar.injEq] at hk
    subst hk
    rcases hi with rfl | rfl | rfl | rfl <;> simp [Execution.isBar, Wg0.kindOf]
  | wait m q ok a sc => cases ok <;> simp [Execution.isBar, Wg0.kindOf]
  | tc t => cases t <;> simp [Execution.isBar, Wg0.kindOf]
  | _ => simp [Execution.isBar, Wg0.kindOf]

/-- The role's barrier events of a list are its ledger's barrier count. -/
private theorem count_role4 (l : List Event)
    (h : ∀ f ∈ l, Execution.isBar f = true → Wg0.inRole f = true →
      ∃ i, Wg0.kindOf f = some (.bar i) ∧ (i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12)) :
    l.countP (fun f => Execution.isBar f && Wg0.inRole f) =
      Wg0.barTot fun c => l.countP (Wg0.cls c) := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    have h1 := ind_bar f (h f List.mem_cons_self)
    have h2 := ih fun f hf => h f (List.mem_cons_of_mem _ hf)
    simp only [Wg0.barTot, List.countP_cons] at h1 h2 ⊢
    omega

/-- **At most one startup barrier**: a lane's barrier events below pc 103 are at most one. -/
private theorem start_le (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hg : g < L.threads) (k : Nat) :
    ((X.tr g).take k).countP (fun f => Execution.isBar f && decide (f.pc < 103)) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.take_add_one, List.countP_append]
    rcases hk : (X.tr g)[k]? with _ | f
    · simpa using ih
    · have hget : X.get (g, k) = some f := hk
      simp only [Option.toList_some, List.countP_singleton]
      by_cases hb : (Execution.isBar f && decide (f.pc < 103)) = true
      · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
        have h0 := bar_first hp hX hFw hg hget hb.2 hb.1
        have hle : ((X.tr g).take k).countP (fun f => Execution.isBar f && decide (f.pc < 103)) ≤
            ((X.tr g).take k).countP Execution.isBar :=
          List.countP_mono_left fun f _ hf => by simp only [Bool.and_eq_true] at hf; exact hf.1
        simp only [Bool.and_eq_true, decide_eq_true_eq, hb, and_self, ↓reduceIte]
        omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        omega

/-- **The barrier count before a barrier event of warpgroup 0** is one plus the state's
ordinal, at a barrier site of a state with the role's invariants. -/
private theorem bar_count (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (ha : Wg0At L g e.pc) (hb : Execution.isBar e = true) :
    ∃ d : Wg0.Control.D, ∃ n, Wg0.RefCore L g d n ∧ Wg0.LaunchOk P L g d ∧ d.site.isBar = true ∧
      e.pc = d.site.pc ∧ ((X.tr g).take k).countP Execution.isBar = 1 + Wg0.barOrd d := by
  obtain ⟨hw, hr⟩ := ha
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f hk
    simp only at hk
    subst hk
    simp [Execution.isBar] at hb
  obtain ⟨d, hR, ⟨hpc, hk⟩, -⟩ := wg0_at hp hX hFw he hub hr
  obtain ⟨hc, hL, hz, ht⟩ := hR (wg0_take_noUb hX he)
  have hsb : d.site.isBar = true := Wg0.isBar_of_pc ((Wg0.evK_bar hub hk hb).imp
    (fun h => h.1) fun h => h.imp (fun h => h.1) fun h => h.1)
  refine ⟨d, _, hc, hL, hsb, hpc, ?_⟩
  have hrole : ∀ f ∈ (X.tr g).take k, Execution.isBar f = true →
      f.pc < 103 ∨ Wg0.inRole f = true := fun f hf hbf => by
    obtain ⟨j, hj⟩ := get_of_mem_take hf
    exact wg0_barRole hp hX hFw hw hj hbf
  -- the role's barrier events are on barriers 9 to 12
  have hids : ∀ f ∈ (X.tr g).take k, Execution.isBar f = true → Wg0.inRole f = true →
      ∃ i, Wg0.kindOf f = some (.bar i) ∧ (i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12) := by
    intro f hf hbf hrf
    obtain ⟨pc, kd⟩ := f
    cases kd <;> simp only [Execution.isBar, Bool.false_eq_true] at hbf
    rename_i i c md
    refine ⟨i, rfl, ?_⟩
    by_contra hi
    have h0 := hz i (by omega) (by omega) (by omega) (by omega)
    simp only at h0
    have hpos : 0 < ((X.tr g).take k).countP (Wg0.cls (.bar i)) :=
      List.countP_pos_iff.mpr ⟨_, hf, by simp [Wg0.cls, hrf, Wg0.kindOf]⟩
    omega
  -- exactly one startup barrier
  have hst : ((X.tr g).take k).countP (fun f => Execution.isBar f && decide (f.pc < 103)) = 1 := by
    have hle := start_le hp hX hFw (Frame.lt_of_get hX he) k
    have h0 := bar0_before hp hX hFw he hub (by omega)
    have hmono : ((X.tr g).take k).countP isBar0 ≤
        ((X.tr g).take k).countP (fun f => Execution.isBar f && decide (f.pc < 103)) := by
      refine List.countP_mono_left fun f hf hb0 => ?_
      obtain ⟨pc, kd⟩ := f
      cases kd <;> simp only [isBar0, Bool.false_eq_true] at hb0
      rename_i i c md
      have hi : i = 0 := by
        revert hb0
        cases i <;> simp
      subst hi
      rcases hrole _ hf rfl with hlo | hrf
      · simpa [Execution.isBar] using hlo
      · obtain ⟨i, hki, hi⟩ := hids _ hf rfl hrf
        simp only [Wg0.kindOf, Option.some.injEq, Wg0.Cnt.bar.injEq] at hki
        omega
    omega
  rw [count_split _ hrole, hst, count_role4 _ hids, ← ht]

/-- **Lanes of one warp of warpgroup 0 at one barrier ordinal are at one pc**
(`BarInputs.wg0`). -/
theorem barOrd_wg0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g h i j : Nat} {e e' : Event} (hs : SameWarp L g h)
    (he : X.get (g, i) = some e) (he' : X.get (h, j) = some e') (ha : Wg0At L g e.pc)
    (ha' : Wg0At L h e'.pc) (hb : Execution.isBar e = true) (hb' : Execution.isBar e' = true)
    (hc : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    e.pc = e'.pc := by
  obtain ⟨d, n, hJ, hL, hsb, hpc, hcd⟩ := bar_count hp hX hFw he ha hb
  obtain ⟨d', n', hJ', hL', hsb', hpc', hcd'⟩ := bar_count hp hX hFw he' ha' hb'
  obtain ⟨⟨-, -, hcta⟩, -⟩ := hs
  rw [hpc, hpc']
  exact Wg0.bar_ord_pc hcta hsb hJ hL hsb' hJ' hL' (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
