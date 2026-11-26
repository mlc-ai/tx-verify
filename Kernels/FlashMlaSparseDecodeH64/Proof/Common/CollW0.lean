-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollCls
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollW0Seg
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollStep0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollSite
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollIdle
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RegTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View

@[expose] public section

/-! # The collectives of warps 0 to 3: the states and the count

A lane of warps 0 to 3 is in the startup, then in warpgroup 0's machine (`w0_cls`). The
collectives of warp `w` are `collList w`: the startup's, and for the warps 0 and 1 the four
elections of the output chunks. A warpgroup 0 state has made the startup's collectives and the
chunks before its site (`ncT_w0`); a step adds one exactly at an election (`w0_step`), which the
warps 2 and 3 never reach (`w0_noOel`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {x : Nat}

/-- The lanes of warp `w` of CTA `c`. -/
def W0Lane (L : Launch) (w c y : Nat) : Prop := y < L.threads ∧ warpOf L y = w ∧ y / L.block = c

/-- A state of warpgroup 0's machine. -/
abbrev w0S (P : Params) (L : Launch) (x : Nat) (d : Wg0.Control.D) (n : Cls → Nat) :
    (thread P L x).D := (.inr ⟨.inl .wg0, d⟩, n)

/-- The collectives of a warp before warpgroup 0's code. -/
def w0Base (w : Nat) : Nat := if w = 0 then 4 else 2

theorem w0_site_pc (s : Wg0.Site) : 103 ≤ s.pc := by
  rcases wg0_pc s with h | ⟨-, h⟩ <;> omega

theorem ncW_w0 {w pc : Nat} (hw : w < 4) (h : 103 ≤ pc) :
    ncW w pc = w0Base w + if w < 2 then Wg0.segOf pc else 0 := by
  have h6 : 6 < pc := by omega
  have h9 : 9 < pc := by omega
  have h16 : 16 < pc := by omega
  have h31 : 31 < pc := by omega
  interval_cases w <;>
    simp [ncW, collList, w0Base, Wg0.segOf, List.filter_cons, h6, h9, h16, h31] <;>
    split_ifs <;> simp_all

theorem pc_w0 (d : Wg0.Control.D) (n : Cls → Nat) :
    (thread P L x).pc (w0S P L x d n) = d.site.pc := rfl

theorem ncT_w0 (hw : warpOf L x < 4) (d : Wg0.Control.D) (n : Cls → Nat) :
    ncT P L x (w0S P L x d n) =
      w0Base (warpOf L x) + if warpOf L x < 2 then Wg0.segOf d.site.pc else 0 := by
  unfold ncT
  rw [pc_w0]
  exact ncW_w0 hw (w0_site_pc _)

/-- **A state of a lane of warps 0 to 3** is a startup state before its hand-over, or a state of
warpgroup 0's machine. -/
theorem w0_cls (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x < 4) {k : Nat}
    {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    (∃ d n, σ = (.inl d, n) ∧ Startup.RefW L x d (n .shfl) ∧ Startup.exitOf d = none) ∨
      ∃ d n, σ = w0S P L x d n := by
  have hJ := (follow_iff.mp hFw x hx k).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · obtain ⟨-, hW, -⟩ := hJ
    exact .inl ⟨d, n, rfl, hW, by simpa [startupEnter] using glue_gate hσ⟩
  · cases e with
    | wg0 => exact .inr ⟨d, n, rfl⟩
    | dequant | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warpOf, tidOf] at hw
      omega
  · exact hJ.elim

/-- **A step from a startup state into warpgroup 0 lands at its first site.** -/
theorem startup_to_w0 (hp : Pre P L m) (hw : warpOf L x < 4) {d : Startup.D} {n : Cls → Nat}
    {e : Event} {σ' : (thread P L x).D} {d'' : Wg0.Control.D} {n'' : Cls → Nat}
    (hW : Startup.RefW L x d (n .shfl))
    (hn : (thread P L x).next (.inl d, n) e = some (some σ')) (hs' : σ' = w0S P L x d'' n'') :
    d''.site = .smr := by
  rw [next_startup] at hn
  rcases hsu : Startup.succ L x d e with _ | _ | d'
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    subst hn
    by_cases hx' : Startup.exitOf d' = none
    · have hg : Code.gatedExit (startupEnter P L x) (sel P L x) d' = none :=
        Code.gatedExit_none.mpr (by simpa [startupEnter] using hx')
      simp only [Code.enter, hg] at hs'
      cases hs'
    · obtain ⟨hb, hd'⟩ := succ_enter hsu hx'
      have hpc := enter_pc hp hW hb hd' (n' := Code.bump cls n e)
      rw [entry_pc_eq hp] at hpc
      simp only [hw, ↓reduceIte] at hpc
      have h1 := congrArg (thread P L x).pc hs'
      exact wg0_pc103 (h1.symm.trans hpc)

/-- **The elections** are reached by the warps 0 and 1 only: a lane of warps 2 and 3 is at no
election. -/
theorem w0_noOel (hp : Pre P L m)
    (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x < 4) (h2 : 2 ≤ warpOf L x) :
    ∀ k σ, k ≤ (X.tr x).length → Frame.stateAt (thread P L) X x k = some (some σ) →
      ∀ d n, σ = w0S P L x d n → d.site.isOel = false := by
  refine Frame.stateAt_inv (C := thread P L) (X := X) (g := x) (fun k σ =>
    ∀ d n, σ = w0S P L x d n → d.site.isOel = false) ?_ ?_
  · intro d n h
    cases h
  · intro k e s s' he hσ hI hn
    rcases w0_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
    · intro d'' n'' hs'
      rw [startup_to_w0 hp hw hW hn hs']
      rfl
    · intro d'' n'' hs'
      rw [next_frag] at hn
      rcases hsu : (frag P L x .wg0).next d e with _ | _ | d'
      · rw [hsu] at hn; cases hn
      · rw [hsu] at hn; cases hn
      · rw [hsu] at hn
        simp only [Option.map_some, Option.some.injEq] at hn
        subst hn
        simp only [w0S, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
          at hs'
        obtain ⟨rfl, -⟩ := hs'
        by_contra hoel
        have hsu' : Wg0.Control.succ P L x (warpW L x) d e = some (some d') := hsu
        obtain ⟨-, hgt⟩ := Wg0.succ_oel (batch_in hp x) hsu' (by simpa using hoel)
        have : scmpi .gt .s (warpW L x) 1 = true := by
          simp only [warpW]
          generalize hk : warpOf L x = k
          rw [hk] at h2 hw
          interval_cases k <;> decide
        rw [this] at hgt
        cases hgt

theorem w0_pc_coll (s : Wg0.Site) : s.pc ∈ collPcs ↔ s.isOel = true := by
  cases s with
  | sld arm k => cases arm <;> fin_cases k <;> simp [Wg0.Site.pc, collPcs, Wg0.Site.isOel]
  | ost2 c k =>
    fin_cases c <;> fin_cases k <;> simp [Wg0.Site.pc, collPcs, Wg0.Site.isOel, Wg0.ost2Base]
  | pst k | pld k | ost k => fin_cases k <;> simp [Wg0.Site.pc, collPcs, Wg0.Site.isOel]
  | rld c | rldw c | rst c | rstw c | old c | oldw c | ofpx c | obar c | oel c | otma c =>
    fin_cases c <;> simp [Wg0.Site.pc, collPcs, Wg0.Site.isOel]
  | _ => simp [Wg0.Site.pc, collPcs, Wg0.Site.isOel]

/-- A step of warpgroup 0's machine. -/
theorem w0_next {d : Wg0.Control.D} {n : Cls → Nat} {e : Event} {σ' : (thread P L x).D}
    (hn : (thread P L x).next (w0S P L x d n) e = some (some σ')) :
    ∃ d', Wg0.Control.succ P L x (warpW L x) d e = some (some d') ∧
      σ' = w0S P L x d' (Code.bump cls n e) := by
  rw [next_frag] at hn
  rcases hsu : (frag P L x .wg0).next d e with _ | _ | d'
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn; cases hn
  · rw [hsu] at hn
    simp only [Option.map_some, Option.some.injEq] at hn
    exact ⟨d', hsu, hn.symm⟩

theorem gt_warpW (hw : warpOf L x < 12) :
    scmpi .gt .s (warpW L x) 1 = decide (1 < warpOf L x) := by
  simp only [warpW]
  generalize hk : warpOf L x = k
  rw [hk] at hw
  interval_cases k <;> decide

/-- **A step of a lane of warps 0 to 3 keeps the pc count.** -/
theorem w0_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hx : x < L.threads) (hw : warpOf L x < 4)
    {k : Nat} {σ σ' : (thread P L x).D} {e : Event}
    (he : X.get (x, k) = some e) (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hn : (thread P L x).next σ e = some (some σ')) :
    ncT P L x σ' = ncT P L x σ + if (thread P L x).pc σ ∈ collPcs then 1 else 0 := by
  rcases w0_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · exact startup_nc_step hp hX hFw hub hx he hσ hn
  · obtain ⟨d', hsu, rfl⟩ := w0_next hn
    rw [ncT_w0 hw, ncT_w0 hw, pc_w0]
    simp only [w0_pc_coll]
    have hk : k < (X.tr x).length := (List.getElem?_eq_some_iff.mp he).1
    by_cases h2 : 2 ≤ warpOf L x
    · have := w0_noOel hp hFw hx hw h2 k _ hk.le hσ d n rfl
      simp [this, show ¬ warpOf L x < 2 by omega]
    · have hlt : warpOf L x < 2 := by omega
      have hg : scmpi .gt .s (warpW L x) 1 = false := by
        rw [gt_warpW (by omega)]; simpa using hlt
      have hs := Wg0.succ_seg hg (batch_in hp x) hsu
      simp only [hlt, ite_true, Wg0.segOf_site, hs]
      split_ifs <;> omega

theorem collList_sub (w : Nat) : ∀ p ∈ collList w, p ∈ collPcs := by
  unfold collList
  split_ifs <;> decide

/-- **An election state is of the warps 0 and 1.** -/
theorem w0_lt2 (hp : Pre P L m) (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x < 4)
    {k : Nat} {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X x k = some (some (w0S P L x d n)))
    (hc : d.site.isOel = true) : warpOf L x < 2 := by
  obtain ⟨k', hk', hσ'⟩ : ∃ k', k' ≤ (X.tr x).length ∧
      Frame.stateAt (thread P L) X x k' = some (some (w0S P L x d n)) := by
    by_cases hk : k ≤ (X.tr x).length
    · exact ⟨k, hk, hσ⟩
    · exact ⟨(X.tr x).length, le_rfl, by
        rw [← Frame.stateAt_of_le (C := thread P L) (X := X) (g := x) (k := k) (by omega)]
        exact hσ⟩
  by_contra h2
  have := w0_noOel hp hFw hx hw (by omega) k' _ hk' hσ' d n rfl
  rw [this] at hc
  cases hc

/-- **The pc of a collective state of warps 0 to 3 is one of the warp's list.** -/
theorem w0_reach (hp : Pre P L m) (hFw : Follow P L X) (hx : x < L.threads)
    (hw : warpOf L x < 4) {k : Nat} {σ : (thread P L x).D}
    (hσ : Frame.stateAt (thread P L) X x k = some (some σ))
    (hc : (thread P L x).pc σ ∈ collPcs) : (thread P L x).pc σ ∈ collList (warpOf L x) := by
  rcases w0_cls hFw hx hw hσ with ⟨d, n, rfl, hW, -⟩ | ⟨d, n, rfl⟩
  · rw [pc_startup] at hc ⊢
    by_cases h0 : warpOf L x = 0
    · rcases startup_coll_site hW hc with ⟨j, hj⟩ | ⟨j, hj⟩
      · rw [hj, h0]; fin_cases j <;> simp [Startup.Site.pc, collList]
      · rw [hj, h0]; fin_cases j <;> simp [Startup.Site.pc, collList]
    · obtain ⟨j, hj⟩ := sh_site h0 hW hc
      have : ∀ p ∈ ([6, 9] : List Nat), p ∈ collList (warpOf L x) := by
        unfold collList
        split_ifs <;> intro p hp <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢ <;> omega
      rw [hj]; fin_cases j <;> exact this _ (by simp [Startup.Site.pc])
  · rw [pc_w0, w0_pc_coll] at hc
    obtain ⟨c, hc'⟩ : ∃ c, d.site = .oel c := by
      generalize d.site = s at hc
      cases s <;> simp [Wg0.Site.isOel] at hc ⊢
    have hlt : warpOf L x < 2 := w0_lt2 hp hFw hx hw hσ (by rw [hc']; rfl)
    rw [pc_w0, hc']
    rcases (by omega : warpOf L x = 0 ∨ warpOf L x = 1) with h | h <;> rw [h] <;> fin_cases c <;>
      simp [Wg0.Site.pc, collList]

/-- **A state of warps 0 to 3 is at a collective exactly when its pc is the list's entry at its
count.** -/
theorem w0_at (hp : Pre P L m) (hFw : Follow P L X) (hx : x < L.threads) (hw : warpOf L x < 4)
    {k : Nat} {σ : (thread P L x).D} (hσ : Frame.stateAt (thread P L) X x k = some (some σ)) :
    CollAt P L x σ ↔
      (collList (warpOf L x))[ncT P L x σ]? = some ((thread P L x).pc σ) := by
  rw [collAt_iff]
  unfold ncT
  rw [getElem_ncW_coll]
  exact ⟨w0_reach hp hFw hx hw hσ, collList_sub _ _⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
