-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseAddr
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.Correction.Export.FinalStores
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Epilogue.WorkPicked
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive

@[expose] public section

/-! # A correction lane that exits stored its rows' log-sum-exp words

The second pass is entered from the last final arrival or from a log-sum-exp store (`late_prev`).
A lane whose row the request has is not past the row's guard, so it was at the stage's store
(`lse_writes`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

namespace Correction

private theorem late_entries : allSites.all (fun s => (nexts s).all fun s' =>
    !s'.late || s.late || s == .fdone 1 1 || s == .lse 0 || s == .lse 1) = true := by
  decide +kernel

/-- The state before the second pass: after the last final arrival with no row of the lane, or
after a log-sum-exp store. -/
theorem late_prev {d d' : D} {e : Event} (hn : succ p L g d e = some (some d'))
    (hl : d.site.late = false) (hl' : d'.site.late = true) :
    let lim := sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
    (d.site = .fdone 1 1 ∧ scmp .ge .s (rowW L g) lim = true ∧
        scmp .ge .s (rowW L g) (addi lim (-128)) = true) ∨
      (d.site = .lse 0 ∧ scmp .ge .s (rowW L g) (addi lim (-128)) = true) ∨ d.site = .lse 1 := by
  obtain ⟨site, v, kk⟩ := d
  have hsite : site = .fdone 1 1 ∨ site = .lse 0 ∨ site = .lse 1 := by
    rcases succ_cases hn with ⟨rfl, _, _, _, _, hk⟩ | ⟨hf, -, rfl⟩ | hM
    · rw [hl] at hl'; cases hl'
    · simp only at hl hl'
      rw [hl] at hl'; cases hl'
    · have h1 := List.all_eq_true.mp (List.all_eq_true.mp late_entries site
        (mem_allSites _)) d'.site hM.1
      simp only at hl
      simpa [hl, hl', or_assoc] using h1
  rcases hsite with rfl | rfl | rfl
  · left
    simp only [succ] at hn
    split at hn
    swap
    · cases hn
    simp only [Option.some.injEq] at hn
    subst hn
    unfold afterFinal D.ite at hl'
    simp only at hl'
    split at hl'
    · rename_i h1
      split at hl'
      · rename_i h2
        exact ⟨rfl, h1, h2⟩
      · cases hl'
    · cases hl'
  · right; left
    simp only [succ] at hn
    split at hn
    swap
    · cases hn
    simp only [Option.some.injEq] at hn
    subst hn
    unfold afterLse D.ite at hl'
    simp only at hl'
    split at hl'
    · rename_i h2
      exact ⟨rfl, h2⟩
    · cases hl'
  · exact .inr (.inr rfl)

end Correction

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- A lane in the second pass entered it. -/
private theorem corr_entered {i : Nat} : ∀ {d' : Correction.Control.D} {n' : Cls → Nat},
    Frame.stateAt (thread p L) X g i = some (some (CorrWarp.cinj p L g d' n')) → n' .ub = 0 →
    i ≤ (X.tr g).length → d'.site.late = true →
    ∃ k d n e ev a0, X.get (g, k) = some e ∧
      Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)) ∧ n .ub = 0 ∧
      Correction.Control.Ev p L g d e ∧ (∀ f, e.kind ≠ .ub f) ∧ d.site.late = false ∧
      Correction.succ p L g d.scheduler ev = some (some a0) ∧ a0.site.late = true := by
  induction i with
  | zero => intro d' n' hσ; rw [Frame.stateAt_zero] at hσ; cases hσ
  | succ i ih =>
    intro d' n' hσ hub hil hl
    obtain ⟨j, d, n, e, hj, he, hσ0, hub0, ⟨a0, ev, -, -, hn, ha, -⟩, hev, hne⟩ :=
      corr_prev hp hX hFw hw hw1 hσ hub hil (by intro h; rw [h] at hl; cases hl)
    obtain rfl : i = j := by omega
    by_cases hd : d.site.late = true
    · exact ih hσ0 hub0 (by omega) hd
    · exact ⟨i, d, n, e, ev, a0, he, hσ0, hub0, hev, hne, by simpa using hd, hn,
        by rw [ha]; exact hl⟩

/-- **A correction lane that exits stored the log-sum-exp word of its row of each stage**, if the
request of its CTA's work item has the row. -/
theorem lse_writes {b pc : Nat} (hb : b < p.batch) (hlo : tilePrefix p b * p.heads ≤ g / L.block)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) (hh : Fin 2)
    (hrow : 256 * (Epilogue.assignedCoordinates p b (g / L.block)).1 + 128 * hh.val +
      g % L.block % 128 < p.qLength b) (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ j pc a bs, X.get (g, j) = some ⟨pc, .wr a bs⟩ ∧
      a.loc = p.lseLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b
        (g / L.block)).1 + 128 * hh.val + g % L.block % 128))
          (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧ a.size = 4 := by
  have hg := Frame.lt_of_get hX he
  have uniq : ∀ {b'}, tilePrefix p b' * p.heads ≤ g / L.block →
      g / L.block < tilePrefix p (b' + 1) * p.heads → b = b' := by
    intro b' h1 h2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b + 1 ≤ b' by omega))
      omega
    · have := Nat.mul_le_mul_right p.heads (tilePrefix_mono p (show b' + 1 ≤ b by omega))
      omega
  have fitsOf : ∀ {j e} {d : Correction.Control.D} {n : Cls → Nat}, X.get (g, j) = some e →
      (∀ f, e.kind ≠ .ub f) →
      Frame.stateAt (thread p L) X g j = some (some (CorrWarp.cinj p L g d n)) →
      CorrWarp.CFits p L g d (n .shfl) (n .vote) := by
    intro j e d n hj hne hσ
    rcases CorrWarp.open_ev hp hX hFw hw hw1 hj hne with ⟨s, n', hσ', -⟩ |
      ⟨d', n', hσ', h0', hR, -⟩
    · rw [hσ] at hσ'; cases hσ'
    · rw [hσ] at hσ'; cases hσ'
      exact (hR h0').2
  -- the store at its site
  have done : ∀ {j e} {d : Correction.Control.D} {n : Cls → Nat}, X.get (g, j) = some e →
      (∀ f, e.kind ≠ .ub f) → n .ub = 0 →
      Frame.stateAt (thread p L) X g j = some (some (CorrWarp.cinj p L g d n)) →
      Correction.Control.Ev p L g d e → d.site = .lse hh →
      ∃ j pc a bs, X.get (g, j) = some ⟨pc, .wr a bs⟩ ∧
        a.loc = p.lseLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b
          (g / L.block)).1 + 128 * hh.val + g % L.block % 128))
            (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧ a.size = 4 := by
    intro j e d n hj hne h0 hσ hev hs
    obtain ⟨pc, a, bs, rfl⟩ := lse_wr hne hev hs
    obtain ⟨b', hb', hlo', hhi', -, hl, hz⟩ :=
      corr_lse_at hp hX hFw hw hw1 hj hσ h0 (fitsOf hj hne hσ) hs
    obtain rfl := uniq hlo' hhi'
    exact ⟨j, pc, a, bs, hj, hl, hz⟩
  -- the guard of the row is open
  have guard : ∀ {d : Correction.Control.D} {ns nv : Nat}, CorrWarp.CFits p L g d ns nv →
      CorrWarp.epi d.site = .ready 0 →
      scmp .ge .s (Correction.rowW L g) (if hh = 0 then
        sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (Correction.rowOff p L g d.v.sc) 8) else
        addi (sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (Correction.rowOff p L g d.v.sc) 8)) (-128)) =
      false := by
    intro d ns nv hF hep
    obtain ⟨b', hb', hlo', hhi', -, -, -, hlim⟩ := lse_tile hp hg hF hep
    obtain rfl := uniq hlo' hhi'
    exact (lse_guard hp hb hh hlim).mpr hrow
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev, -⟩
  · exfalso
    have hx : exit L g s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
  obtain ⟨l, hs⟩ := corr_exit_site (s := d.site) (v := d.v.scheduler) (k := d.k)
    (hev.data_or_vote.resolve_right (by rintro ⟨_, _, h⟩; cases h))
  have hs : d.site = .exit l := hs
  cases l with
  | false =>
    exfalso
    obtain ⟨rv, -, -, hFE, -⟩ : CorrWarp.CFits p L g d (n .shfl) (n .vote) := (hR h0).2
    exact Epilogue.no_exit_of_work hp hg hb hhi hFE
      (by simp only [show d.scheduler.site = d.site from rfl, hs, CorrWarp.epi])
  | true =>
    obtain ⟨j, d1, n1, e1, ev, a0, hj, hσ1, h1, hev1, hne1, hl1, hn1, hl1'⟩ :=
      corr_entered hp hX hFw hw hw1 hσ h0
        (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1.le (by rw [hs]; rfl)
    have hF1 := fitsOf hj hne1 hσ1
    rcases Correction.late_prev (d := d1.scheduler) hn1 hl1 hl1' with ⟨hs1, g1, g2⟩ |
      ⟨hs1, g2⟩ | hs1
    · -- past both guards
      have hG := guard hF1 (by rw [show d1.site = _ from hs1]; rfl)
      by_cases h : hh = 0
      · rw [ite_eq_left h] at hG
        exact absurd (g1.symm.trans hG) (by decide)
      · rw [ite_eq_right h] at hG
        exact absurd (g2.symm.trans hG) (by decide)
    · by_cases h : hh = 0
      · exact done hj hne1 h1 hσ1 hev1 (h ▸ hs1)
      · have hG := guard hF1 (by rw [show d1.site = _ from hs1]; rfl)
        rw [ite_eq_right h] at hG
        exact absurd (g2.symm.trans hG) (by decide)
    · by_cases h : hh = 0
      · -- the first stage's store comes before the second's
        obtain ⟨i, d0, n0, e0, rfl, he0, hσ0, hub0, ⟨a1, ev1, hev0', -, hn0, ha0, -⟩, hev0, hne0⟩ :=
          corr_prev hp hX hFw hw hw1 hσ1 h1
            (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = _ from hj)).1.le
            (by rw [show d1.site = _ from hs1]; simp)
        obtain ⟨-, -, -, hs0 | ⟨hs0, hg0⟩⟩ := Correction.lse_prev (d := d0.scheduler) (d' := a1)
          (h := 1) hev0' hn0 (ha0.trans hs1)
        · exact done he0 hne0 hub0 hσ0 hev0 (h ▸ hs0)
        · have hG := guard (fitsOf he0 hne0 hσ0) (by rw [show d0.site = _ from hs0]; rfl)
          rw [ite_eq_left h] at hG
          exact absurd ((hg0 (by decide)).symm.trans hG) (by decide)
      · have : hh = 1 := by
          have := hh.isLt
          have : hh.val ≠ 0 := fun h' => h (Fin.ext h')
          exact Fin.ext (by simp only [Fin.isValue, Fin.val_one]; omega)
        exact done hj hne1 h1 hσ1 hev1 (this ▸ hs1)

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
