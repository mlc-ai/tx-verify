-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollSites
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of the correction warps, and their static parts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (allSites mem_allSites)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The static part at a correction site with the scan's ballot `bal`. -/
def corrSiteShape (s : Correction.Site) (bal : BitVec 64) : Sched.CollShape :=
  match s with
  | .pre _ => choiceShape false bal
  | .tiles _ => choiceShape true bal
  | s => pcShape s.pc

/-- **The static part of a collective state of a correction warp.** -/
def corrShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Sched.CollShape :=
  match σ with
  | (.inr ⟨.correction, d⟩, _) => corrSiteShape d.site d.v.sc.bal
  | σ => pcShape ((thread p L g).pc σ)

private def dyn : Correction.Site → Bool
  | .pre _ | .tiles _ => true
  | _ => false

private theorem corr_chk : allSites.all (fun s => siteCk (dyn s) s.wcoll s.pc) = true := by
  decide +kernel

private theorem corr_site (s : Correction.Site) : siteCk (dyn s) s.wcoll s.pc = true :=
  List.all_eq_true.mp corr_chk s (mem_allSites s)

private theorem startAt_site {w : Nat} {s : Startup.D} {n : Cls → Nat} (hS : StartAt L w s n) :
    ∀ r, s.site ≠ .enter r := by
  intro r hr
  simp only [StartAt, hr] at hS

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {w : Nat} (hw8 : 8 ≤ w ∧ w ≤ 11)
  (hw : Prologue.warpIndex L g = w)
include hp hX hFw hub hg hw8 hw

omit hFw hub in
/-- **A state of a correction warp is at a collective exactly at its collective sites.** -/
theorem corr_collAt {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    CollAt p L g σ ↔ corrAt p L g σ = true := by
  have hR := (CorrWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · rw [collAt_of_site (σ := (.inl s, n)) (start_site (startAt_site hR.1))]
    obtain ⟨site, x1, x2, x3⟩ := s
    have hS := hR.1
    cases site <;> simp only [StartAt] at hS <;> simp [startAt, corrAt]
  · exact collAt_of_site (σ := (.inr ⟨.correction, d⟩, n)) (corr_site d.site)

omit hFw in
/-- A collective position of a correction warp is a collective site. -/
theorem corr_isP {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) : corrAt p L g σ = true := by
  obtain ⟨hσ, ⟨e, he, hc⟩ | ⟨rfl, hc⟩⟩ := h
  · rw [← (corr_event_coll hp hX hub hg hw8 hw he hσ).1]; exact hc
  · exact (corr_collAt hp hX hg hw8 hw hσ).mp hc

/-- **The static part of a collective state of a correction warp.** -/
theorem corr_shapeAt {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) :
    Sched.ShapeAt (Progress.timed p L) (corrShape p L) g σ := by
  have hP := corr_isP hp hX hub hg hw8 hw h
  have hσ := h.1
  have hR := (CorrWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · have hst : startAt s.site = true := by
      change (match s.site with | .sh _ => true | _ => false) = true at hP
      revert hP
      cases s.site <;> simp [startAt]
    refine shapeAt_static ?_ rfl
    obtain ⟨-, -, h3, -⟩ := siteCk_ok (start_site (startAt_site hR.1))
    exact (h3 hst).resolve_left (by simp)
  · have hP' : d.site.wcoll = true := hP
    cases hd : dyn d.site with
    | false =>
      obtain ⟨-, -, h3, -⟩ := siteCk_ok (corr_site d.site)
      have hst := (h3 hP').resolve_left (by simp [hd])
      refine shapeAt_static (σ := (.inr ⟨.correction, d⟩, n)) hst ?_
      show corrSiteShape d.site d.v.sc.bal = pcShape d.site.pc
      revert hd
      cases d.site <;> simp [dyn, corrSiteShape]
    | true =>
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hT := table_shape_of hp hFw
      have hck := corr_site d.site
      rw [hd] at hck
      have key : ∀ (tiles l : Bool), d.site = (if tiles then .tiles l else .pre l) →
          Sched.ShapeAt (Progress.timed p L) (corrShape p L) g (.inr ⟨.correction, d⟩, n) := by
        intro tiles l hs
        refine shapeAt_choice (σ := (.inr ⟨.correction, d⟩, n)) (tiles := tiles) (l := l)
          (d := { d.v.sc with site := if tiles then .tiles l else .pre l }) hck rfl ?_ ?_
        · show corrSiteShape d.site d.v.sc.bal = _
          rw [hs]
          cases tiles <;> rfl
        · intro t ins e o hAt hinv hi hf hne
          have h1 := hT.shape g hg _ _ _ _ _ hJ hAt hinv hi hf hne
          have h2 : Correction.Control.Ev p L g d e := h1.1
          have hs0 : d.site = (if tiles then .tiles l else .pre l) := hs
          have hs' : d.scheduler.site = d.site := rfl
          cases tiles <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hs0 ⊢ <;>
            simp only [Correction.Control.Ev, Correction.Ev, hs', hs0,
              Correction.Site.toE] at h2 <;> exact h2
      cases hs : d.site <;> rw [hs] at hd <;> simp only [dyn, Bool.false_eq_true] at hd
      · exact key false _ hs
      · exact key true _ hs

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
