-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollSites
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of the loader warps, and their static parts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader (AllSites wOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The static part at a loader site with the scan's ballot `bal`. -/
def ldSiteShape (s : Loader.Site) (bal : BitVec 64) : Sched.CollShape :=
  match s with
  | .pre _ => choiceShape false bal
  | .tiles _ => choiceShape true bal
  | s => pcShape s.pc

/-- **The static part of a collective state of a loader warp.** -/
def ldShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Sched.CollShape :=
  match σ with
  | (.inr ⟨.loader _, d⟩, _) => ldSiteShape d.site d.v.sc.bal
  | σ => pcShape ((thread p L g).pc σ)

private def dyn : Loader.Site → Bool
  | .pre _ | .tiles _ => true
  | _ => false

private theorem ld_chk : AllSites fun s => siteCk (dyn s) s.wcoll s.pc = true := by
  unfold AllSites
  decide +kernel

private theorem ld_site (s : Loader.Site) : siteCk (dyn s) s.wcoll s.pc = true := ld_chk.ok s

private theorem startAt_site {w : Nat} {s : Startup.D} {n : Cls → Nat} (hS : StartAt L w s n) :
    ∀ r, s.site ≠ .enter r := by
  intro r hr
  simp only [StartAt, hr] at hS

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {b : Bool} (hw : Prologue.warpIndex L g = wOf b)
include hp hX hFw hub hg hw

omit hFw hub in
/-- **A state of a loader warp is at a collective exactly at its collective sites.** -/
theorem ld_collAt {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    CollAt p L g σ ↔ ldAt p L g σ = true := by
  have hR := (LdWarp.good hp hX Loader.wOf_or hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · rw [collAt_of_site (σ := (.inl s, n)) (start_site (startAt_site hR.1))]
    obtain ⟨site, x1, x2, x3⟩ := s
    have hS := hR.1
    cases site <;> simp only [StartAt] at hS <;> simp [startAt, ldAt]
  · rename_i b'
    exact collAt_of_site (σ := (.inr ⟨.loader b', d⟩, n)) (ld_site d.site)

omit hFw in
/-- A collective position of a loader warp is a collective site. -/
theorem ld_isP {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) : ldAt p L g σ = true := by
  obtain ⟨hσ, ⟨e, he, hc⟩ | ⟨rfl, hc⟩⟩ := h
  · rw [← (ld_event_coll hp hX hub hg (Loader.wb hw) he hσ).1]; exact hc
  · exact (ld_collAt hp hX hg hw hσ).mp hc

/-- **The static part of a collective state of a loader warp.** -/
theorem ld_shapeAt {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) :
    Sched.ShapeAt (Progress.timed p L) (ldShape p L) g σ := by
  have hP := ld_isP hp hX hub hg hw h
  have hσ := h.1
  have hR := (LdWarp.good hp hX Loader.wOf_or hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · have hst : startAt s.site = true := by
      change (match s.site with | .sh _ => true | _ => false) = true at hP
      revert hP
      cases s.site <;> simp [startAt]
    refine shapeAt_static ?_ rfl
    obtain ⟨-, -, h3, -⟩ := siteCk_ok (start_site (startAt_site hR.1))
    exact (h3 hst).resolve_left (by simp)
  · rename_i b'
    have hP' : d.site.wcoll = true := hP
    cases hd : dyn d.site with
    | false =>
      obtain ⟨-, -, h3, -⟩ := siteCk_ok (ld_site d.site)
      have hst := (h3 hP').resolve_left (by simp [hd])
      refine shapeAt_static (σ := (.inr ⟨.loader b', d⟩, n)) hst ?_
      show ldSiteShape d.site d.v.sc.bal = pcShape d.site.pc
      revert hd
      cases d.site <;> simp [dyn, ldSiteShape]
    | true =>
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hT := table_shape_of hp hFw
      have hck := ld_site d.site
      rw [hd] at hck
      have key : ∀ (tiles l : Bool), d.site = (if tiles then .tiles l else .pre l) →
          Sched.ShapeAt (Progress.timed p L) (ldShape p L) g (.inr ⟨.loader b', d⟩, n) := by
        intro tiles l hs
        refine shapeAt_choice (σ := (.inr ⟨.loader b', d⟩, n)) (tiles := tiles) (l := l)
          (d := { d.v.sc with site := if tiles then .tiles l else .pre l }) hck rfl ?_ ?_
        · show ldSiteShape d.site d.v.sc.bal = _
          rw [hs]
          cases tiles <;> rfl
        · intro t ins e o hAt hinv hi hf hne
          have h2 : Loader.Ev p L g (wOf b') d e := hT.shape g hg _ _ _ _ _ hJ hAt hinv hi hf hne
          have hs' : d.site = (if tiles then .tiles l else .pre l) := hs
          cases tiles <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hs' ⊢ <;>
            simp only [Loader.Ev, hs', Loader.Site.toE] at h2 <;> exact h2
      cases hs : d.site <;> rw [hs] at hd <;> simp only [dyn, Bool.false_eq_true] at hd
      · exact key false _ hs
      · exact key true _ hs

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
