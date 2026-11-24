-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.CollSites
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Top.Table
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The collective sites of the softmax warps, and their static parts -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (allSites mem_allSites)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The static part at a softmax site with the scan's ballot `bal`. -/
def softSiteShape (s : Softmax.Site) (bal : BitVec 64) : Sched.CollShape :=
  match s with
  | .pre _ => choiceShape false bal
  | .tiles _ => choiceShape true bal
  | s => pcShape s.pc

/-- **The static part of a collective state of a softmax warp.** -/
def softShape (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Sched.CollShape :=
  match σ with
  | (.inr ⟨.softmax, d⟩, _) => softSiteShape d.site d.v.sc.bal
  | σ => pcShape ((thread p L g).pc σ)

private def dyn : Softmax.Site → Bool
  | .pre _ | .tiles _ => true
  | _ => false

private theorem soft_chk : allSites.all (fun s => siteCk (dyn s) s.wcoll s.pc) = true := by
  decide +kernel

private theorem soft_site (s : Softmax.Site) : siteCk (dyn s) s.wcoll s.pc = true :=
  List.all_eq_true.mp soft_chk s (mem_allSites s)

theorem startW_site {w : Nat} {s : Startup.D} {n : Cls → Nat} (hS : SmWarp.StartW L w s n) :
    ∀ r, s.site ≠ .enter r := by
  intro r hr
  simp only [SmWarp.StartW, StartAt0, StartAt, hr, ite_self] at hS

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {w : Nat} (hw8 : w < 8)
  (hw : Prologue.warpIndex L g = w)
include hp hX hFw hub hg hw8 hw

omit hFw hub in
/-- **A state of a softmax warp is at a collective exactly at its collective sites.** -/
theorem soft_collAt {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    CollAt p L g σ ↔ softAt p L g σ = true := by
  have hR := (SmWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · rw [collAt_of_site (σ := (.inl s, n)) (start_site (startW_site hR.1))]
    show _ ↔ (match s.site with | .sh _ | .elect _ => true | _ => false) = true
    cases s.site <;> simp [startAt]
  · exact collAt_of_site (σ := (.inr ⟨.softmax, d⟩, n)) (soft_site d.site)

omit hFw in
/-- A collective position of a softmax warp is a collective site. -/
theorem soft_isP {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) : softAt p L g σ = true := by
  obtain ⟨hσ, ⟨e, he, hc⟩ | ⟨rfl, hc⟩⟩ := h
  · rw [← (soft_event_coll hp hX hub hg hw8 hw he hσ).1]; exact hc
  · exact (soft_collAt hp hX hg hw8 hw hσ).mp hc

/-- **The static part of a collective state of a softmax warp.** -/
theorem soft_shapeAt {k : Nat} {σ : (thread p L g).D}
    (h : Sched.CollPos (Progress.timed p L) X (CollAt p L) g k σ) :
    Sched.ShapeAt (Progress.timed p L) (softShape p L) g σ := by
  have hP := soft_isP hp hX hub hg hw8 hw h
  have hσ := h.1
  have hR := (SmWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · have hst : startAt s.site = true := by
      change (match s.site with | .sh _ | .elect _ => true | _ => false) = true at hP
      revert hP
      cases s.site <;> simp [startAt]
    refine shapeAt_static ?_ rfl
    obtain ⟨-, -, h3, -⟩ := siteCk_ok (start_site (startW_site hR.1))
    exact (h3 hst).resolve_left (by simp)
  · have hP' : d.site.wcoll = true := hP
    cases hd : dyn d.site with
    | false =>
      obtain ⟨-, -, h3, -⟩ := siteCk_ok (soft_site d.site)
      have hst := (h3 hP').resolve_left (by simp [hd])
      refine shapeAt_static (σ := (.inr ⟨.softmax, d⟩, n)) hst ?_
      show softSiteShape d.site d.v.sc.bal = pcShape d.site.pc
      revert hd
      cases d.site <;> simp [dyn, softSiteShape]
    | true =>
      have hJ := (goodR hp hX hFw hg k).2 _ hσ
      have hT := table_shape_of hp hFw
      have hck := soft_site d.site
      rw [hd] at hck
      have key : ∀ (tiles l : Bool), d.site = (if tiles then .tiles l else .pre l) →
          Sched.ShapeAt (Progress.timed p L) (softShape p L) g (.inr ⟨.softmax, d⟩, n) := by
        intro tiles l hs
        refine shapeAt_choice (σ := (.inr ⟨.softmax, d⟩, n)) (tiles := tiles) (l := l)
          (d := { d.v.sc with site := if tiles then .tiles l else .pre l }) hck rfl ?_ ?_
        · show softSiteShape d.site d.v.sc.bal = _
          rw [hs]
          cases tiles <;> rfl
        · intro t ins e o hAt hinv hi hf hne
          have h1 : Softmax.EvS p L g d.scheduler e :=
            hT.shape g hg _ _ _ _ _ hJ hAt hinv hi hf hne
          have h2 := h1.1
          have hs' : d.scheduler.site = (if tiles then .tiles l else .pre l) := hs
          cases tiles <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hs' ⊢ <;>
            simp only [Softmax.Ev, hs', Softmax.Site.toE] at h2 <;> exact h2
      cases hs : d.site <;> rw [hs] at hd <;> simp only [dyn, Bool.false_eq_true] at hd
      · exact key false _ hs
      · exact key true _ hs

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Top
