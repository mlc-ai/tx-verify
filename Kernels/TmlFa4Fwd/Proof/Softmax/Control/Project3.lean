-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.ProjectStep

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

theorem project_pwst {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0 x1, Projects (p := p) (L := L) (g := g) ⟨.pwst x0 x1,v,k, acc⟩ := by
  intro x0 x1
  project_step

theorem project_parr {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.parr x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_pws {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.pws x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_pel {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.pel x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_parr2 {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.parr2 x0,v,k, acc⟩ := by
  intro x0
  project_step

private theorem erase_branch (b : Bool) (u v : Softmax.D) :
    erase (Softmax.D.ite b u v) = if b then erase u else erase v := by
  cases b <;> rfl

private theorem erase_round {p L g} (d : Softmax.D) (r : Rd) :
    erase (afterRound p L g (erase d).scheduler r) = erase (afterRound p L g d r) := by
  obtain ⟨s,v,k,acc⟩ := d
  cases r <;> simp only [afterRound, afterFirst, afterPlain, afterBias, plainEntry,
      erase_branch] <;> rfl

theorem project_pwend {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) (r : Rd) :
    Projects (p := p) (L := L) (g := g) ⟨.pwend r,v,k, acc⟩ := by
  intro e a h
  generalize hd : (⟨.pwend r,v,k,acc⟩ : Softmax.D) = d at *
  have hs : d.site = .pwend r := hd ▸ rfl
  have he : ∃ m q ok ac sc, e.kind = .wait m q ok ac sc := by
    simp only [Softmax.succ, hs] at h
    split at h
    · exact ⟨_, _, _, _, _, ‹_›⟩
    · cases h
  obtain ⟨m,q,ok,ac,sc,he⟩ := he
  subst d
  cases ok <;> simp only [Softmax.succ, he, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
  all_goals subst a
  · simp only [succ, erase, D.scheduler, Softmax.succ, he, Bool.false_eq_true, ↓reduceIte,
      Option.map_some]; rfl
  · simpa only [succ, erase, D.scheduler, Softmax.succ, he, ↓reduceIte, Option.map_some,
      Option.some.injEq] using (erase_round (p := p) (L := L) (g := g) ⟨.pwend r,v,k,acc⟩ r)

theorem project_fin {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    ∀ x0, Projects (p := p) (L := L) (g := g) ⟨.fin x0,v,k, acc⟩ := by
  intro x0
  project_step

theorem project_finarr {p L g} (v : Softmax.V) (k : Fin 4) (acc : List Value) :
    Projects (p := p) (L := L) (g := g) ⟨.finarr,v,k, acc⟩ := by
  project_step

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
