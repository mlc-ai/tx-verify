-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
public import Lemmas.Flow.AdvanceU
public import Lemmas.Flow.CtlStepsU
public import Lemmas.Flow.Step.SiteCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

/-- A site in the loop body with no lane or bias guard. -/
def SiteBody (s : Site) : Bool :=
  match s with
  | .epilogue | .setMaxReg | .bar0 | .pre _ | .nxt _ | .arrive => false
  | _ => true

theorem Inv.iter_lt {e t s i v} (hi : Inv e t ⟨s,i,v⟩) (hs : SiteBody s) : i < e.limit := by
  apply hi.loop
  · rintro h; change s = _ at h; subst s; cases hs
  · rintro h; change s = _ at h; subst s; cases hs
  · rintro h; change s = _ at h; subst s; cases hs
  · rintro j h; change s = _ at h; subst s; cases hs

theorem body_inv {e t s s' i v v'} (hi : Inv e t ⟨s,i,v⟩) (hs : SiteBody s)
    (hs' : SiteBody s') : Inv e t ⟨s',i,v'⟩ := by
  refine ⟨hi.entry,hi.thread,hi.bound,?_,?_,?_,?_,fun _ _ _ _ => hi.iter_lt hs⟩
  · rintro (rfl | rfl) <;> cases hs'
  · rintro _ rfl; cases hs'
  · rintro _ rfl; cases hs'
  · rintro rfl; cases hs'

theorem step_of_inv {e L g d} (h : Inv e (g % L.block) d → (code e L g).StepAtU d) :
    (code e L g).StepAtU d :=
  ⟨fun hi => (h hi).site hi,fun ins ht hi => (h hi).step ins ht hi⟩

/-- The successor has the same register table when only the site changes. -/
theorem project {L g e i v s s' p q} (h : ∀ r ∈ ctlLive q, r ∈ ctlLive p) :
    ∀ a ∈ facts e L g ⟨s',i,v⟩ q, a ∈ facts e L g ⟨s,i,v⟩ p := by
  intro a ha
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp ha
  exact mem_factsFrom (val := valueOf e L g ⟨s,i,v⟩) (h r hr)

theorem project_seg {L g e i v s s' p q} (h : ∀ r ∈ ctlLive q, r ∈ ctlLive p) :
    SegU kernel Assumptions.all L g q (facts e L g ⟨s,i,v⟩ p) q (facts e L g ⟨s',i,v⟩ q) :=
  fun t ht => by
    have ⟨_,_,_,_,hr⟩ := ht
    exact .inl ⟨t,.refl,ht.mono (holds_factsFrom_mono hr h)⟩

theorem carry_seg {L g e i v} {s s' : Site} {start stop}
    (sub : ∀ r ∈ ctlLive stop, r ∈ ctlLive s.pc)
    (run : ∀ val, SegU kernel Assumptions.all L g start (factsFrom (ctlLive stop) val)
      stop (factsFrom (ctlLive stop) val)) :
    SegU kernel Assumptions.all L g start (facts e L g ⟨s,i,v⟩ s.pc)
      stop (facts e L g ⟨s',i,v⟩ stop) := by
  intro t ht
  have ⟨_,_,_,_,hr⟩ := ht
  exact run (valueOf e L g ⟨s,i,v⟩) t (ht.mono (holds_factsFrom_mono hr sub))

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
