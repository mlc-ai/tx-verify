-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorBox

@[expose] public section

/-! # A tensor load's route and descriptor

A proof tool. A unicast tensor load issues its copy only when its destination and barrier are
routed from the issuing CTA (`TensorRoute`) and the map it reads has a valid descriptor
(`fires_cpTensor_route`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- A unicast tensor load's copy is routed from the issuing CTA. -/
theorem tensorTmpl_unicast_route {L : Launch} {g : Nat} {t u : TState} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {a : Nat} {s : TensorCopy.Spec}
    (h : tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm) = .tensorIssue a s u) :
    TensorRoute L (g / L.block) s.clusterAddress s.group s.sharedBase s.mbar := by
  simp only [tensorTmpl, cachePolicyRead, ofExec, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at h
  rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
    rw [hc] at h
  · cases h
  · dsimp only at h
    split_ifs at h with hr
    cases h
    exact hr

/-- **A tensor load's route and map.** A unicast tensor load through a cluster address issues a
copy routed from the issuing CTA, of a map with a valid descriptor. -/
theorem fires_cpTensor_route {A : List Assumption} {L : Launch} {g : Nat} {t u : TState}
    {grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u)) {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    TensorCopy.RoutingOk L (g / L.block) s ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧ TensorDescriptor.Valid d ∧
        s.descriptor = lm.transfer d := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor true grp dst off map cs mb moff none lm)) e
      (some u) := hf
  rcases tensorTmpl_cpTensor_unicast (L := L) (g := g) (t := t) (ca := true) (grp := grp)
    (dst := dst) (mb := mb) (off := off) (moff := moff) (map := map) (cs := cs) (lm := lm) with
    ⟨f, hT⟩ | ⟨a', s', hT⟩
  · rw [hT] at hf'
    simp [Fires] at hf'
  · rw [hT] at hf'
    obtain ⟨rfl, -⟩ := hf'
    cases hk
    obtain ⟨hcopy, -⟩ := tensorTmpl_unicast_issue hT
    obtain ⟨-, -, d, hd, hv, hdesc, -⟩ := tensorLoadCopy_ok hcopy
    exact ⟨tensorTmpl_unicast_route hT, d, hd, hv, hdesc⟩

end

end PTX.Flow
