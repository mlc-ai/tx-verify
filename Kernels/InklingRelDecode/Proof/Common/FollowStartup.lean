-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.FollowHead
public import Kernels.InklingRelDecode.Proof.Common.Staged.Alloc

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section
variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem start_active {s t : Startup.D} {e : Event}
    (h : Startup.succ L g s e = some (some t)) : Startup.enterOf s = none := by
  obtain ⟨site,tm,x,w⟩ := s
  cases site <;> first | rfl | cases h

private theorem no_shfl_to_start {s t : Startup.D} {e : Event}
    (hs : Startup.succ L g s e = some (some t)) (ht : Startup.enterOf t = none)
    (shape : Execution.isShfl e = true → Startup.Ev L g s e) : Execution.isShfl e = false := by
  cases sh : Execution.isShfl e with
  | false => rfl
  | true =>
    have ev := shape sh
    obtain ⟨site,tm,x,w⟩ := s
    cases site <;> simp only [Startup.Ev] at ev
    all_goals try first | (solve | subst ev; cases sh) |
      (solve | obtain ⟨_,_,rfl⟩ := ev; cases sh) |
      (solve | obtain ⟨_,_,rfl,-⟩ := ev; cases sh) | (solve | cases hs)
    obtain ⟨recv,ok,rfl⟩ := ev
    simp only [Startup.succ] at hs
    split at hs <;> cases hs
    cases ht

/-- A live startup position precedes its lane's first shuffle. This direction uses
the shape of ordinary events, including the shuffle's transition into a role. -/
theorem startup_ordinal (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {t : Startup.D} {n} (hk : k ≤ (X.tr g).length) (ht : Startup.enterOf t = none)
    (live : Frame.stateAt (thread Q L) X g k = some (some (.inl t,n))) :
    ((X.tr g).take k).countP Execution.isShfl = 0 := by
  induction k generalizing t n with
  | zero => simp
  | succ k ih =>
    obtain ⟨s,n,e,hs,he,hn⟩ := prev_start (by omega) live
    have ord := ih (by omega) (start_active hn) hs
    have clear := no_shfl_to_start hn ht fun sh => start_ev hp hX he hs (by
      rintro f hf
      obtain ⟨pc,kd⟩ := e
      cases hf
      cases sh)
    change (X.tr g)[k]? = some e at he
    simp [List.take_add_one,he,ord,clear]

/-- No event stops a reached startup state. A shuffle that could otherwise
stop on a non-word receives the first source lane's warp index. -/
theorem startup_no_stop (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {s : Startup.D} {n} {e : Event} (he : X.get (g,k) = some e)
    (live : Frame.stateAt (thread Q L) X g k = some (some (.inl s,n))) :
    Startup.succ L g s e ≠ some none := by
  by_cases sh : s.site = .shfl
  · obtain ⟨pc,kd⟩ := e
    cases kd <;> simp only [Startup.succ,sh] <;> try trivial
    have ev := start_ev hp hX he live (by simp)
    rw [Startup.Ev,sh] at ev
    obtain ⟨recv,ok,eq⟩ := ev
    cases eq
    have hk : k < (X.tr g).length := by
      by_contra! h
      change (X.tr g)[k]? = some _ at he
      rw [List.getElem?_eq_none h] at he
      cases he
    have active : Startup.enterOf s = none := by simp [Startup.enterOf,sh]
    have word := startup_recv hp hX he (startup_ordinal hp hX hk.le active live)
    rw [word]
    simp [b32]
  · intro stop
    obtain ⟨site,tm,x,w⟩ := s
    cases site <;> simp only [Startup.succ] at stop
    all_goals repeat' first | (solve | cases stop) | (solve | exact sh rfl) | split at stop

end
end PTX.Kernels.InklingRelDecode.Proof
