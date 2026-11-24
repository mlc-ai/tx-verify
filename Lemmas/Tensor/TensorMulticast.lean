-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.Tensor.TensorThread
public import Lemmas.Tensor.TensorMap

@[expose] public section

/-! A `.multicast::cluster` sub-step (`tensorMulticast`) issues one tensor copy and continues at
the same instruction (next destination) or the next one, without touching registers. -/
namespace PTX

theorem tensorMulticast_ok {L : Launch} {g : Nat} {t : TState} {mapAddress : Nat}
    {s : TensorCopy.Spec} {width : Nat} {mask : Opnd} {m : Tmpl}
    (h : tensorMulticast L g t mapAddress s width mask = .ok m) :
    ∃ s' u, m = .tensorIssue mapAddress s' u ∧ u.regs = t.regs ∧
      (u.pc = t.pc ∨ u.pc = t.pc + 1) := by
  unfold tensorMulticast at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | split_ifs at h | split at h)
  all_goals cases h
  all_goals exact ⟨_, _, rfl, rfl, by simp [next]⟩

/-- A tensor-load instruction's template is a fault, or one tensor-copy issue that keeps every
register and continues at the same instruction (a further multicast destination) or the next. -/
theorem tensorTmpl_cpTensor_cases {L : Launch} {g : Nat} {t : TState} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {mc : Option (Nat × Opnd)}
    {lm : TensorMode} {policy : Option Opnd} :
    (∃ f, tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff mc lm policy) = .ub f) ∨
    ∃ a s u,
      tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff mc lm policy) = .tensorIssue a s u ∧
      u.regs = t.regs ∧ (u.pc = t.pc ∨ u.pc = t.pc + 1) := by
  generalize hm : tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff mc lm policy) = m
  simp only [tensorTmpl, ofExec] at hm
  split at hm
  · rename_i r hr
    right
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
    subst hm
    repeat' (first | split_ifs at hr | split at hr)
    all_goals first
      | (cases hr; exact ⟨_, _, _, rfl, rfl, .inr rfl⟩)
      | cases hr
      | (obtain ⟨s', u, rfl, hregs, hpc⟩ := tensorMulticast_ok hr
         exact ⟨_, _, _, rfl, hregs, hpc⟩)
  · exact .inl ⟨_, hm.symm⟩

/-- Without multicast a tensor-load template is a fault or one copy issue continuing at the next
instruction. -/
theorem tensorTmpl_cpTensor_unicast {L : Launch} {g : Nat} {t : TState} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} :
    (∃ f, tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm) = .ub f) ∨
    ∃ a s, tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm) =
      .tensorIssue a s (next t) := by
  simp only [tensorTmpl, cachePolicyRead, ofExec, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw]
  rcases tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a, s⟩
  · exact .inl ⟨f, rfl⟩
  · dsimp only
    split_ifs
    · exact .inr ⟨a, s, rfl⟩
    · exact .inl ⟨_, rfl⟩

/-- A successful tensor load's copy uses the map at its resolved address and the resolved
mbarrier: the transfer descriptor of its mode, with row coordinates exactly in gather4 mode. -/
theorem tensorLoadCopy_ok {L : Launch} {g : Nat} {t : TState} {ca grp : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec} (h : tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s)) :
    tensorMapAddress L g t map = .ok a ∧
      (if ca then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff) = .ok s.mbar ∧
      ∃ d, L.tensorMaps a = some ⟨s.outer, d⟩ ∧
      TensorDescriptor.Valid d ∧ s.descriptor = lm.transfer d ∧ (s.rows = none ↔ lm = .tile) := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  obtain ⟨hma, hd, hv, -⟩ := tensorMap_ok hm
  cases ca <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  all_goals repeat' (split at h <;> (try (cases h; done)))
  all_goals
    cases h
    refine ⟨hma, by assumption, d, hd, hv, rfl, ?_⟩
    cases lm <;> simp

/-- A unicast tensor-load issue is the copy of `tensorLoadCopy` continuing at the next
instruction. -/
theorem tensorTmpl_unicast_issue {L : Launch} {g : Nat} {t u : TState} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode}
    {a : Nat} {s : TensorCopy.Spec}
    (h : tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm) = .tensorIssue a s u) :
    tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s) ∧ u = next t := by
  simp only [tensorTmpl, cachePolicyRead, ofExec, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at h
  rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
    rw [hc] at h
  · cases h
  · dsimp only at h
    split_ifs at h
    · cases h; exact ⟨rfl, rfl⟩

end PTX
