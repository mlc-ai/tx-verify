-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Source.LocalOwned
public import Lemmas.Flow.NotBulkGroup
public import Lemmas.Flow.NotObject

@[expose] public section

/-! # The CTA of a tensor load's destination and of a `cp.async` copy

A tensor load's destination and mbarrier are in the issuer's cluster (`fires_tensorIssue_cluster`),
and a `cp.async` copies global memory to the issuer's CTA (`fires_cpAsync_local`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-- **A tensor load's destination and mbarrier are in the issuer's cluster.** -/
theorem fires_tensorIssue_cluster {op : Op} {pc epc a : Nat} {s : TensorCopy.Spec}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .tensorIssue a s⟩ o) :
    CtaInCluster L (g / L.block) s.sharedBase.cta ∧ CtaInCluster L (g / L.block) s.mbar.cta := by
  have hop : tensorOp op = true := by
    cases hq : tensorOp op
    · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a s)
    · rfl
  obtain ⟨u, hm⟩ : ∃ u, eventTmpl A L g t op = .tensorIssue a s u := by
    generalize eventTmpl A L g t op = m at hf
    cases m <;> simp only [Fires] at hf <;> aesop
  cases op <;> simp only [tensorOp, Bool.false_eq_true] at hop
  simp only [eventTmpl, tensorTmpl] at hm
  have hr := ofExec_eq_ok (fun f h => by cases h) hm
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    tensorMulticast] at hr
  repeat' (first | split at hr | (cases hr; done))
  all_goals
    simp only [Except.ok.injEq, Tmpl.tensorIssue.injEq] at hr
    obtain ⟨-, rfl, -⟩ := hr
    obtain ⟨-, -, -, h1, h2, -⟩ := ‹TensorRoute _ _ _ _ _ _›
    exact ⟨h1, h2⟩

/-- **A `cp.async` copies global memory to shared memory of the issuer's CTA.** -/
theorem fires_cpAsync_local {op : Op} {pc epc : Nat} {s : AsyncCopy.Spec} {o : Option TState}
    (hop : bulkGroupOp op = false)
    (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .copy s⟩ o) :
    s.completion = .asyncGroup ∧ s.src.loc.space = .global ∧ s.dst.loc.space = .shared ∧
      s.dst.loc.cta = g / L.block ∧ s.writes = .whole := by
  have hb := fires_bulk_op hf rfl
  obtain ⟨u, hm⟩ : ∃ u, eventTmpl A L g t op = .copy s u := by
    generalize eventTmpl A L g t op = m at hf
    cases m <;> simp only [Fires] at hf <;> aesop
  cases op <;> simp only [bulkOp, bulkGroupOp, Bool.false_eq_true, reduceCtorEq] at hb hop
  simp only [eventTmpl, cpAsyncTmpl] at hm
  have hr := ofExec_eq_ok (fun f h => by cases h) hm
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hr
  repeat' (first | split at hr | (cases hr; done))
  all_goals
    simp only [Except.ok.injEq, Tmpl.copy.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
  all_goals
    have h1 := effAddr_local ‹effAddr L g t .shared _ _ = .ok _›
    have h2 := effAddr_local ‹effAddr L g t .global _ _ = .ok _›
    exact ⟨rfl, h2.1, h1.1, h1.2 rfl, rfl⟩

/-- A load or store of local memory through a register. -/
def localRegOp : Op → Bool
  | .mem ma => ma.space == some .local && (ma.kind == .load || ma.kind == .store) &&
      match ma.addr.base with
      | .reg .. => true
      | _ => false
  | _ => false

/-- The location of an access of local memory through a register is in local memory. -/
theorem accessAcc_local_space {ma : MemAccess} {acc : Acc} {r w : Nat}
    (hs : ma.space = some .local) (hb : ma.addr.base = .reg r w)
    (h : accessAcc L g t ma = .ok acc) : acc.loc.space = .local := by
  have hmap : ∀ {α : Type} {f : α → Acc} {x : Exec α} {r : Acc}, f <$> x = .ok r →
      ∃ y, x = .ok y ∧ f y = r := by
    intro α f x r hx
    cases x with
    | error e => simp at hx
    | ok y => exact ⟨y, rfl, by simpa using hx⟩
  unfold accessAcc at h
  simp only [bind, Except.bind] at h
  cases hloc : accessLoc L g t ma with
  | error f => simp only [hloc, reduceCtorEq] at h
  | ok loc =>
    have hl : loc.space = .local := by
      unfold accessLoc at hloc
      simp only [hs, hb, bind, Except.bind, pure, Except.pure] at hloc
      repeat' (first | split at hloc | (cases hloc; done))
      cases hloc
      rfl
    simp only [hloc] at h
    repeat' (first | split at h | contradiction)
    obtain ⟨acc0, h0, he⟩ := hmap h
    obtain ⟨h1, -⟩ := elemAcc_local h0
    subst he
    rw [semAcc_loc, h1, hl]

/-- **An access of shared memory by an instruction that is no local access through a register is of
the thread's own CTA.** -/
theorem fires_access_own {op : Op} {pc : Nat} {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) e o) (hd : dynamicAccess op = true → localRegOp op = true)
    {a : Acc} (hk : (∃ bs, e.kind = .rd a bs) ∨ ∃ bs, e.kind = .wr a bs)
    (hs : a.loc.space = .shared) : a.loc.cta = g / L.block := by
  have key : dynamicAccess op = true → a.loc.cta = g / L.block := by
    intro hdy
    have hl := hd hdy
    cases op <;> simp only [localRegOp, Bool.false_eq_true] at hl
    rename_i ma
    cases hb : ma.addr.base <;> simp only [hb, Bool.and_false, Bool.false_eq_true] at hl
    rename_i r w
    simp only [Bool.and_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hl
    obtain ⟨hsp, hkd⟩ := hl
    have hnone : ma.locSpace? = none := by
      unfold MemAccess.locSpace?
      simp [hsp]
    exfalso
    have hacc : accessAcc L g t ma = .ok a → False := fun h => by
      rw [accessAcc_local_space hsp hb h] at hs
      cases hs
    have hT : memTmpl A L g t ma = atomTmpl A L g t ma ∨
        memTmpl A L g t ma = accessTmpl A L g t ma ∨ memTmpl A L g t ma = .ub .noRule := by
      simp only [memTmpl, hnone, hb]
      split
      · rename_i h _; cases h
      · exact .inl rfl
      · split
        · exact .inr (.inl rfl)
        · exact .inr (.inr rfl)
    obtain ⟨epc, ek⟩ := e
    simp only at hk
    rcases hk with ⟨bs, rfl⟩ | ⟨bs, rfl⟩
    · obtain ⟨k, hm⟩ := fires_read_tmpl hf
      simp only [eventTmpl] at hm
      rcases hT with h | h | h <;> rw [h] at hm
      · exact atomTmpl_noRead hm
      · unfold accessTmpl at hm
        rcases hkd with hkd | hkd <;> simp only [hkd] at hm
        · split at hm
          · cases hm
          · rename_i acc hac
            repeat' (first | split at hm | (cases hm; done))
            simp only [Tmpl.read.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            exact hacc hac
        · repeat' split at hm
          all_goals cases hm
      · cases hm
    · rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, -⟩
      · simp only [eventTmpl] at hm
        rcases hT with h | h | h <;> rw [h] at hm
        · exact atomTmpl_noWrite hm
        · unfold accessTmpl at hm
          rcases hkd with hkd | hkd <;> simp only [hkd] at hm
          · repeat' split at hm
            all_goals cases hm
          · split at hm
            · cases hm
            · rename_i acc hac
              repeat' (first | split at hm | (cases hm; done))
              simp only [Tmpl.write.injEq] at hm
              obtain ⟨rfl, -⟩ := hm
              exact hacc hac
        · cases hm
      · have := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := ma)
        simp only [eventTmpl] at hm
        rw [hm] at this
        exact this.elim
  rcases hk with ⟨bs, hk⟩ | ⟨bs, hk⟩
  · rcases fires_read_loc hf hk with ⟨-, h2⟩ | h
    · exact h2 hs
    · exact key h
  · rcases fires_write_loc hf hk with ⟨-, h2⟩ | h
    · exact h2 hs
    · exact key h

end
end PTX.Flow
