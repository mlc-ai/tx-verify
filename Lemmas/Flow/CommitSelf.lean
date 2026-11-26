-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Step.Cluster

@[expose] public section

/-! # An unmasked commit targets only its addressed mbarrier

A proof tool. A `tcgen05.commit` without a multicast mask selects the rank of the addressed
mbarrier's CTA (`THREAD-TC-COMMIT-TARGETS`), so its only target is the addressed mbarrier
(`resolve_self_target`); `fires_commit_self` is `fires_commit_reg` with that fact. -/

namespace PTX.Flow
open PTX

noncomputable section

/-- **The only target of an unmasked commit is its addressed mbarrier.** -/
theorem resolve_self_target {L : Launch} {group : CtaGroup} {issuer : Nat} {mbar : Loc}
    {s : TcCommit.Spec}
    (hs : TcCommit.resolve L group issuer mbar (BitVec.ofNat 16 (2 ^ L.rankOfCta mbar.cta)) =
      some s) {rank : Fin 16} {l : Loc} (ht : TcCommit.target s rank = some l) : l = s.mbar := by
  unfold TcCommit.resolve at hs
  split_ifs at hs with h
  cases hs
  obtain ⟨hv, -, hsh, hcta, hcl, -⟩ := h
  unfold TcCommit.target at ht
  split_ifs at ht with h2
  cases ht
  obtain ⟨-, hbit⟩ := h2
  simp only at hbit ⊢
  have hr : L.rankOfCta mbar.cta = rank.val := by
    have hlt := rank.isLt
    by_contra hne
    simp only [BitVec.toNat_ofNat] at hbit
    rcases Nat.lt_or_ge (L.rankOfCta mbar.cta) 16 with h16 | h16
    · rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) h16)] at hbit
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)] at hbit
        simp at hbit
      · obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_lt h
        rw [hc, Nat.pow_add, Nat.pow_add, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]
          at hbit
        simp at hbit
    · rw [show 2 ^ L.rankOfCta mbar.cta = 2 ^ 16 * 2 ^ (L.rankOfCta mbar.cta - 16) by
        rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_right] at hbit
      simp at hbit
  obtain ⟨-, -, hst⟩ := Step.cta_cluster hv hcta
  rw [← hcl, ← hr, hst]
  obtain ⟨sp, c, a⟩ := mbar
  simp only at hsh ⊢
  rw [hsh]

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **An unmasked commit**: its event addresses the register's mbarrier, which is its only
target, or undefined behaviour. -/
theorem fires_commit_self {t : TState} {group : CtaGroup} {base : Nat} {off : Int} {pc : Nat}
    {e : Event} {o : Option TState} {x : BitVec 64} {wx : Nat}
    (hb : t.regs base = some (.bits wx x))
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off none)) e o) :
    (∃ s, e.kind = .tc (.commit s) ∧ s.mbar = smLoc L g x off ∧ s.group = group ∧
      ∀ rank l, TcCommit.target s rank = some l → l = s.mbar) ∨ ∃ f, e.kind = .ub f := by
  simp only [eventTmpl, tcCommitTmpl, mbarClusterLoc, sharedEffAddr, readReg, hb, readBits,
    bind, Except.bind, pure, Except.pure] at hf
  split_ifs at hf
  · cases hs : TcCommit.resolve L group (g / L.block) (smLoc L g x off)
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (smLoc L g x off).cta)) with
    | none =>
      simp only [smLoc] at hs
      simp only [hs, ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
      exact .inr ⟨_, congrArg Event.kind hf.1⟩
    | some s =>
      have hs' := hs
      have hself := fun rank l (ht : TcCommit.target s rank = some l) => resolve_self_target hs ht
      simp only [smLoc] at hs
      simp only [hs, ofExec, Fires] at hf
      refine .inl ⟨s, by rw [hf.1], ?_⟩
      simp only [TcCommit.resolve] at hs'
      split_ifs at hs'
      cases hs'
      exact ⟨rfl, rfl, hself⟩
  all_goals
    simp only [ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact .inr ⟨_, congrArg Event.kind hf.1⟩

end
end PTX.Flow
