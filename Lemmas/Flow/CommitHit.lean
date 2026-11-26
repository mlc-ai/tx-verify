-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.CommitSelf

@[expose] public section

/-! # An unmasked commit hits its addressed mbarrier

A proof tool, the converse of `resolve_self_target`. A `tcgen05.commit` without a multicast mask
resolves with the mask of the addressed mbarrier's rank (`fires_commit_unmasked`,
`THREAD-TC-COMMIT-TARGETS`), and when the issuer's cluster has at most 16 CTAs that rank's bit
selects the addressed mbarrier itself (`resolve_self_hit`). -/

namespace PTX.Flow
open PTX

noncomputable section

/-- **An unmasked commit resolves with its mbarrier's rank bit.** -/
theorem fires_commit_unmasked {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {group : CtaGroup} {base : Nat} {off : Int} {pc : Nat} {e : Event} {o : Option TState}
    {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off none)) e o)
    (hk : e.kind = .tc (.commit s)) :
    ∃ mb, TcCommit.resolve L group (g / L.block) mb
      (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) = some s := by
  simp only [eventTmpl, tcCommitTmpl, bind, Except.bind, pure, Except.pure] at hf
  split_ifs at hf
  · cases hm : mbarClusterLoc L g t base off with
    | error f =>
      simp only [hm, ofExec, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok mb =>
      simp only [hm] at hf
      cases hs : TcCommit.resolve L group (g / L.block) mb
          (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) with
      | none =>
        simp only [hs, ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | some s' =>
        simp only [hs, ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk
        exact ⟨mb, hs⟩
  · simp only [throw, throwThe, MonadExceptOf.throw, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk

/-- **The rank bit of an unmasked commit selects its mbarrier**, in a cluster of at most 16 CTAs. -/
theorem resolve_self_hit {L : Launch} {group : CtaGroup} {issuer : Nat} {mb : Loc}
    {s : TcCommit.Spec}
    (hs : TcCommit.resolve L group issuer mb (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) = some s)
    (h16 : L.clusterSizeOf issuer ≤ 16) : ∃ rank, TcCommit.target s rank = some s.mbar := by
  unfold TcCommit.resolve at hs
  split_ifs at hs with h
  cases hs
  obtain ⟨hv, -, hsh, hcta, hcl, -⟩ := h
  obtain ⟨-, hr, hst⟩ := Step.cta_cluster hv hcta
  have hsz : L.clusterSizeOf issuer = L.clusterSizeAt (L.clusterOfCta mb.cta) := by
    rw [hcl]; rfl
  have hlt : L.rankOfCta mb.cta < 16 := by omega
  refine ⟨⟨L.rankOfCta mb.cta, hlt⟩, ?_⟩
  have hbit :
      (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)).toNat / 2 ^ L.rankOfCta mb.cta % 2 = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hlt),
      Nat.div_self (Nat.two_pow_pos _)]
  unfold TcCommit.target
  split_ifs with hc
  swap
  · exact absurd ⟨by rw [← hsz] at hr; exact hr, hbit⟩ hc
  simp only
  rw [← hcl, hst]
  obtain ⟨sp, c, a⟩ := mb
  simp only at hsh ⊢
  rw [hsh]

end
end PTX.Flow
