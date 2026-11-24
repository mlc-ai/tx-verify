-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

namespace PTX
noncomputable section

/-- Each observed target notification requires completion of the actual tracked MMA. -/
theorem commit_observed_done {X : Execution} (h : AsyncCopy.CommitOk X)
    {mma waiter : EvId} {acq : Bool} {ws : MbarScope}
    (ho : AsyncCopy.AsyncObserved X mma .mmaDone waiter acq ws) :
    X.async.mmaDone mma = true := by
  obtain ⟨commit, s, rank, m, ht, _, _, hn, _⟩ := ho.mma
  exact (h commit rank hn).2 mma ht

/-- An unmasked commit in a one-CTA cluster: its only target is rank 0, the addressed mbarrier. -/
def TcCommit.unicast (m : Loc) : TcCommit.Spec := ⟨.one, m, 1, m.cta, 1⟩

theorem TcCommit.target_unicast {m : Loc} (hm : m.space = .shared) :
    TcCommit.target (TcCommit.unicast m) 0 = some m := by
  obtain ⟨sp, cta, addr⟩ := m
  simp only at hm
  subst hm
  simp [TcCommit.target, TcCommit.unicast]

theorem TcCommit.target_unicast_inv {m l : Loc} {rank : Fin 16} (hm : m.space = .shared)
    (h : TcCommit.target (TcCommit.unicast m) rank = some l) : rank = 0 ∧ l = m := by
  obtain ⟨sp, cta, addr⟩ := m
  simp only at hm
  subst hm
  unfold TcCommit.target TcCommit.unicast at h
  split_ifs at h with hr
  cases h
  have h0 : rank = 0 := Fin.ext (by simp at hr; omega)
  subst h0
  exact ⟨rfl, by simp⟩

end
end PTX
