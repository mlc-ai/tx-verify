-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotWait
public import Lemmas.Flow.NotArrive
public import Lemmas.Flow.Events

@[expose] public section

/-! # The ordering flags of polls and arrivals

A proof tool. A poll event comes from an `mbarrier.try_wait` instruction with that
instruction's acquire flag (`fires_wait_flags`), and an arrival from an `mbarrier.arrive` with
its release flag (`fires_arrive_flags`); at a site an assumption selects for cluster scope, a
CTA-scope acquire or release is widened to cluster scope. -/

namespace PTX.Flow

/-- A poll event is fired by a wait instruction with its acquire flag, widened to cluster scope
under the assumption. -/
theorem fires_wait_flags {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    ∃ p' b off par sc0, op = .mbarWait p' b off par acq sc0 ∧
      (A.any (·.clusterScopeMbar t.pc) = true → acq = true → sc0 = .cta → sc = .cluster) := by
  cases op
  case mbarWait p' b off par acq' sc' =>
    simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
    cases hm : mbarLoc L g t b off with
    | error f =>
      simp only [hm, ofExec, widenMbarScope, ite_self, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok m' =>
      cases hq : readBits L g t 32 par with
      | error f =>
        simp only [hm, hq, ofExec, widenMbarScope, ite_self, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | ok q =>
        simp only [hm, hq, ofExec] at hf
        cases acq' <;> cases sc' <;> simp only [widenMbarScope] at hf <;>
          split_ifs at hf with hA <;>
          (simp only [Fires] at hf
           obtain ⟨ok', he, -⟩ := hf
           rw [he] at hk
           obtain ⟨-, -, -, h1, h2⟩ := Kind.wait.inj hk
           subst h1 h2
           exact ⟨_, _, _, _, _, rfl, by simp_all⟩)
  all_goals exfalso
  all_goals exact fires_notWait (eventTmpl_notWait (fun _ _ _ _ _ _ h =>
    Op.noConfusion h)) hf _ _ _ _ _ hk

/-- An arrival is fired by an arrive instruction with its release flag, widened to cluster scope
under the assumption. -/
theorem fires_arrive_flags {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx c rel sc) :
    ∃ b off tx' c' cl sc0 st, op = .mbarArrive b off tx' c' cl rel sc0 st ∧
      (A.any (·.clusterScopeMbar t.pc) = true → rel = true → sc0 = .cta → sc = .cluster) := by
  cases op
  case mbarArrive b off tx' c' cl rel' sc' st =>
    simp only [eventTmpl, tmaTmpl, bind, Except.bind, pure, Except.pure] at hf
    cases rel' <;> cases sc'
    all_goals repeat' split at hf
    all_goals simp only [ofExec, widenMbarScope] at hf
    all_goals (try split_ifs at hf)
    all_goals (try simp only [Fires] at hf)
    all_goals rw [hf.1] at hk
    all_goals first
      | (cases hk; done)
      | (obtain ⟨-, -, -, h1, h2⟩ := Kind.arrive.inj hk
         subst h1 h2
         exact ⟨_, _, _, _, _, _, _, rfl, by simp_all⟩)
  all_goals exfalso
  all_goals exact fires_notArrive (eventTmpl_notArrive (arriveOp_ne rfl)) hf _ _ _ _ _ hk

end PTX.Flow
