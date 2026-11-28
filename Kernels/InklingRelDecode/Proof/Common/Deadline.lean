-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.PreElect
public import Kernels.InklingRelDecode.Proof.Common.Time
import all Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Lib.ResPcs
import Lemmas.Flow.NotBulk

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame PTX.Sched

/-- A last live state gives the deadline. An observed terminal event charges one more
tick to its preceding state, which therefore needs a strict bound. -/
theorem deadline_of_states {Q L m X g bound} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hg : g<L.threads)
    (atState : ∀ {k st}, k≤(X.tr g).length → stateAt (schedule Q L).code X g k=some (some st) →
      (schedule Q L).time g st≤bound ∧ ((schedule Q L).code g).pc st≠2855 ∧
        (k<(X.tr g).length → (schedule Q L).time g st<bound)) :
    threadTime (schedule Q L) X g≤bound ∧ ∀ k pc, X.get (g,k)≠some ⟨pc,.exit⟩ := by
  constructor
  · unfold threadTime
    split
    · rename_i st hs; have := (atState (by omega) hs).1; omega
    · omega
    · split
      · rename_i st hs
        by_cases z : (X.tr g).length=0
        · simp only [z,Nat.zero_sub,Frame.stateAt_zero] at *
          simp_all
        · have := (atState (by omega) hs).2.2 (by omega)
          omega
      · omega
  · intro k pc he
    obtain ⟨st,hs,_⟩ := good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
      hX he (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
    have pcEq := event_pcU (fun g hg => thread_sound hp hg) hX he hs (by simp)
    obtain ⟨_,bad⟩|⟨_,_,_,_,code,fire⟩ := get_source hX he
    · cases bad
    exact (atState (List.getElem?_eq_some_iff.mp he).1.le hs).2.1
      (pcEq.symm.trans (List.mem_singleton.mp (Lib.ret_pc' code fire rfl)))

end PTX.Kernels.InklingRelDecode.Proof
