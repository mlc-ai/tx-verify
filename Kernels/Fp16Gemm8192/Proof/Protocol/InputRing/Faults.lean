-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Items
public import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

/-! # The input ring's records are fault-free

Every record of a slot's barriers is fault-free (`fault_free`, by `PairTmaRing.fault_free` for
`pslot` under `hyp`). On an empty barrier, the slot's notification selector is the generic one
(`notification_iff`, `PairTmaRing.notifies`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every record of the input ring's objects is fault-free.** -/
theorem fault_free (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {m : Loc}
    (hm : m ∈ (slot L c s).objects) {r : Record Ref} (hr : r ∈ X.objects m) : r.fault = none := by
  refine PairTmaRing.fault_free hX (hyp hpre hX ht c s) ?_ hr
  rcases (slot L c s).objects_cases hm with ⟨k, rfl⟩ | ⟨a, rfl⟩
  · exact .inl (by rw [Subsingleton.elim k 0]; rfl)
  · exact .inr ⟨a, rfl⟩

/-- On producer `a`'s empty barrier, consumer `b`'s notifications are the slot's notification
selector's. -/
theorem notification_iff (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {a b : Fin 2} {x : Record Ref}
    (hx : x ∈ X.objects ((slot L c s).empty a)) :
    (slot L c s).notification a b x = PairTmaRing.notifies (pslot L X c s) a b x := by
  have hcons := consumerOf_thread (X := X) hpre c s b
  cases hn : (slot L c s).notification a b x
  · cases hm : PairTmaRing.notifies (pslot L X c s) a b x
    · rfl
    · obtain ⟨jc, pc, sp, hid, -⟩ := PairTmaRing.notifies_commit (hyp hpre hX ht c s) hx hm
      have ha : x.action = .arrive 1 0 := by
        simp only [PairTmaRing.notifies, hid, decide_eq_true_eq] at hm
        exact hm.2.2
      simp only [slot, notification, hid, pslot, hcons, ha, Bool.true_and, and_true] at hn
      simp [PairTmaRing.rankOf] at hn
  · obtain ⟨jc, pc, sp, hid, -⟩ := notification_commit hX ht hx hn
    obtain ⟨-, -, -, -, -, ha⟩ := notification_facts hn
    simp only [PairTmaRing.notifies, hid, pslot, PairTmaRing.rankOf, ha, decide_true, and_true]

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
