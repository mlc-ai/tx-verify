-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Records
public import Lemmas.Flow.NthEv

@[expose] public section

/-! # The sources of the input ring's records

Every record of a slot's barriers arises as `BarSource` says (`full_src`, `empty_src`): the
initializations of CTA thread 0; the polls; the leader loader's arrivals on the full barrier;
the copies' completions; and the MMA threads' commit notifications on the empty barriers. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

/-- A fault-free arrival expecting the tile's bytes. -/
def isArrival (q : Record Ref) : Bool := decide (q.action = .arrive 1 98304 ∧ q.fault = none)

/-- A fault-free completion of one copy. -/
def isCompletion (q : Record Ref) : Bool := decide (q.action = .completeTx 16384 ∧ q.fault = none)

theorem isArrival_iff (q : Record Ref) :
    isArrival q = true ↔ q.action = .arrive 1 98304 ∧ q.fault = none := by
  simp [isArrival]

theorem isCompletion_iff (q : Record Ref) :
    isCompletion q = true ↔ q.action = .completeTx 16384 ∧ q.fault = none := by
  simp [isCompletion]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The source of a record of slot `s`'s full barrier. -/
theorem full_src (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {r : Record Ref} (hr : r ∈ X.objects ((slot L c s).full 0)) :
    BarSource L X ⟨.input, s.val, true⟩ (2 * c) r :=
  bar_source (b := ⟨.input, s.val, true⟩) hX ht s.isLt hr

/-- The source of a record of slot `s`'s empty barrier of producer `a`. -/
theorem empty_src (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {c : Nat}
    {s : Fin 4} {a : Fin 2} {r : Record Ref} (hr : r ∈ X.objects ((slot L c s).empty a)) :
    BarSource L X ⟨.input, s.val, false⟩ (2 * c + a.val) r :=
  bar_source (b := ⟨.input, s.val, false⟩) hX ht s.isLt hr

/-- A loader thread of the cluster is the producer of its CTA's rank. -/
theorem loader_producer (ht : ThreadFacts L X) {c g j : Nat} {l : Loader.D}
    (he : j ≤ (X.tr g).length) (hg : g < L.threads)
    (hσ : Frame.stateAt (code L) X g j = some (some (.inr (.loader l))))
    (hc : g / L.block / 2 = c) :
    producerThread L c ⟨g / L.block % 2, Nat.mod_lt _ (by decide)⟩ g = true := by
  have hw := ht.role_warp hg he hσ
  simp only [roleWarp] at hw
  simp only [producerThread, decide_eq_true_eq]
  omega

/-- A notification of consumer `b` to producer `a` is a commit notification of a thread of
selector `b` to rank `a`. -/
theorem notification_facts {c : Nat} {s : Fin 4} {a b : Fin 2} {d : Record Ref}
    (hn : (slot L c s).notification a b d = true) :
    ∃ i rank, d.id = .async i (.tcNotify rank) ∧ consumerThread L c b i.1 = true ∧
      rank.val = a.val ∧ d.action = .arrive 1 0 := by
  simp only [slot, notification] at hn
  split at hn
  · rename_i i rank hid
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hn
    exact ⟨i, rank, hid, hn.1, hn.2.1, hn.2.2⟩
  · cases hn

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
