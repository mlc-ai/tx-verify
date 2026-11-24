-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.EpilogueWriteback

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- A global write is either an LSE word or a byte of an issued output box. -/
theorem globalWriteSource {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l Decoded.kernel A m X)
    {w : AsyncCopy.Ref} {a : Acc} (hw : X.Intent w a true) (hs : a.loc.space = .global) :
    (∃ i bytes, w = .thread i ∧ X.Writes i a bytes) ∨
    (∃ i x y k addr spec, w = .async i (.write (.store x y k)) ∧
      X.TensorStoreIssue i addr spec ∧
      TensorStore.writeLoc spec x y k = some a.loc ∧ a.size = 1) := by
  rcases globalWriteIntentSources hX hw hs with
    ⟨i, site, bytes, hRef, _, he⟩ | ⟨i, x, y, k, site, addr, spec, hRef, _, he, hLoc, hSize⟩
  · exact .inl ⟨i, bytes, hRef, site, he⟩
  · exact .inr ⟨i, x, y, k, addr, spec, hRef, ⟨site, he⟩, hLoc, hSize⟩

/-- The performed value of an ordinary write equals the value carried by its trace event. -/
theorem sameOrdinaryWriteBytes {X : Execution} {i : EvId} {a : Acc} {bytes bytes' : List Byte}
    (hWrite : X.MemWrites (.thread i) a bytes) (he : X.Writes i a bytes') : bytes = bytes' := by
  obtain ⟨_, he⟩ := he
  rcases hWrite with ⟨_, hw⟩ | ⟨_, _, hw⟩
  · rw [he] at hw
    exact (Kind.wr.inj (Event.mk.inj (Option.some.inj hw)).2).2.symm
  · rw [he] at hw
    cases hw

end PTX.Kernels.TmlFa4Fwd.Thread

namespace PTX.Kernels.TmlFa4Fwd
open PTX

/-- Every issued tensor store has the output descriptor of its work item's stage and box. -/
def OutputTensorSpecs (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ i pc addr s, pc ∈ outputStoreSites → X.get i = some ⟨pc, .tensorStore addr s⟩ →
    ∃ batch < p.batch, ∃ head < p.heads, ∃ (tile : Nat) (stage : Fin 2) (box : Fin 4),
      s = Epilogue.writebackStoreSpec p l i.1 batch head tile stage box

/-- The two scalar store sites write a complete FP32 LSE element. -/
def LseStoreSpecs (p : Params) (X : Execution) : Prop :=
  ∀ i pc a bytes, pc ∈ lseStoreSites → X.get i = some ⟨pc, .wr a bytes⟩ →
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4

end PTX.Kernels.TmlFa4Fwd
