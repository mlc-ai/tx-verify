-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Flow.UbFree

@[expose] public section

/-! # The shared source of a tensor store from its address register

A proof tool. A `cp.async.bulk.tensor` store (or reduction) whose source register holds the
32-bit word `x` reads its box from the shared location `smLoc L g x off` (`fires_tensorStore_src`):
the specification's `sharedBase` is the register's word plus the instruction's offset. -/

namespace PTX.Flow
open PTX PTX.Proof

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- **The source of a tensor store is its address register's word.** -/
theorem fires_tensorStore_src {t : TState} {map : Opnd} {cs : List Opnd} {src : Nat} {off : Int}
    {policy : Option Opnd} {mode : TensorMode} {reduce : Option AtomOp} {pc : Nat} {e : Event}
    {o : Option TState} {x : BitVec 64} (hr : t.regs src = some (.bits 32 x))
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map cs src off policy mode reduce)) e o)
    {a : Nat} {s : TensorStore.Spec} (hk : e.kind = .tensorStore a s) :
    s.sharedBase = smLoc L g x off := by
  have h := fires_cpTensorStore_ok hf hk
  have he : sharedEffAddr L g t false src off = .ok (smLoc L g x off) := by
    have := effAddr_shared32 (L := L) (g := g) (off := off) hr
    simpa only [effAddr, smLoc] using this
  unfold tensorStoreSpec at h
  cases hm : tensorMap L g t map cs mode with
  | error f => simp only [hm, bind, Except.bind] at h; cases h
  | ok r =>
    obtain ⟨ma, outer, desc⟩ := r
    simp only [hm, he, bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals cases h
    all_goals rfl

end PTX.Flow
