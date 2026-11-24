-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.CorrStore
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.NoUb
import Kernels.TmlFa4Fwd.Proof.Lib.Guarded
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.FaultFree
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.Global
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Bytes
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Operands
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Results

@[expose] public section

/-! # The facts of the operand values, and the data reads

The order of the induction, for one consistent execution:

1. `Follow p L X` holds for every consistent execution (`Proof.follow`); no data read is used.
2. The elements in shared memory are numbers (`smemElements`), from the copies' sources.
3. The conditional facts of the lanes: a softmax lane's store (`SoftFacts.soft`) at an event has its
   values once the Tensor Memory loads of the CTA before *that event* returned numbers
   (`LoadsBefore`). A statistics read returns what the correction lane follows under the same
   condition (`SoftFacts.stat`): its source store is causally before it (`stat_source`), so the
   condition at the read gives that at the store. And so a correction lane's store has its values
   under it (`corrStores`).
4. The one induction (`results`, on the position of the MMA in its lane): an MMA's old value and
   operands come from earlier MMAs and from stores before it; the loads before such a store are
   before the MMA, so the induction hypothesis gives their `LoadsBefore`. Its other hypothesis,
   `SyncGuarded`, is `no_fault`, from 1 alone. So every load returned numbers (`load_f32`).
5. The data reads (`scorePayloads`, `dataTo`), and then the absence of undefined behaviour.

Steps 1 to 4 read neither `DataSrc` nor `ScorePayloads`, which are results of step 5. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

/-- **The softmax lanes' part of the operand values**: their stores, and what the correction lanes
read of their statistics. -/
structure SoftFacts (L : Launch) (X : Execution) : Prop where
  soft : SoftStores L X
  stat : StatReads L X

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hS : SoftFacts L X)
include hp hX hFw hS

/-- **The facts of the operand values** (steps 2 and 3). -/
theorem elementFacts : ElementFacts L X where
  smem := smemElements hp (operandBytes
    (J := fun _ => ⟨fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩) hp hX hFw
    (inputsUnwritten hp (Top.noInputWrite hp hX hFw))) hX hFw
  soft := hS.soft
  corr := corrStores hp hX hFw hS.stat

/-- **Every Tensor Memory load returned numbers** (step 4). -/
theorem loads_f32 {e : EvId} {a : Nat} {vals : List Value} (hl : X.TLd e a vals .s32x32b) :
    F32s vals :=
  load_f32 hp hX hFw (guardedOfNoObjectFault hX (no_fault hp hX hFw))
    (elementFacts hp hX hFw hS) hl

/-- **The score loads return numbers.** -/
theorem scorePayloads : SmWarp.ScorePayloads p L X := by
  intro g k d n r j a vals sh pc he _ _
  have hl : X.TLd (g, k) a vals sh := ⟨pc, he⟩
  obtain rfl := (Tm.scoreFacts hp hX hFw).tc_shape (.inl hl)
  exact loads_f32 hp hX hFw hS hl

/-- **The data reads of a correction lane** are those its data machine follows. -/
theorem dataTo {h : Nat} (hh : h < L.threads) (h8 : 8 ≤ Prologue.warpIndex L h)
    (h12 : Prologue.warpIndex L h ≤ 11) (K : Nat) : CorrWarp.DataTo p L X h K :=
  dataTo_of hp hX hFw hS.stat (loads_f32 hp hX hFw hS) hh h8
    (by omega) K

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Values
