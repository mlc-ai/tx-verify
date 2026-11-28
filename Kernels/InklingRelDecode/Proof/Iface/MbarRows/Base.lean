-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRow
public import Lemmas.Flow.PollRounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.MbarRow
open PTX PTX.Flow

def loc (L : Launch) (g off : Nat) : Loc := ⟨.shared,g / L.block,L.sharedBase + off⟩
def slot2 (n : Nat) : Fin 2 := ⟨n % 2, by omega⟩
def slot3 (n : Nat) : Fin 3 := ⟨n % 3, by omega⟩
def roundAt (X : Execution) (g k pc : Nat) := pollRound pc ((X.tr g).take k)

def Row (L : Launch) (X : Execution) (atPc : Nat → Nat → Prop)
    (use : Nat → Nat → Event → Loc → Prop) : Prop :=
  ∀ {g k e l}, g < L.threads → X.get (g,k) = some e → atPc g e.pc → Frame.MbarOf e l →
    use g k e l

end PTX.Kernels.InklingRelDecode.Proof.MbarRow
