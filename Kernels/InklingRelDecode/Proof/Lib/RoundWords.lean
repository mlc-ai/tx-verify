-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Lib.Alpha

@[expose] public section

/-! # The words of the softmax rounds, as functions of the trace

The scale word of the launch and the running maximum and the round's new maximum as functions of
the words the thread's shuffles of pc 1838 sent and received. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The softmax scale parameter, as the startup left it in register 525. -/
def scaleVal (L : Launch) : Value :=
  .bits 32 (truncBits 32 ((L.params (param "15")).getD 0))

/-- The scale word `%r498` of pc 601. -/
def scaleW (L : Launch) : Value := Lib.scaleWord (scaleVal L)

/-- The words an event adds: the sent and received words of a shuffle of pc 1838. -/
def wordOf : Event → List (Value × Value)
  | ⟨1838, .shfl _ sent _ _ recv _⟩ => [(sent, recv)]
  | _ => []

/-- **The sent and received words** of the shuffles of pc 1838 among the first `j` events of a
lane. -/
def roundWords (X : Execution) (g j : Nat) : List (Value × Value) :=
  ((X.tr g).take j).flatMap wordOf

/-- The running maximum after the rounds of these words: `-inf`, then each round's new maximum
and update. -/
def mAfter (c : Value) (ps : List (Value × Value)) : Value :=
  ps.foldl (fun m p => Lib.mNext c m (Lib.mxWord m p.1 p.2)) (b32 4286578688)

theorem mAfter_append (c : Value) (ps : List (Value × Value)) (p : Value × Value) :
    mAfter c (ps ++ [p]) = Lib.mNext c (mAfter c ps) (Lib.mxWord (mAfter c ps) p.1 p.2) := by
  simp [mAfter]

/-- The running maximum a lane carries into its last round of the first `j` events. -/
def mRound (L : Launch) (X : Execution) (g j : Nat) : Value :=
  mAfter (scaleW L) (roundWords X g j).dropLast

/-- The new maximum of a lane's last round of the first `j` events. -/
def mxRound (L : Launch) (X : Execution) (g j : Nat) : Value :=
  match (roundWords X g j).getLast? with
  | some p => Lib.mxWord (mRound L X g j) p.1 p.2
  | none => b32 0

/-- The rescale factor (register 507) the round's words leave. -/
def alphaWord (c m mx : Value) : Value := Lib.alphaVal c m mx 507

theorem roundWords_succ {X : Execution} {g k : Nat} {ev : Event} (get : X.get (g, k) = some ev) :
    roundWords X g (k + 1) = roundWords X g k ++ wordOf ev := by
  have : (X.tr g)[k]? = some ev := get
  simp [roundWords, List.take_add_one, this, List.flatMap_append]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
