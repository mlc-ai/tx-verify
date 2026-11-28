-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Lemmas.Flow.PollRounds

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow Control

/-- Successful S and O polls, and this thread's P notifications. -/
structure Cnt where
  s : Nat
  o : Nat
  p : Nat
  deriving DecidableEq

def Cnt.bump (c : Cnt) (ev : Event) : Cnt :=
  ⟨c.s + (okPollAt 1257 ev).toNat,c.o + (okPollAt 2239 ev).toNat,
   c.p + (ev.pc == 1013).toNat⟩

def Site.afterS : Site → Bool
  | .setMaxReg | .bar0 | .pre _ | .nxt _ | .waitS | .epilogue => false
  | _ => true

def Site.afterO : Site → Bool
  | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL | .shfl11
  | .shfl12 | .ldO | .waitLdO | .bar24 | .stO | .waitStO | .bar20 | .tmemSt | .tmemWait
  | .bar21 | .arrive => true
  | _ => false

def counts (t : Nat) (d : D) : Cnt :=
  ⟨d.i + d.site.afterS.toNat,if d.site.afterO then d.i else d.i-1,
    if t%128=0 then d.i else 0⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax
