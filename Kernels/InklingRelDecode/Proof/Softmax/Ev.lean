-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Iface.MbarRows.Softmax

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX Control MbarRow PTX.MbarRow

/-- The three observable mbarrier shapes, indexed by the current loop iteration. -/
def ObjectEv (L : Launch) (g i : Nat) (s : Site) (ev : Event) : Prop :=
  match s with
  | .waitS => Wait ev (loc L g (Iface.sReady (slot2 i))) (i/2%2)
  | .waitO => Wait ev (loc L g Iface.oDone) ((i+1)%2)
  | .arrive => Arrive ev (loc L g (Iface.pReady (slot2 i))) 0
  | _ => True

end PTX.Kernels.InklingRelDecode.Proof.Softmax
