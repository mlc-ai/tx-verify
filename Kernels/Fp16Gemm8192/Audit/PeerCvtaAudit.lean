-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Spec
public import Core.Thread.Run
public import Lemmas.Flow.Run

@[expose] public section

/-! Audit of the loader's peer generic-to-shared conversion.

The decoded instruction at pc103 is `cvta.to.shared::cluster.u64 %rd32, %rd33`.
`mapa.u64` in rank one's loader prepares `%rd33` as a pointer into rank zero's shared
window, so the pointer records CTA one as its producer. This
primitive example checks the current rules for rank one's loader with that operand.
It does not supply the preceding source trace or collective history.

The standard rule still rejects an implicit CTA conversion for the peer pointer.
The regenerated production instruction explicitly converts in cluster space and
preserves the target, producer and offset, including through the following 32-bit narrowing.
-/
namespace PTX.Kernels.Fp16Gemm8192.PeerCvtaAudit
open PTX

def launch : Launch where
  grid := 2
  block := 384
  clusterSize := 2
  params := fun _ => none

/-- CTA one, warp eleven, lane zero. -/
def loader : Nat := 736

def state : TState where
  pc := 103
  regs := fun r => if r = 926 then
    some (.ptr 64 true (.shared 1 0) (BitVec.ofNat 64 8)) else none

theorem loader_is_peer : loader / launch.block = 1 := rfl

theorem decoded_instruction : kernel.code[103]? =
    some ⟨none, .addr (.cvta true (.shared .cluster) 64 925 (.reg 926))⟩ := rfl

theorem standard_conversion_rejected :
    execCvta launch loader state
      (.cvta true (.shared .cta) 64 925 (.reg 926)) = .error .badValue := rfl

theorem production_instruction_preserves_peer :
    out kernel [] launch loader state =
      .tau (next (setReg state 925 (.ptr 64 false (.shared 1 0) (BitVec.ofNat 64 8)))) := rfl

theorem production_narrowing_preserves_peer :
    run kernel [] launch loader 2 state =
      some (next (setReg (next (setReg state 925
        (.ptr 64 false (.shared 1 0) (BitVec.ofNat 64 8)))) 750
        (.ptr 32 false (.shared 1 0) (BitVec.ofNat 64 8)))) := rfl

theorem cluster_conversion_preserves_peer :
    execCvta launch loader state
      (.cvta true (.shared .cluster) 64 925 (.reg 926)) =
      .ok (next (setReg state 925 (.ptr 64 false (.shared 1 0) (BitVec.ofNat 64 8)))) := rfl

end PTX.Kernels.Fp16Gemm8192.PeerCvtaAudit
