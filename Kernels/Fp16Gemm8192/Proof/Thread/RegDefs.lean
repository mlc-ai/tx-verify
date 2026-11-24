-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine

@[expose] public section

/-! # A thread's register requests

Every thread issues one register request (`setmaxnreg`), right after its cluster barrier wait
of the prologue: warps 8 to 11 lower their register count to 56 at the prologue's site, the
consumer warps raise it to 224 at the consumer's first site. The requests a thread has issued
(`regOps`) and the count its state implies (`ThreadD.regOps`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX

noncomputable section

/-- A register request. -/
def isSetMaxReg (e : Event) : Bool := match e.kind with | .setMaxReg .. => true | _ => false

/-- A thread's register requests. -/
def regOps (es : List Event) : Nat := es.countP isSetMaxReg

/-- The register requests before a state: none until the request's site, one after it. -/
def ThreadD.regOps : ThreadD → Nat
  | .inl p => if p.site = .roleElect then 1 else 0
  | .inr (.cons c) => if c.site = .setMaxReg then 0 else 1
  | .inr _ => 1

/-- A state at its register request. -/
def ThreadD.AtSetMaxReg : ThreadD → Prop
  | .inl p => p.site = .setMaxReg
  | .inr (.cons c) => c.site = .setMaxReg
  | .inr _ => False

/-- The request a state at its site issues: the prologue's lowering, the consumers' raising. -/
def ThreadD.regRequest : ThreadD → Nat × Bool × Nat
  | .inl _ => (Flow.setMaxReg_0, false, 56)
  | .inr _ => (Flow.setMaxReg_1, true, 224)

/-- The request of the threads of warp `w`: its program position, direction and count. -/
def regRequest (w : Nat) : Nat × Bool × Nat :=
  if w < 8 then (Flow.setMaxReg_1, true, 224) else (Flow.setMaxReg_0, false, 56)

/-- The latest time of a state of warp `w` before its request: the consumer's first site, or the
prologue's. -/
def regEarly (w : Nat) : Nat := if w < 8 then 58 else 54

/-- The earliest time of a state of warp `w` after its request. -/
def regLate (w : Nat) : Nat := if w < 8 then 104 else 56

end
end PTX.Kernels.Fp16Gemm8192.Proof
