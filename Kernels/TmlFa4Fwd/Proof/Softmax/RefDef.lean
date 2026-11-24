-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape

@[expose] public section

/-! # The reference invariant and the expected values -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- What an event at a state must return for the reference invariant to continue: a 32-bit word
at the scheduler's reads and shuffles and at the request's reads; at the first pass's tile count,
a word whose coordinates the code divides by nonzero divisors (`divOk`, as the output warp's
`coords_W` gives from the scheduler's values); at a bias load, bytes that rebuild into two `bf16`
payloads or masked halves (`biasOk`: the protected-read source of the loader's copies of the
bias); at a score load, `f32` payloads (the source of the kernel's `TcLdDataflow` assumption). -/
def ExpectD (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk => ∀ a bs, e.kind = .rd a bs → ∃ x, rebuild 3 bs = .ok (.bits 32 x)
  | .tiles false => ∀ md a b c v ok, e.kind = .shfl md a b c v ok → ∃ x, v = .bits 32 x ∧
      Epilogue.divOk (Mma.coords p L g { d.v.sc with nt := x }).n1
        (Mma.coords p L g { d.v.sc with nt := x }).d1 = true ∧
      Epilogue.divOk (Mma.coords p L g { d.v.sc with nt := x }).n2
        (Mma.coords p L g { d.v.sc with nt := x }).d2 = true
  | .down _ | .up _ _ | .total _ | .pre _ | .tiles true =>
    ∀ md a b c v ok, e.kind = .shfl md a b c v ok → ∃ x, v = .bits 32 x
  | .bld _ _ => ∀ a bs, e.kind = .rd a bs → ∃ v, rebuild 3 bs = .ok v ∧ biasOk v = true
  | .sld _ _ => ∀ a vals sh, e.kind = .tc (.ld a vals sh) → ∀ v ∈ vals, ∃ x, v = .float .f32 x
  | _ => True

/-- **The expected values** at a counted state. -/
def Expect (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) (e : Event) : Prop :=
  ExpectD p L g dn.1 e

/-- **The softmax warps' reference invariant** at a counted state: the counts in closed form. -/
structure Ref (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop where
  counts : RefCounts p L g dn

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
