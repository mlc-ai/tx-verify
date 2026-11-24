-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape

@[expose] public section

/-! # The reference invariant and the expected values -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- What an event at a state must return for the reference invariant to continue. -/
def ExpectD (d : D) (e : Event) : Prop :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk => ∀ a bs, e.kind = .rd a bs → ∃ x, rebuild 3 bs = .ok (.bits 32 x)
  | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ =>
    ∀ md a b c v ok, e.kind = .shfl md a b c v ok → ∃ x, v = .bits 32 x
  | .rscale _ => ∀ a bs, e.kind = .rd a bs → ∃ s : Sc, rebuild 3 bs = .ok s.val
  | .fmax _ => ∀ a bs, e.kind = .rd a bs →
    ∃ x : EReal, x ≠ ⊤ ∧ rebuild 3 bs = .ok (Assumption.erealValue .f32 x)
  | .fsum _ => ∀ a bs, e.kind = .rd a bs → ∃ x : ℝ, rebuild 3 bs = .ok (fv x) ∧ 0 ≤ x
  | .rld _ _ => ∀ a vals sh, e.kind = .tc (.ld a vals sh) → (flN 16 vals).isSome
  | .fld _ _ => ∀ a vals sh, e.kind = .tc (.ld a vals sh) → (flN 8 vals).isSome
  | _ => True

/-- **The expected values** at a counted state. -/
def Expect (dn : D × (Cnt → Nat)) (e : Event) : Prop := ExpectD dn.1 e

/-- **The correction warps' reference invariant** at a counted state: the counts in closed form,
and the row sums nonnegative from their read to the LSE stores. -/
structure Ref (p : Params) (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) : Prop where
  counts : RefCounts p L g dn
  pos : ∀ st, rsPos st dn.1.site = true → 0 ≤ rsOf dn.1.v st

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
