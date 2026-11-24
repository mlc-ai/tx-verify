-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles

@[expose] public section

/-! # A role's state and counts as the thread machine's

The roles' states with their counts, as states of the thread machine, and a role's counts out of the
thread's ledger. A theorem that places a lane at a role's state reads these, not the role's
reference invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

/-- The MMA classes of the thread's ledger: the role's counts. -/
abbrev rc (n : Cls → Nat) : Cnt → Nat := fun c => n (.mma c)

/-- The MMA warp's state `d` with the counts `n` as a state of the thread machine. -/
abbrev minj (p : Params) (L : Launch) (g : Nat) (d : D) (n : Cls → Nat) : (thread p L g).D :=
  (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n)

end PTX.Kernels.TmlFa4Fwd.Proof.Mma

namespace PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Correction

/-- The correction classes of the thread's ledger: the role's counts. -/
abbrev rc (n : Cls → Nat) : Cnt → Nat := fun c => n (.corr c)

/-- The correction state `d` with the counts `n` as a state of the thread machine. -/
abbrev cinj (p : Params) (L : Launch) (g : Nat) (d : Control.D) (n : Cls → Nat) :
    (thread p L g).D :=
  (.inr ⟨.correction, d⟩, n)

end PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp

namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax

/-- The softmax state `d` with the counts `n` as a state of the thread machine. -/
abbrev sinj (p : Params) (L : Launch) (g : Nat) (d : Control.D) (n : Cls → Nat) :
    (thread p L g).D :=
  (.inr ⟨.softmax, d⟩, n)

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

/-- The loader classes of the thread's ledger: the role's counts. -/
abbrev lcn (n : Cls → Nat) : Cnt → Nat := fun c => n (.load c)

/-- The loader state `d` of fragment `b` with the counts `n` as a state of the thread machine. -/
abbrev linj (p : Params) (L : Launch) (g : Nat) (b : Bool) (d : D) (n : Cls → Nat) :
    (thread p L g).D :=
  (.inr ⟨.loader b, d⟩, n)

end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
