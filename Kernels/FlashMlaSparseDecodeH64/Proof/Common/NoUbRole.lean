-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.NoUbId

@[expose] public section

/-! # The role of a state of the thread machine, by constructor

`InRole P L g r σ`: the thread machine's state `σ` is a state of role `r` (the startup, warpgroup
1's head and idle code, the MMA, TMA and index warps, warpgroups 2 and 0). It is the body of
`AliveIn` (`Common/NoUbView.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- The role a state of the thread machine is in. -/
inductive InRole (P : Params) (L : Launch) (g : Nat) :
    RoleId → (thread P L g).D → Prop
  | startup (d : (startupCode P L g).D) (n : Cls → Nat) : InRole P L g .startup (.inl d, n)
  | head (s : Wg1.Site) (n : Cls → Nat) :
      InRole P L g .wg1 (.inr ⟨.inl .wg1, .inl s⟩, n)
  | idle (s : IdleSite) (n : Cls → Nat) :
      InRole P L g .wg1 (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, s⟩⟩, n)
  | mma (d : (mmaCode P L g).D) (n : Cls → Nat) :
      InRole P L g .mma (.inr ⟨.inl .wg1, .inr ⟨.inl .mma, d⟩⟩, n)
  | tma (d : (tmaCode P L g).D) (n : Cls → Nat) :
      InRole P L g .tma (.inr ⟨.inl .wg1, .inr ⟨.inl .tma, d⟩⟩, n)
  | index (d : (indexCode P L g).D) (n : Cls → Nat) :
      InRole P L g .index (.inr ⟨.inl .wg1, .inr ⟨.inl .index, d⟩⟩, n)
  | dequant (d : (dequantCode P L g (warpW L g)).D) (n : Cls → Nat) :
      InRole P L g .dequant (.inr ⟨.inl .dequant, d⟩, n)
  | wg0 (d : (wg0Code P L g (warpW L g)).D) (n : Cls → Nat) :
      InRole P L g .wg0 (.inr ⟨.inl .wg0, d⟩, n)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
