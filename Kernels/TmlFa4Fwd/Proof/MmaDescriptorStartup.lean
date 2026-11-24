-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part029
public import Kernels.TmlFa4Fwd.Flow.Code.Part030

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

/-- The low descriptor word initially points to the second Q stage. -/
def startupQLow (l : Launch) : Nat := (l.sharedBase + 35840) / 16 + 65536

private theorem startField {a : Nat} (hAlign : a % 1024 = 0) (hBound : a < 2 ^ 18) :
    a / 16 &&& 16320 = a / 16 := by
  have hEq : a / 16 = (a / 1024) <<< 6 := by
    rw [Nat.shiftLeft_eq]
    omega
  rw [hEq, show (16320 : Nat) = 255 <<< 6 by rfl, ← Nat.shiftLeft_and_distrib]
  have h : a / 1024 < 2 ^ 8 := by omega
  rw [show (255 : Nat) = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_of_lt_two_pow h]

/-- The four local operations compute the broadcast's Q descriptor operand. -/
theorem startupQWord {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 4 1912 [(2535, b32 l.sharedBase)] 1916 [(2455, b32 (startupQLow l))] := by
  have hBound := hp.shared.2.1
  have hAlign := hp.shared.1
  have hMask := startField (a := l.sharedBase + 35840) (by omega) (by omega)
  have hOr : (l.sharedBase + 35840) / 16 ||| 65536 =
      (l.sharedBase + 35840) / 16 + 65536 := by
    have hl : (l.sharedBase + 35840) / 16 < 2 ^ 16 := by omega
    rw [Nat.or_comm, show (65536 : Nat) = 2 ^ 16 * 1 by rfl,
      ← Nat.two_pow_add_eq_or_of_lt hl, Nat.mul_one, Nat.add_comm]
  have h0 : l.sharedBase < 4294967296 := by omega
  have h1 : l.sharedBase + 35840 < 4294967296 := by omega
  have h2 : (l.sharedBase + 35840) / 16 < 4294967296 := by omega
  intro t ht
  seg_fp ht using
    (unfold startupQLow
     nf_simp
     simp only [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, hMask, hOr])

/-- PC 1916 is the full-warp lane-zero broadcast of the assembled low word. -/
theorem startupQShuffle {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {t : TState} (ht : At t 1916 [(2455, b32 (startupQLow l))]) :
    out kernel Assumptions.all l g t = .ev (.shfl .idx (b32 (startupQLow l)) 0 31
      (fun v _ => next (setReg t 2450 v))) := by
  rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
    out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_1916) rfl rfl]
  change Out.ev (shflTmpl l g t .idx 2450 none (.reg 2455) (.imm 0)
    (.imm 31) (.imm (-1))) = _
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  simp [shflTmpl, readValue, readReg, ht.2.2.2.2.1, hBlock, Value.bytes, b32, readBits,
    pure, Except.pure]
  rfl

end PTX.Kernels.TmlFa4Fwd.Mma
