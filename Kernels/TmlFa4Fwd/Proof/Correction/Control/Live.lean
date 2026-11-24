-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.State

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control

/-! Control liveness at correction sites, obtained by walking the CFG backwards from its branch
guards, addresses, synchronization operands and scheduler collectives. For stores only their
address is needed. Each site proof checks its actual incoming and outgoing register facts.
An implicit load wait uses the live registers at the instruction after its load. -/

/-- Bitsets of the retained register ids, in blocks of 256. -/
def controlReg (r : Nat) : Bool :=
  let bits : Nat := match r / 256 with
    | 2 => 0x7c11f0000000004f820020000000000000000000000000000000000000000000
    | 3 => 0x2
    | 4 => 0x204000000000
    | 6 => 0x5407ffffffadf0000000000000000000
    | 9 => 0x8000000000000000000000000000000000004000000000000000000000
    | 22 => 0x9240100000000000000000000000000000000000000000000000000000000000
    | 23 => 0x40080000000000004124800
    | 24 => 0x100000000000000000000000
    | 25 => 0x200010000800042001840030800610000915fc00000000000000000000000
    | 26 => 0x100008000420018400308006100000002000100008000400020001000080004
    | 27 => 0x4300c009024900124800200002000100008000400020001000080004000200
    | 28 => 0xaffaf8000000000000000000000000
    | 29 => 0x4f0080000000000000000
    | 35 => 0x3d0000000
    | 37 => 0x2000000000000000002800000000000000
    | _ => 0
  bits.testBit (r % 256)

/-- Both scheduler passes, request selection and the role exit retain their strict facts. -/
def schedulerSite : Site → Bool
  | .setmax | .bar1 | .arr _ | .word _ | .down _ | .up _ _ | .total _ | .vote _
  | .pre _ | .tiles _ | .q0 | .q1 | .uk | .nb _ | .free | .wend _ | .barEnd _ | .exit _ => true
  | _ => false

noncomputable def liveAt (site : Site) : List Nat :=
  let pc := match site with
    | .rldw .. => site.pc + 1
    | _ => site.pc
  if schedulerSite site then Flow.live pc else (Flow.live pc).filter controlReg

end PTX.Kernels.TmlFa4Fwd.Proof.Correction.Control
