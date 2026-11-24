-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Data.Barriers

@[expose] public section

/-! # The kernel's synchronization objects, by role

The protocol layer names the 23 mbarriers and the named CTA barriers by their role rather than by
their shared byte offset. The offsets and counts are `Data/Barriers.mbars` / `namedBars`, checked
against the decoded initialization instructions. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol

open PTX

/-- The two double-buffered KV slots and the four index slots. -/
inductive Mbar where
  | lastStore
  | qTma
  | qUtccp
  | dequantReady (buf : Fin 2)
  | rawReady (buf : Fin 2)
  | rawFree (buf : Fin 2)
  | qkDone (buf : Fin 2)
  | soReady (buf : Fin 2)
  | svDone (buf : Fin 2)
  | validReady (slot : Fin 4)
  | validFree (slot : Fin 4)
  deriving DecidableEq, Repr

/-- The shared byte offset of the object. -/
def Mbar.off : Mbar → Nat
  | .lastStore => 222768
  | .qTma => 222776
  | .qUtccp => 222784
  | .dequantReady b => if b.val = 0 then 222792 else 222800
  | .rawReady b => if b.val = 0 then 222808 else 222816
  | .rawFree b => if b.val = 0 then 222824 else 222832
  | .qkDone b => if b.val = 0 then 222904 else 222912
  | .soReady b => if b.val = 0 then 222920 else 222928
  | .svDone b => 222936 + 8 * b.val
  | .validReady s => 222840 + 8 * s.val
  | .validFree s => 222872 + 8 * s.val

/-- The expected arrival count of the object. -/
def Mbar.count : Mbar → Nat
  | .lastStore => 128
  | .qTma => 1
  | .qUtccp => 1
  | .dequantReady _ => 128
  | .rawReady _ => 1
  | .rawFree _ => 128
  | .qkDone _ => 1
  | .soReady _ => 128
  | .svDone _ => 1
  | .validReady _ => 32
  | .validFree _ => 129

/-- Every mbarrier object, for the audit against `Data/Barriers.mbars`. -/
def Mbar.all : List Mbar :=
  [.lastStore, .qTma, .qUtccp, .dequantReady 0, .dequantReady 1, .rawReady 0, .rawReady 1,
    .rawFree 0, .rawFree 1, .qkDone 0, .qkDone 1, .soReady 0, .soReady 1, .svDone 0, .svDone 1,
    .validReady 0, .validReady 1, .validReady 2, .validReady 3, .validFree 0, .validFree 1,
    .validFree 2, .validFree 3]

/-- The named CTA barriers used by the kernel. -/
inductive NBar where
  | wg0
  | warpPair (half : Fin 2)
  | everyone
  deriving DecidableEq, Repr

/-- The PTX barrier id. -/
def NBar.id : NBar → Nat
  | .wg0 => 9
  | .warpPair h => 10 + h.val
  | .everyone => 12

/-- The participant count. -/
def NBar.count : NBar → Nat
  | .wg0 => 128
  | .warpPair _ => 64
  | .everyone => 384

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol
