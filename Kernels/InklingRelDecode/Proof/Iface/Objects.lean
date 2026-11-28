-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

def kvReady (slot : Fin 3) : Nat := 213216 + 8 * slot.val
def kvEmpty (slot : Fin 3) : Nat := 213248 + 8 * slot.val
def sReady (slot : Fin 2) : Nat := 213280 + 8 * slot.val
def pReady (slot : Fin 2) : Nat := 213296 + 8 * slot.val
def oDone : Nat := 213312
def oFinal : Nat := 213328

def ctaBarrier : Nat := 0
def namedBarrier : Nat := 1

end PTX.Kernels.InklingRelDecode.Proof.Iface
