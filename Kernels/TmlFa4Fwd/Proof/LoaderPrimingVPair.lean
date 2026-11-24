-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVFirstCopy
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue AsyncCopy

noncomputable section

/-- The first V pair sets the byte column offset. After that all pairs share the
same two shuffles and two address instructions. -/
def vPacketShufflePc (pair : Fin 16) : Nat :=
  vCopyPc pair - if pair.val = 0 then 5 else 4

def vPacketSlot (pair : Fin 16) : Fin 2 :=
  ⟨pair.val / 8, by have := pair.isLt; omega⟩

def vPacketSelect (pair : Fin 16) : Nat := pair.val % 8

def vPacketShflLow (pair : Fin 16) : Nat :=
  if pair.val < 8 then 1929 + 2 * pair.val else 1947 + 2 * (pair.val - 8)

def vPacketShflDst (pair : Fin 16) (word : Fin 2) : Nat := vPacketShflLow pair + word.val

def vPacketShflSrc (pair : Fin 16) (word : Fin 2) : Nat :=
  (primingVPointerReload (vPacketSlot pair)).lowReg + word.val

theorem vPacketShuffleCode (pair : Fin 16) (word : Fin 2) :
    kernel.code[vPacketShufflePc pair + word.val]? = some ⟨none, .warp
      { kind := .shfl .idx, ty := some (.int .b 32), dsts := [some (vPacketShflDst pair word)],
        srcs := [.reg (vPacketShflSrc pair word), .imm (vPacketSelect pair), .imm 6175],
        mask := some (.imm (-1)) }⟩ := by
  fin_cases pair <;> fin_cases word <;> (set_option maxRecDepth 100000 in kernel_rfl)

def primingVPacketFrame (l : Launch) (tid residual : Nat) (bytes : Fin 16 → Nat) :
    List (Nat × Value) :=
  [(7292, b64 l.localBase), (1089, b32 residual), (1082, b32 (kvCopyColumn tid false)),
   (1083, b32 (kvCopyAddress l.sharedBase 0 tid 0 false)),
   (1084, b32 (kvCopyAddress l.sharedBase 0 tid 1 false))] ++
    (List.finRange 16).map fun pair => (vCopyByteReg pair, b32 (bytes pair))

def primingVColumn (tid : Nat) : Nat × Value := (7611, b64 (2 * kvCopyColumn tid false))

/-- The second broadcast takes the upper half of its loaded pointer. -/
theorem vPacketSrcHi (pair : Fin 16) :
    vPacketShflSrc pair 1 = (primingVPointerReload (vPacketSlot pair)).highReg := by
  fin_cases pair <;> rfl

def vPacketSender (pair : Fin 16) (lane : Nat) : Nat :=
  pointerBroadcastLane lane + vPacketSelect pair

theorem vPacketSender_lt (pair : Fin 16) {lane : Nat} (hl : lane < 32) :
    vPacketSender pair lane < 32 := by
  have h := Nat.mod_lt pair.val (by decide : 0 < 8)
  unfold vPacketSender pointerBroadcastLane vPacketSelect
  omega

def vPacketAddrInputs (pair : Fin 16) (base tid : Nat) : List (Nat × Value) :=
  [(vPacketShflDst pair 0, b32 (base % 2 ^ 32)), (vPacketShflDst pair 1, b32 (base / 2 ^ 32)),
   if pair.val = 0 then (1082, b32 (kvCopyColumn tid false)) else primingVColumn tid]

theorem vPacketAddress (l : Launch) (g : Nat) (pair : Fin 16) {base tid : Nat}
    (hBase : base < 2 ^ 64) :
    Seg kernel [] l g (if pair.val = 0 then 3 else 2) (vPacketShufflePc pair + 2)
      (vPacketAddrInputs pair base tid) (vCopyPc pair)
      [(vCopySrcReg pair, b64 ((base + 2 * kvCopyColumn tid false) % 2 ^ 64)),
       primingVColumn tid] := by
  have hLo : base % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hShift : base / 4294967296 * 4294967296 < 18446744073709551616 := by omega
  have hColumn : kvCopyColumn tid false < 2 ^ 32 := by
    have := Nat.mod_lt tid (by decide : 0 < 8)
    simp [kvCopyColumn]
    omega
  have hJoin : (base % 4294967296 ||| base / 4294967296 * 4294967296 %
      18446744073709551616) = base := by
    rw [Nat.mod_eq_of_lt hShift, Nat.or_comm, Nat.mul_comm]
    change 2 ^ 32 * (base / 2 ^ 32) ||| base % 2 ^ 32 = base
    rw [← Nat.two_pow_add_eq_or_of_lt hLo]
    omega
  fin_cases pair <;> intro t ht <;>
    simp only [vPacketAddrInputs, primingVColumn, vPacketShflDst, vPacketShflLow,
      Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
      Nat.reduceSub] at ht ⊢ <;>
    seg_fp ht using norm_bits [hJoin, Nat.mod_eq_of_lt hColumn]

def vPacketAddressCount (pair : Fin 16) : Nat := if pair.val = 0 then 3 else 2

def vPacketColumnInput (pair : Fin 16) (tid : Nat) : Nat × Value :=
  if pair.val = 0 then (1082, b32 (kvCopyColumn tid false)) else primingVColumn tid

def vPacketResultFrame (pair : Fin 16) (base tid : Nat) (F : List (Nat × Value)) :
    List (Nat × Value) :=
  primingVColumn tid :: primingVReloadWords (vPacketSlot pair) base ++ F

def vPacketCopySpec (l : Launch) (g tid base bytes : Nat)
    (pair : Fin 16) (upper : Bool) : AsyncCopy.Spec :=
  vCopySpec l g tid ((base + 2 * kvCopyColumn tid false) % 2 ^ 64) bytes pair upper

/-- Caller facts carried by one decoded vector pair. -/
structure PrimingVPairFrame (l : Launch) (pair : Fin 16) (base tid bytes : Nat)
    (F : List (Nat × Value)) : Prop where
  column : vPacketColumnInput pair tid ∈ F
  destination : (vCopyDstReg pair, b32 (kvCopyAddress l.sharedBase 0 tid (pair.val % 2) false)) ∈ F
  count : (vCopyByteReg pair, b32 bytes) ∈ F
  shuffles : ∀ fact ∈ F, fact.1 ≠ vPacketShflDst pair 0 ∧ fact.1 ≠ vPacketShflDst pair 1
  preserved : ((kernel.code.drop (vPacketShufflePc pair + 2)).take (vPacketAddressCount pair)).all
    (fun ins => ((primingVReloadWords (vPacketSlot pair) base ++ F).map Prod.fst).all
      (fun r => !(writesRegs ins.op).contains r)) = true

end
end PTX.Kernels.TmlFa4Fwd.Loader
