-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CachePublicationOutput
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedCacheBank
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaObservedValueBank
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyStaging
import Kernels.TmlFa4Fwd.Proof.Protocol.InitialValueStaging
import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaKeyReleaseDescriptor
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFinalCacheUseOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX Mma

/-- At any physical ring slot, the eight canonical QK B footprints
cover every byte of an ordinary loader vector. -/
theorem keyVectorHasOperandCoordinate (l : Launch) (g : Nat) (block : Fin 4) (slot : Fin 3)
    (lane : Fin 64) (pair : Fin 16) (upper : Bool)
    (hBase : l.sharedBase % 1024 = 0) {off : Nat} (hOff : off < 16) :
    ∃ step : Fin 8, ∃ index,
      (qkOperands l g block step slot.val).byteLoc .b index =
        some ⟨.shared, g / l.block, kvCopyAddress l.sharedBase slot lane pair upper + off⟩ := by
  obtain ⟨step, row, k, byte, hr, hk, hb, hCoords⟩ :=
    initialKeyByteOfVector l (g / l.block) lane pair upper hOff
  have hAddr := congrArg Loc.addr hCoords
  change kvCopyAddress l.sharedBase 0 (qkLoaderLane step row k) (row / 8)
    (decide (4 ≤ step.val)) + qkLoaderByte step k byte =
      kvCopyAddress l.sharedBase 0 lane pair upper + off at hAddr
  refine ⟨step, qkByteIndex row k byte, ?_⟩
  rw [qkKCopyByteLoc l g block step slot.val hBase hr hk hb]
  simp only [kvSlot, Nat.mod_eq_of_lt slot.isLt, Option.some.injEq, Loc.mk.injEq, true_and]
  unfold kvCopyAddress at hAddr ⊢
  omega

/-- At any physical ring slot, the eight canonical PV B footprints
cover every byte of an ordinary loader vector. -/
theorem valueVectorHasOperandCoordinate (l : Launch) (g : Nat) (block : Fin 4) (slot : Fin 3)
    (lane : Fin 64) (pair : Fin 16) (upper : Bool)
    (hBase : l.sharedBase % 1024 = 0) {off : Nat} (hOff : off < 16) :
    ∃ step : Fin 8, ∃ index,
      (pvOperands l g block step slot.val).byteLoc .b index =
        some ⟨.shared, g / l.block, kvCopyAddress l.sharedBase slot lane pair upper + off⟩ := by
  obtain ⟨step, col, k, byte, hc, hk, hb, hCoords⟩ :=
    initialValueByteOfVector l (g / l.block) lane pair upper hOff
  have hAddr := congrArg Loc.addr hCoords
  let key := pvKeyRow step k
  change kvCopyAddress l.sharedBase 1 (8 * (key % 8) + (col % 64) / 8)
    (key / 8) (decide (64 ≤ col)) + 2 * (col % 8) + byte =
      kvCopyAddress l.sharedBase 1 lane pair upper + off at hAddr
  refine ⟨step, qkByteIndex col k byte, ?_⟩
  rw [pvValueByteLoc l g block step slot.val hBase hc hk hb]
  simp only [kvSlot, Nat.mod_eq_of_lt slot.isLt, Option.some.injEq, Loc.mk.injEq, true_and]
  unfold kvCopyAddress at hAddr ⊢
  dsimp only [key] at hAddr
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Each vector byte at the matched slot of an issued recurring key release is
read by a concrete fragment of that bank, even while the notification is pending. -/
theorem recurringKeyVectorReadOfMatch {g release : Nat} {form : Thread.Mma.ReleaseForm}
    {target : Loc} {spec : TcCommit.Spec} (hIssue : Thread.Mma.ReleaseIssue X g release form spec)
    (matched : Thread.Mma.ReleaseMatch l X g release form target) (hKind : form = .loopKey)
    (stage : Fin 2) (lane : Fin 64) (pair : Fin 16) (upper : Bool) {off : Nat} (hOff : off < 16) :
    ∃ (step : Fin 8) (i d index : Nat) (op : TcMma.OperandSpec) (accum : Bool)
        (mask : List Nat),
      Thread.QkInstruction X (g,i) (recurringKeyBlock stage) step d op accum mask ∧
      TraceBefore X (g,matched.wait) (g,i) ∧ TraceBefore X (g,i) (g,release) ∧
      op.byteLoc .b index =
        some ⟨.shared,g/l.block,kvCopyAddress l.sharedBase matched.slot lane pair upper + off⟩ := by
  obtain ⟨step,index,hCoord⟩ := keyVectorHasOperandCoordinate l g
    (recurringKeyBlock stage) matched.slot lane pair upper hp.shared.1 hOff
  obtain ⟨start,hBank⟩ := Thread.Mma.recurringKeyBankOfMatch hp hX hIssue matched hKind stage
  obtain ⟨d,op,accum,mask,hKey,hAfter,hBefore⟩ := hBank step
  have hB := Thread.Mma.recurringKeyDescriptorOfReleaseMatch hp hX stage hKey matched
    hKind hAfter hBefore
  have hQ := hKey.queryOperand hp hX
  have hSame : op.byteLoc .b index =
      (qkOperands l g (recurringKeyBlock stage) step matched.slot.val).byteLoc .b index := by
    simp only [TcMma.OperandSpec.byteLoc, qkOperands, hQ.descriptor, hQ.ctaLow, hQ.ctaHigh,
      hB, reduceCtorEq, false_and, ↓reduceIte]
    rfl
  exact ⟨step,start+step.val,d,index,op,accum,mask,hKey,hAfter,hBefore,hSame.trans hCoord⟩

/-- Each vector byte at a delivered recurring key release's slot is read by a
concrete fragment of that release's bank, even before any final output commit. -/
theorem recurringKeyVectorReadOfRelease {owner g position : Nat} {slot : Fin 3}
    (release : Thread.Mma.EmptyReleaseAt l X
      (Thread.Mma.Observation.emptyObject l owner slot) g position)
    (hKind : release.form = .loopKey) (stage : Fin 2) (lane : Fin 64) (pair : Fin 16) (upper : Bool)
    {off : Nat} (hOff : off < 16) :
    ∃ (step : Fin 8) (i d index : Nat) (op : TcMma.OperandSpec) (accum : Bool)
        (mask : List Nat),
      Thread.QkInstruction X (g,i) (recurringKeyBlock stage) step d op accum mask ∧
      TraceBefore X (g,release.matched.wait) (g,i) ∧ TraceBefore X (g,i) (g,release.index) ∧
      op.byteLoc .b index =
        some ⟨.shared,g/l.block,kvCopyAddress l.sharedBase slot lane pair upper + off⟩ := by
  simpa only [release.matchedSlot] using
    recurringKeyVectorReadOfMatch hp hX release.issue release.matched hKind stage
      lane pair upper hOff

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
