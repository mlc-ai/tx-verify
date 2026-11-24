-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingKeyPrefix
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingValuePrefix
public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyCursorContinue
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Loader
  (actualCopyAtInLoader loaderCopyPcInPacket packetCopyCoordinates packetPlanePc
    primingPacketSite recurringPacketSite kCopyPc vCopyPc)

/-- An actual ordinary cache copy belongs to one of the two initial packets or
to a recurring packet. The occurrence may be pending in the current prefix. -/
theorem copyPrimingOrRecurringVector {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {copy : EvId} {spec : AsyncCopy.Spec}
    (hCopy : X.Copy copy spec) :
    (∃ (pair : Fin 16) (upper : Bool), PrimingKeyVector X copy pair upper spec) ∨
    (∃ (pair : Fin 16) (upper : Bool), PrimingValueVector X copy pair upper spec) ∨
    ∃ e, X.get copy = some e ∧ recurringVectorEvent e ∧ e.kind = .copy spec := by
  obtain ⟨g,index⟩ := copy
  obtain ⟨pc,he⟩ := hCopy
  obtain ⟨hLo,hHi,hOrdinary⟩ := actualCopyAtInLoader hX he
  obtain ⟨packet,hFirst,hLast⟩ := loaderCopyPcInPacket hLo hHi hOrdinary
  obtain ⟨pair,upper,rfl⟩ := packetCopyCoordinates packet hFirst hLast hOrdinary
  rcases Nat.lt_or_ge packet.val 2 with hPriming | hRecurring
  · let slot : Fin 2 := ⟨packet.val,hPriming⟩
    have hPacket : packet = primingPacketSite slot := Fin.ext rfl
    rw [hPacket] at he
    have hSmall : ∀ q : Fin 2, q = 0 ∨ q = 1 := by decide
    rcases hSmall slot with hZero | hOne
    · have hPc : packetPlanePc (primingPacketSite 0) pair upper =
          kCopyPc pair + (if upper then 1 else 0) := by
        fin_cases pair <;> cases upper <;> decide
      rw [hZero, hPc] at he
      exact .inl ⟨pair,upper,he⟩
    · have hPc : packetPlanePc (primingPacketSite 1) pair upper =
          vCopyPc pair + (if upper then 1 else 0) := by
        fin_cases pair <;> cases upper <;> decide
      rw [hOne, hPc] at he
      exact .inr (.inl ⟨pair,upper,he⟩)
  · let site : Fin 4 := ⟨packet.val-2,by have := packet.isLt; omega⟩
    have hPacket : packet = recurringPacketSite site := Fin.ext (by
      change packet.val = (packet.val-2)+2
      omega)
    rw [hPacket] at he
    exact .inr (.inr ⟨_,he,⟨site,pair,upper,spec,rfl⟩,rfl⟩)

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
