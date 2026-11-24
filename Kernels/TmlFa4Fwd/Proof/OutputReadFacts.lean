-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Barriers
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputFallbackCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainAddressClass
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCuQReadClass
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputFallbackCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputDrainCuQReadClass
import all Kernels.TmlFa4Fwd.Proof.Thread.OutputLaterDrainCuQReadClass

@[expose] public section

/-! # The output warp's CuQ reads, for the upper layers

Every read at an output pc reads the word of a cumulative query offset of the batch: it is a
read of a lane of warp 13 after its prologue (`Proof2.Epilogue.output_event`), and the
machine's read addresses are such words (`Proof2.Epilogue.read_addr`). -/

namespace PTX.Kernels.TmlFa4Fwd.OutputWarp
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A read at an output pc reads the word of a cumulative query offset of the batch. -/
theorem readAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g, j) = some ⟨pc, .rd a bytes⟩) (hlo : 2768 ≤ pc) (hhi : pc < 3099) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} := by
  obtain ⟨hw, hj5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX he hlo hhi
    (by rintro _ _ ⟨⟩)
  obtain ⟨i, hi, rfl⟩ := Proof2.Epilogue.read_addr hp hX hw hj5 he
  exact ⟨i, hi, rfl⟩

/-- The output warp's fallback lookups read words of the batch's cumulative query offsets. -/
theorem fallbackAddresses (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    Thread.OutputFallbackAddresses p X := by
  rintro ⟨g, j⟩ a bytes h
  exact readAddress hp hX h (by decide) (by decide)

/-- The output warp's later drain lookups read words of the batch's cumulative query
offsets. -/
theorem laterDrainAddresses (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) :
    Thread.OutputLaterDrainAddresses p X := by
  rintro ⟨g, j⟩ a bytes h
  exact readAddress hp hX h (by decide) (by decide)

/-- The chosen request's two lookups read words of the batch's cumulative query offsets. -/
theorem cuQReadWord (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {i : EvId}
    {a : Acc} {bytes : List (Option Byte)} (h : Thread.OutputCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} := by
  obtain ⟨g, j⟩ := i
  obtain ⟨endpoint, he⟩ := h
  exact readAddress hp hX he (by have := endpoint.isLt; omega) (by have := endpoint.isLt; omega)

/-- The first drain lookup reads a word of the batch's cumulative query offsets. -/
theorem drainCuQReadWord (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {a : Acc} {bytes : List (Option Byte)} (h : Thread.OutputDrainCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase + 4 * index), size := 4} := by
  obtain ⟨g, j⟩ := i
  exact readAddress hp hX h (by decide) (by decide)

end
end PTX.Kernels.TmlFa4Fwd.OutputWarp
