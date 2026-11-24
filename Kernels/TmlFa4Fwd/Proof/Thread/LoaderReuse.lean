-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReuseCheckpoint
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Loader (reuseArrival actualRecurringGuard)

/-- An actual publication while the loader rotates through the K/V ring. -/
def RecurringPublication (X : Execution) (publication : EvId) (loc : Loc) : Prop :=
  ∃ site : Fin 4, X.get publication = some ⟨reuseArrival site, .asyncArrive loc true⟩

/-- The last copy of a recurring publication is guarded by the same slot's empty acquire. -/
structure GuardedReuse (l : Launch) (X : Execution) (publication : EvId) (slot : Fin 3) where
  acquire : EvId
  copy : EvId
  parity : Nat
  empty : EmptyAcquire l X acquire slot parity
  guarded : Resumes kernel X acquire copy
  tracked : TracksCpAsync X copy publication

/-- Recover the actual local reuse witnesses from a recurring publication. -/
theorem recurringGuard {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner : Nat} {publication : EvId} {slot : Fin 3}
    (hPub : RecurringPublication X publication (readyObject l owner slot)) :
    Nonempty (GuardedReuse l X publication slot) := by
  obtain ⟨g, index⟩ := publication
  obtain ⟨site, he⟩ := hPub
  obtain ⟨stage, phase, wait, copy, hLoc, hWait, hGuard, hTrack⟩ :=
    actualRecurringGuard hp hX site he
  have hAddr := congrArg Loc.addr hLoc
  change (Prologue.initObject l (owner / l.block) (Loader.readySlot slot)).addr =
    (Prologue.initObject l (g / l.block) (Loader.readySlot stage)).addr at hAddr
  rw [Loader.readySlot_address, Loader.readySlot_address] at hAddr
  simp only at hAddr
  have hSlot : slot = stage := Fin.ext (by omega)
  subst stage
  exact ⟨⟨(g, wait), (g, copy), phase, ⟨_, hWait, rfl⟩, hGuard, hTrack⟩⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
