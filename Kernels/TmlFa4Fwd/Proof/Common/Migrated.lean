-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src

@[expose] public section

/-! # The migrated roles' lanes are followed

`good_migrated`: for every consistent execution under the launch's premises, every lane of the
correction warps (8 to 11), the MMA warp (12) and the output warp (13) is followed by the thread
machine and holds its role's reference invariant (`RefAll`); `good_all` adds the loader warps (14
and 15). The correction warps' statistics
reads and Tensor Memory loads are the premise `CorrWarp.DataSrc`, which the softmax fragment and
the Tensor Memory protocol discharge. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The reference invariant of the migrated roles' warps. -/
def RefAll (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Prop :=
  if Prologue.warpIndex L g = 12 then Mma.Ref p L g σ
  else if Prologue.warpIndex L g = 13 then Epilogue.Ref p L g σ
  else if Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15 then
    LdWarp.Ref p L (Prologue.warpIndex L g) g σ
  else CorrWarp.Ref p L (Prologue.warpIndex L g) g σ

/-- **Every lane of warps 8 to 13 is followed, and its states hold the reference invariant of its
role.** -/
theorem good_migrated (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hw : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 13) (k : Nat) :
    Frame.FollowedAt (thread p L) (RefAll p L) X g k := by
  have hReads := cuQReadsFromLaunch hp hX
  by_cases h12 : Prologue.warpIndex L g = 12
  · obtain ⟨h1, h2⟩ := Mma.good hp hX hReads hg h12 k
    exact ⟨h1, fun σ hσ => by simpa [RefAll, h12] using h2 σ hσ⟩
  by_cases h13 : Prologue.warpIndex L g = 13
  · obtain ⟨h1, h2⟩ := Epilogue.good hp hX hReads hg h13 k
    exact ⟨h1, fun σ hσ => by simpa [RefAll, h13] using h2 σ hσ⟩
  · have h14 : ¬ (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) := by omega
    obtain ⟨h1, h2⟩ := CorrWarp.good hp hX (by omega) hg rfl k
    exact ⟨h1, fun σ hσ => by simpa [RefAll, h12, h13, h14] using h2 σ hσ⟩

/-- **Every lane of warps 8 to 15 is followed, and its states hold the reference invariant of its
role**. -/
theorem good_all (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads)
    (hw : 8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 15) (k : Nat) :
    Frame.FollowedAt (thread p L) (RefAll p L) X g k := by
  by_cases h14 : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15
  · have h12 : Prologue.warpIndex L g ≠ 12 := by omega
    have h13 : Prologue.warpIndex L g ≠ 13 := by omega
    obtain ⟨h1, h2⟩ := LdWarp.good hp hX h14 hg rfl k
    exact ⟨h1, fun σ hσ => by simpa [RefAll, h12, h13, h14] using h2 σ hσ⟩
  · exact good_migrated hp hX hg (by omega) k

end
end PTX.Kernels.TmlFa4Fwd.Proof
