-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixCopy
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- The loader's two physical vectors for any pair of its initial value packet. -/
def PrimingValueVector (X : Execution) (issue : EvId) (pair : Fin 16) (upper : Bool)
    (spec : AsyncCopy.Spec) :
    Prop :=
  X.get issue = some ⟨vCopyPc pair + if upper then 1 else 0, .copy spec⟩

theorem PrimingValueVector.copy {X : Execution} {issue : EvId} {pair : Fin 16} {upper : Bool}
    {spec : AsyncCopy.Spec} (h : PrimingValueVector X issue pair upper spec) : X.Copy issue spec :=
  ⟨_, h⟩

/-- The source of an issued value vector in an active CTA, even
if its copy effect has not executed yet. -/
theorem PrimingValueVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingValueVector X (g, j) pair upper spec) (hWarp : 14 ≤ warpIndex l g)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      let tid := g % l.block
      let row := kvCopyRow tile tid pair.val
      head < p.kvHeads ∧ spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      spec.src.loc = p.vLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) := by
  let lane := laneOf l g
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hg : g < l.threads := event_thread_lt hX h
  have hTid : 32 * warpIndex l g + lane = g % l.block := by
    unfold warpIndex lane laneOf
    omega
  have he : X.get (warpLane l g lane, j) =
      some ⟨vCopyPc pair + if upper then 1 else 0, .copy spec⟩ := by
    rw [hSelf]
    exact h
  obtain ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩ :=
    actualVCopySourceInPrefix hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA pair upper he
  rw [hTid] at hSize hLoc
  exact ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩

/-- The loader's two physical vectors for the first pair of its initial value packet. -/
def FirstPrimingValueVector (X : Execution) (issue : EvId) (upper : Bool) (spec : AsyncCopy.Spec) :
    Prop :=
  X.get issue = some ⟨vCopyPc 0 + if upper then 1 else 0, .copy spec⟩

theorem FirstPrimingValueVector.copy {X : Execution} {issue : EvId} {upper : Bool}
    {spec : AsyncCopy.Spec} (h : FirstPrimingValueVector X issue upper spec) : X.Copy issue spec :=
  ⟨_, h⟩

/-- The source of an issued first value vector in an active CTA, even
if its copy effect has not executed yet. -/
theorem FirstPrimingValueVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : FirstPrimingValueVector X (g, j) upper spec) (hWarp : 14 ≤ warpIndex l g)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let coords := assignedCoordinates p batch (g / l.block)
      let head := coords.2 / 6
      let tile := Mma.trips p batch coords.1 - 1
      let tid := g % l.block
      let row := kvCopyRow tile tid 0
      head < p.kvHeads ∧ spec.src.size = (if row < p.kLength batch then 16 else 0) ∧
      spec.src.loc = p.vLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) :=
  PrimingValueVector.source hp hX hFrame (pair := 0) h hWarp hCTA

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
