-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKLaterPrefixCopy
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

noncomputable section

/-- The loader's two physical vectors for the first pair of its initial key packet. -/
def FirstPrimingKeyVector (X : Execution) (issue : EvId) (upper : Bool) (spec : AsyncCopy.Spec) :
    Prop :=
  X.get issue = some ⟨kCopyPc 0 + if upper then 1 else 0, .copy spec⟩

theorem FirstPrimingKeyVector.copy {X : Execution} {issue : EvId} {upper : Bool}
    {spec : AsyncCopy.Spec} (h : FirstPrimingKeyVector X issue upper spec) : X.Copy issue spec :=
  ⟨_, h⟩

/-- The source of an issued first key vector in an active CTA, even
if its copy effect has not executed yet. -/
theorem FirstPrimingKeyVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : FirstPrimingKeyVector X (g, j) upper spec) (hWarp : 14 ≤ warpIndex l g)
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
      spec.src.loc = p.kLayout.loc (primingScratchPage p batch row)
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
  have he : X.get (warpLane l g lane, j) = some ⟨550 + if upper then 1 else 0, .copy spec⟩ := by
    rw [hSelf]
    exact h
  obtain ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩ :=
    actualFirstKCopySourceInPrefix hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA upper he
  rw [hTid] at hSize hLoc
  exact ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩

/-- A physical vector issued in the loader's initial key packet. -/
def PrimingKeyVector (X : Execution) (issue : EvId) (pair : Fin 16) (upper : Bool)
    (spec : AsyncCopy.Spec) : Prop :=
  X.get issue = some ⟨kCopyPc pair + if upper then 1 else 0, .copy spec⟩

theorem PrimingKeyVector.copy {X : Execution} {issue : EvId} {pair : Fin 16} {upper : Bool}
    {spec : AsyncCopy.Spec} (h : PrimingKeyVector X issue pair upper spec) :
    X.Copy issue spec := ⟨_, h⟩

/-- Recover the key-cache source through the actual issue, including partially observed pairs. -/
theorem PrimingKeyVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {pair : Fin 16} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : PrimingKeyVector X (g, j) pair upper spec) (hWarp : 14 ≤ warpIndex l g)
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
      spec.src.loc = p.kLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) := by
  by_cases hZero : pair = 0
  · subst pair
    exact FirstPrimingKeyVector.source hp hX hFrame h hWarp hCTA
  let lane := laneOf l g
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hLocal := Nat.mod_le g l.block
    have hLaneLe := Nat.mod_le (g % l.block) 32
    omega
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hg : g < l.threads := event_thread_lt hX h
  have hTid : 32 * warpIndex l g + lane = g % l.block := by unfold warpIndex lane laneOf; omega
  have hPositive : 0 < pair.val := by
    by_contra! hP
    exact hZero (Fin.ext (by omega))
  let i : Fin 15 := ⟨pair.val - 1, by have := pair.isLt; omega⟩
  have hPair : primingKLaterPair i = pair := Fin.ext (by
    change pair.val - 1 + 1 = pair.val
    omega)
  have he : X.get (warpLane l g lane, j) =
      some ⟨kCopyPc (primingKLaterPair i) + if upper then 1 else 0, .copy spec⟩ := by
    rw [hSelf, hPair]
    exact h
  obtain ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩ :=
    actualLaterKCopySourceInPrefix hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA i upper he
  rw [hTid, hPair] at hSize hLoc
  exact ⟨batch, hb, hLo, hHi, hh, hSize, hLoc⟩

/-- A physical vector issued in the first half of the loader's initial key packet. -/
def FirstHalfPrimingKeyVector (X : Execution) (issue : EvId) (pair : Fin 8) (upper : Bool)
    (spec : AsyncCopy.Spec) : Prop :=
  X.get issue = some ⟨kCopyPc (pair.castLE (by decide)) + if upper then 1 else 0, .copy spec⟩

theorem FirstHalfPrimingKeyVector.copy {X : Execution} {issue : EvId} {pair : Fin 8} {upper : Bool}
    {spec : AsyncCopy.Spec} (h : FirstHalfPrimingKeyVector X issue pair upper spec) :
    X.Copy issue spec := ⟨_, h⟩

/-- Recover the key-cache source through the actual issue, including partially observed pairs. -/
theorem FirstHalfPrimingKeyVector.source {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g j : Nat} {pair : Fin 8} {upper : Bool} {spec : AsyncCopy.Spec}
    (h : FirstHalfPrimingKeyVector X (g, j) pair upper spec) (hWarp : 14 ≤ warpIndex l g)
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
      spec.src.loc = p.kLayout.loc (primingScratchPage p batch row)
        head (row % 16) (kvCopyColumn tid upper) :=
  PrimingKeyVector.source hp hX hFrame (pair := pair.castLE (by decide)) h hWarp hCTA

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
