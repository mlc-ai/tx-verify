-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Quiet.Base
public import Lemmas.Kernel.StoreDrain

@[expose] public section

/-! # The store-drain constraint under quiet extensions and at an exit

`TensorStore.ReadsDrainedBeforeExit` (the `wf` of a store-drain assumption) survives every quiet
extension (`ReadsDrainedBeforeExit.quietExt`): such an extension appends no exit, so each exit of
the extension is an old exit, and the stores before it are old stores whose read completion stays
performed. Appending an exit keeps it when the thread's selected stores have finished reading
(`TensorStore.Drained`, `ReadsDrainedBeforeExit.snoc_exit`). -/

namespace PTX

variable {select : Nat → Bool} {X Y : Execution}

/-- **The selected stores of thread `g` have finished reading their shared source.** -/
def TensorStore.Drained (select : Nat → Bool) (X : Execution) (g : Nat) : Prop :=
  ∀ i, i.1 = g → TensorStore.Selected select X i → X.AsyncPresent i .readsDone

/-- An event of a monotone extension at an old position is the old event. -/
theorem Execution.le_get_of_lt (hle : X.le Y) {e : EvId} (he : e.2 < (X.tr e.1).length) :
    Y.get e = X.get e := by
  obtain ⟨suffix, hs⟩ := hle.1 e.1
  unfold Execution.get
  rw [← hs, List.getElem?_append_left he]

/-- **The drain constraint survives every quiet extension.** -/
theorem TensorStore.ReadsDrainedBeforeExit.quietExt
    (h : TensorStore.ReadsDrainedBeforeExit select X) (hle : X.le Y) (hq : X.QuietExt Y) :
    TensorStore.ReadsDrainedBeforeExit select Y := by
  intro i finish hb ⟨site, address, spec, hi, hsite⟩ ⟨pc, he⟩
  have heX := hq.noExit finish _ he rfl
  have hlen := len_of_get heX
  have hiX : i.2 < (X.tr i.1).length := by
    rw [hb.1]
    exact Nat.lt_trans hb.2.1 hlen
  rw [Execution.le_get_of_lt hle hiX] at hi
  exact Execution.readsDone_mono hle
    (h ⟨hb.1, hb.2.1, hlen⟩ ⟨site, address, spec, hi, hsite⟩ ⟨pc, heX⟩)

/-- **Appending an exit to a drained thread keeps the drain constraint.** -/
theorem TensorStore.ReadsDrainedBeforeExit.snoc_exit
    (h : TensorStore.ReadsDrainedBeforeExit select X) {g pc : Nat}
    {r : Nat → Option AsyncCopy.Ref} (hd : TensorStore.Drained select X g) :
    TensorStore.ReadsDrainedBeforeExit select (X.snoc g ⟨pc, .exit⟩ r) :=
  h.snoc fun _ i hi hs => hd i hi hs

end PTX
