-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Def
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow

@[expose] public section

/-! # The exit that follows an event of an exited CTA -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX

variable {L : Launch} {m : Mem0} {X : Execution}

/-- **An event that is no exit is followed, in its lane, by the lane's exit** once its CTA
exited. -/
theorem exit_after (hX : Consistent L kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) (hne : e.kind ≠ .exit) (hx : CtaExited L X (i.1 / L.block)) :
    ∃ finish, OwnerExit L X (i.1 / L.block) finish ∧ TraceBefore X i finish := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨tag, hl⟩ := hx i.1 hg rfl
  rw [List.getLast?_eq_getElem?] at hl
  have hGet : X.get (i.1, (X.tr i.1).length - 1) = some ⟨tag, .exit⟩ := hl
  have hi := PTX.len_of_get he
  have hLast := PTX.len_of_get hGet
  have hlt : i.2 < (X.tr i.1).length - 1 := by
    by_contra hn
    have hIndex : i = (i.1, (X.tr i.1).length - 1) := Prod.ext rfl (by omega)
    have hEq := Option.some.inj ((hIndex ▸ he).symm.trans hGet)
    exact hne (congrArg Event.kind hEq)
  exact ⟨(i.1, (X.tr i.1).length - 1), ⟨hg, rfl, tag, hGet⟩, rfl, hlt, hLast⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
