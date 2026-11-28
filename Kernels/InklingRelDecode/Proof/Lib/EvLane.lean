-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.LanePre
public import Lemmas.Kernel.Memory
import Lemmas.Flow.Final

@[expose] public section

/-! # An event of a consistent execution fires from a state of the lane -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

variable {L : Launch} {g : Nat} {m : Mem0} {X : Execution}

/-- **An event that does not end the thread fires from a state of the lane.** -/
theorem lane_of_event (hX : Consistent L kernel Assumptions.all m X) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hne : ¬ Ends e) :
    ∃ s u, Iface.LaneState L X g s ∧ EStep kernel Assumptions.all L g s e (some u) := by
  have hg := Frame.lt_of_get hX he
  have hk : (X.tr g)[k]? = some e := he
  have hlt := (List.getElem?_eq_some_iff.mp hk).1
  obtain ⟨o, hr⟩ := hX.thr g hg
  have hsplit : (X.tr g).take (k + 1) ++ (X.tr g).drop (k + 1) = X.tr g := List.take_append_drop _ _
  rw [← hsplit] at hr
  obtain ⟨o1, h1⟩ := Run.prefix hr
  cases o1 with
  | none =>
    obtain ⟨e', hl, hend⟩ := Run.ended_last h1
    have : e' = e := by
      rw [List.getLast?_eq_getElem?, List.length_take_of_le (by omega)] at hl
      simp only [List.getElem?_take, Nat.add_sub_cancel, Nat.lt_succ_self, ↓reduceIte] at hl
      exact Option.some.inj (hl.symm.trans hk)
    subst this
    exact absurd hend hne
  | some u =>
    rw [List.take_add_one, hk, Option.toList_some] at h1
    obtain ⟨u0, s, hu, hus, hes⟩ := Run.unsnoc _ e h1
    exact ⟨s, u, ⟨k, u0, by simpa using hu, hus⟩, hes⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
