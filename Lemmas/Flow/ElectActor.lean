-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Elect

@[expose] public section

/-! # One elected thread per warp

A proof tool. Elections with the same mask in one warp return the same leader
(`ElectOk.deterministic`), so the threads of a warp that went on as the leader of such an
election are one thread, whatever the elections' source positions and instances. -/

namespace PTX
noncomputable section

/-- A CTA, warp position and lane identify exactly one launched thread. -/
theorem sameWarp_eq_of_lane_eq {L : Launch} {g h : Nat}
    (hw : SameWarp L g h) (hl : laneOf L g = laneOf L h) : g = h := by
  obtain ⟨⟨_,_,hc⟩,hwarp⟩ := hw
  unfold laneOf at hl
  have hg := Nat.mod_add_div g L.block
  have hh := Nat.mod_add_div h L.block
  have hg' := Nat.mod_add_div (g % L.block) 32
  have hh' := Nat.mod_add_div (h % L.block) 32
  rw [hc] at hg
  omega

/-- Two actual equal-mask elections cannot select different physical threads
of the same warp, even if their source PCs and instance labels differ. -/
theorem selected_elect_thread_unique {L : Launch} {X : Execution}
    (hok : ElectOk L X) {e f : EvId} {pc pc' mask inst inst' leader leader' : Nat}
    (he : X.Elect e pc mask inst leader) (hf : X.Elect f pc' mask inst' leader')
    (hw : SameWarp L e.1 f.1) (hs : laneOf L e.1 = leader)
    (hs' : laneOf L f.1 = leader') : e.1 = f.1 := by
  apply sameWarp_eq_of_lane_eq hw
  rw [hs,hs',hok.deterministic he hf hw]

end
end PTX
