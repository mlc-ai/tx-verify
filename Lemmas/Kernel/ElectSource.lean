-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

@[expose] public section

/-! # The source of an election's result

A proof tool (promoted from the tml-fa4 MMA warp's proof). Core's election rule (`ElectOk`,
DEP-WARP-ELECT) says that every election of a warp with one member mask returns one leader. Two
consequences a role uses:

* `elect_leader`: two elections of lanes of one warp with one mask return the same leader; in
  particular a lane that won one election with a mask wins every election with that mask, and a
  lane that lost one loses every one (the elections of one lane are of one warp).
* `elect_winner`: two lanes of one warp that each won an election with one mask have the same
  lane index, so at most one lane of the warp wins, and the warp's issues after its elections are
  that lane's. -/

namespace PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Two elections of one warp with one mask return one leader.** -/
theorem elect_leader (hX : Consistent L K A mem0 X) {e f : EvId} {pc pc' m inst inst' ld ld' : Nat}
    (he : X.get e = some ⟨pc, .elect m inst ld⟩) (hf : X.get f = some ⟨pc', .elect m inst' ld'⟩)
    (hw : SameWarp L e.1 f.1) : ld = ld' :=
  hX.elect.2.2 e f pc pc' m inst inst' ld ld' he hf hw

/-- **Two lanes of one warp that won an election with one mask have one lane index.** -/
theorem elect_winner (hX : Consistent L K A mem0 X) {e f : EvId} {pc pc' m inst inst' : Nat}
    (he : X.get e = some ⟨pc, .elect m inst (laneOf L e.1)⟩)
    (hf : X.get f = some ⟨pc', .elect m inst' (laneOf L f.1)⟩) (hw : SameWarp L e.1 f.1) :
    laneOf L e.1 = laneOf L f.1 :=
  elect_leader hX he hf hw

end PTX
