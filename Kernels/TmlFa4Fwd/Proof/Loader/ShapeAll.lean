-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Loader.ShapeRowsPrime
import Kernels.TmlFa4Fwd.Proof.Loader.ShapeRowsSteady
import Kernels.TmlFa4Fwd.Proof.Loader.ShapeRowsWarm
import Kernels.TmlFa4Fwd.Proof.Loader.ShapeSites
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' events by state, at every state; return kinds

`shape`: the event a state fires is the event of its site (`Ev`), from the family theorems; a
state at a sub-step its site does not have fails the machine's invariant. `ret` is the kind of
value each site returns, a 32-bit word at a load or a shuffle, and the machine stops exactly on
a returned value of another kind (`stop_iff`, by `stop_cases`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- A state at a sub-step its site does not have: its shape obligation holds vacuously. -/
theorem shapeAt_junk {d : D} (h : ¬ (d.k = 0 ∨ d.site.midOk d.k)) :
    (code p L g w ent).ShapeAt (Ev p L g w) d :=
  fun _ hi _ _ => absurd hi h

theorem shapeAt (hp : Pre p L m) (d : D) : (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  by_cases hlw : ∃ per b h, s = .lw per b h
  · obtain ⟨per, b, h, rfl⟩ := hlw
    exact shapeAt_lw hp _ ⟨per, b, h, rfl⟩
  by_cases hk : k = 0
  case neg =>
    refine shapeAt_junk ?_
    rintro (h | h)
    · exact hk h
    · cases s <;> first | exact h | exact hlw ⟨_, _, _, rfl⟩
  subst hk
  cases s with
  | lw per b h => exact absurd ⟨per, b, h, rfl⟩ hlw
  | setmax | word _ | down _ | up _ _ | total _ | vote _ | pre _ | tiles _ | q0 | q1 | uk
  | exit => exact shapeAt_sched hp _ rfl (by simp)
  | dw _ | dq | de | da => exact shapeAt_drain hp _ rfl (by simp)
  | pgLd _ _ | pgSt _ _ | rwSt _ _ => exact shapeAt_pg hp _ rfl (by simp)
  | slot _ _ | ptP _ _ _ | ptR _ _ _ | ptS _ _ _ => exact shapeAt_pt hp _ rfl (by simp)
  | commit _ _ | arrive _ _ => exact shapeAt_end hp _ rfl (by simp)
  | tw _ | te _ _ | ta _ => exact shapeAt_tma hp _ rfl (by simp)
  | tc _ _ => exact shapeAt_tc hp _ rfl (by simp)
  | xl per _ _ | xh per _ _ =>
    cases per
    · exact shapeAt_shflPrime hp _ rfl (by simp)
    · exact shapeAt_shflWarm hp _ rfl (by simp)
    · exact shapeAt_shflSteady hp _ rfl (by simp)
  | cp per _ _ _ =>
    cases per
    · exact shapeAt_cpPrime hp _ rfl (by simp)
    · exact shapeAt_cpWarm hp _ rfl (by simp)
    · exact shapeAt_cpSteady hp _ rfl (by simp)

/-- **The event a state of the loader fires is the event of its site.** -/
theorem shape (hp : Pre p L m) : (code p L g w ent).Shape (Ev p L g w) :=
  Code.Shape.of_at (shapeAt hp)

/-- The kind of value each site returns: a 32-bit word at a load or a shuffle. -/
def ret (d : D) : RetKind :=
  match d.site with
  | .word _ | .q0 | .q1 | .uk | .down _ | .up _ _ | .total _ | .pre _ | .tiles _ | .pgLd _ _
  | .ptP _ _ _ | .ptR _ _ _ | .lw _ _ _ | .xl _ _ _ | .xh _ _ _ => .word 32
  | _ => .none

set_option maxHeartbeats 4000000 in
/-- **The machine stops exactly on a returned value that is not a 32-bit word.** -/
theorem stop_iff (d : D) : ∀ {e : Event}, (code p L g w ent).inv d → Ev p L g w d e →
    ((code p L g w ent).next d e = some none ↔ ¬ (ret d).accepts e) := by
  obtain ⟨s, v, k⟩ := d
  stop_cases s unfolding [Ev, Epilogue.Ev, Site.toE]
    trans [ret, succ, word32, scAt, D.mk', afterTotal, afterTiles, loopHead, scanExit, passStart,
      afterArrive, groupEnd, teNext, teElected, dwNext, pkStart, pgEnter]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
