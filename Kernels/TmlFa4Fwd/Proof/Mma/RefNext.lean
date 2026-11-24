-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
import Kernels.TmlFa4Fwd.Proof.Mma.RefElect
import Kernels.TmlFa4Fwd.Proof.Mma.RefPoll
import Kernels.TmlFa4Fwd.Proof.Mma.RefScan

@[expose] public section

/-! # The MMA warp's counts are kept by every step -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat} {ent : Nat → Value}

/-- **The counts and loop registers are kept by every step** of the counted machine on an event
of the state's shape that is not undefined behaviour and whose election, if any, returns what
`Expect` asks. -/
theorem ref_step (hp : Pre p L m) {d : D} {n : Cnt → Nat} {e : Event}
    (hJ : RefCounts p L g (d, n)) (hE : ExpectElect L g (d, n) e) (hev : Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f) {d' : D}
    (hn : succ p L g d e = some (some d')) : RefCounts p L g (d', Code.bump (cls L g) n e) := by
  obtain ⟨r, w, hQ⟩ := hJ
  obtain ⟨s, v⟩ := d
  obtain ⟨pc, k⟩ := e
  have h : StepRef p L g s := by
    cases s with
    | bar1 => exact step_bar1 hp
    | ldAlloc => exact step_ldAlloc hp
    | bcast => exact step_bcast hp
    | word sk => exact step_word hp sk
    | down sk => exact step_down hp sk
    | up sk j => exact step_up hp sk j
    | total sk => exact step_total hp sk
    | vote l => exact step_vote hp l
    | pre l => exact step_pre hp l
    | tiles l => exact step_tiles hp l
    | q0 => exact step_q0 hp
    | q1 => exact step_q1 hp
    | uk => exact step_uk hp
    | wt k => exact step_wt hp k
    | sh k => exact step_sh hp k
    | eq b => exact step_eq hp b
    | qk b j => exact step_qk hp b j
    | ep b => exact step_ep hp b
    | pv b j => exact step_pv hp b j
    | mw b ld => exact step_mw hp b ld
    | ce c => exact step_ce hp c
    | cm c => exact step_cm hp c
    | relinq l => exact step_relinq hp l
    | bar2 l => exact step_bar2 hp l
    | dealloc l => exact step_dealloc hp l
    | exit l => exact step_exit hp l
  exact h v n r w pc k d' hQ hE hev hub hn

/-- What an event at a counted state must return: a value of the site's kind, and at an election
the outcome of the lane's earlier elections. -/
def Expect (L : Launch) (g : Nat) (dn : D × (Cnt → Nat)) (e : Event) : Prop :=
  (ret dn.1).accepts e ∧ ExpectElect L g dn e

/-- **The `ref_next` obligation for the counts**: at a state satisfying `RefCounts`, an expected
event of the state's shape that is not undefined behaviour neither stops the counted machine nor
leads to a state that breaks `RefCounts`. -/
theorem ref_next (hp : Pre p L m) {dn : D × (Cnt → Nat)} {e : Event}
    (hJ : RefCounts p L g dn) (hE : Expect L g dn e) (hev : Ev p L g dn.1 e)
    (hub : ∀ f, e.kind ≠ .ub f) :
    (MC p L g ent).next dn e ≠ some none ∧
      ∀ dn', (MC p L g ent).next dn e = some (some dn') → RefCounts p L g dn' := by
  obtain ⟨d, n⟩ := dn
  refine ⟨fun h => next_ne_stop (ent := ent) hev hE.1 ?_, fun dn' h => ?_⟩
  · change ((code p L g ent).next d e).map _ = _ at h
    rcases hx : (code p L g ent).next d e with _ | _ | _ <;> rw [hx] at h <;> simp_all
  · change ((code p L g ent).next d e).map _ = _ at h
    rcases hx : (code p L g ent).next d e with _ | _ | d' <;> rw [hx] at h <;> cases h
    exact ref_step hp hJ hE.2 hev hub hx

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
