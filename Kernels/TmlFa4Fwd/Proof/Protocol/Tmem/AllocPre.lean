-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemTrace
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Std.Tactic.BVDecide.Normalize.Prop
set_option linter.unusedTactic false

@[expose] public section

/-! # Lane 0 of warp 12 allocates before its first barrier-2 event

A startup state and a state of the MMA warp's allocation prefix (`IsPre`) are preceded only by
such states (the thread machine never returns from a role), and their events are no barrier-2
events (the startup's barrier is 0, the prefix makes none), so no barrier-2 event precedes them
(`pre_bar2_zero`). The allocation event of a lane of warp 12 is fired from the prefix (the role's
code fires its resource events at the relinquish and deallocation sites, whose program counters
are not the allocation's), so lane 0's allocation, which every state of the role's code follows
(`mma_trace`), has no barrier-2 event before or at it (`lane0_alloc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A startup state or a state of the MMA warp's allocation prefix. -/
def IsPre : (thread p L g).D → Prop
  | (.inl _, _) => True
  | (.inr ⟨.mma, .inl _⟩, _) => True
  | _ => False

set_option maxHeartbeats 8000000 in
/-- The role's code fires no allocation at program counter 1909. -/
theorem code_noalloc {d : Mma.D} {grp : CtaGroup} {dst : Option Loc} {nn : Nat}
    (hev : Mma.Ev p L g d ⟨1909, .tc (.resource grp dst (.alloc nn))⟩)
    (hpc : 1909 = d.site.pc) : False := by
  obtain ⟨s0, v0⟩ := d
  cases s0 <;> simp only [Mma.Ev] at hev
  all_goals first | exact (epi_nores hev rfl).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Mma.Site.pc]

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

set_option maxHeartbeats 4000000 in
/-- **No barrier-2 event precedes a startup or allocation-prefix state.** -/
theorem pre_bar2_zero : ∀ (k : Nat) (σ : (thread p L g).D),
    Frame.stateAt (thread p L) X g k = some (some σ) → IsPre σ →
    ((X.tr g).take k).countP (Execution.isBarId 2) = 0 := by
  intro k
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro σ h hpre
    rcases hk : (X.tr g)[k]? with _ | e
    · have hle : (X.tr g).length ≤ k := by
        by_contra hc; rw [List.getElem?_eq_getElem (by omega)] at hk; cases hk
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hle] at h
      rw [List.take_of_length_le (by omega), ← List.take_of_length_le hle]
      exact ih σ h hpre
    · have h0 := h
      rw [Frame.stateAt_succ hk] at h
      rcases hs : Frame.stateAt (thread p L) X g k with _ | _ | ⟨σ1, n'⟩
      · rw [hs] at h; cases h
      · rw [hs] at h; cases h
      rw [hs] at h
      obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
      obtain ⟨σ', n⟩ := σ
      -- the state before is a startup or prefix state
      have hpre0 : IsPre (p := p) (L := L) (g := g) (σ1, n') := by
        rcases σ1 with s | ⟨i, d⟩
        · trivial
        · cases i with
          | mma =>
            rcases d with s | d
            · trivial
            · exfalso
              obtain ⟨⟨⟩, d⟩ := d
              have h' : (thread p L g).next (Mma.minj p L g d n') e = some (some (σ', n)) := h
              rw [Mma.next_minj] at h'
              obtain ⟨o, -, ho⟩ := Option.map_eq_some_iff.mp h'
              cases o with
              | none => cases ho
              | some x =>
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ho
                obtain ⟨rfl, -⟩ := ho
                exact hpre
          | _ =>
            exfalso
            simp only [glued, Code.glue] at h1
            obtain ⟨o, -, ho⟩ := Option.map_eq_some_iff.mp h1
            cases o with
            | none => cases ho
            | some x =>
              simp only [Option.map_some, Option.some.injEq] at ho
              subst ho
              exact hpre
      have hc0 := ih _ hs hpre0
      rw [List.take_add_one, hk, Option.toList_some, List.countP_append, hc0]
      -- the event is no barrier-2 event
      obtain ⟨pc, kind⟩ := e
      cases kind with
      | bar id cnt mode =>
        by_cases hid : id = 2
        · subst hid
          exfalso
          have hg := Frame.lt_of_get hX (show X.get (g, k) = _ from hk)
          obtain ⟨σ2, hσ2, hJ, -, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
            (table_followed hp hX hFw) (show X.get (g, k) = _ from hk)
            (by intro f hf; cases hf)
          rw [hs] at hσ2
          simp only [Option.some.injEq] at hσ2
          subst hσ2
          rcases σ1 with s | ⟨i, d⟩
          · have := start_barOps hJ hev
            simp at this
          · cases i with
            | mma =>
              rcases d with s | d
              · rcases hev with ⟨_, _, _, hk'⟩ | ⟨_, _, _, hk'⟩ | ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;>
                  cases hk'
              · exact hpre0.elim
            | _ => exact hpre0.elim
        · simp [Execution.isBarId, hid]
      | _ => rfl

/-- **Lane 0 of warp 12 allocates before its first barrier-2 event**: every state of the role's
code follows an allocation of the lane with no barrier-2 event before or at it, and the lane's
address store after it. -/
theorem lane0_alloc {z k : Nat} {d : Mma.D} {n : Cls → Nat} (hz : z < L.threads)
    (h12 : Prologue.warpIndex L z = 12) (hl : laneOf L z = 0) (hk : k ≤ (X.tr z).length)
    (hσ : Frame.stateAt (thread p L) X z k = some (some (Mma.minj p L z d n))) :
    ∃ j < k, AllocAt L X z j ∧ j + 1 < (X.tr z).length ∧
      ((X.tr z).take (j + 1)).countP (Execution.isBarId 2) = 0 := by
  obtain ⟨⟨j, hjk, hall, hst⟩, -⟩ := mma_trace hp hX hz h12 k hk _ hσ
  obtain ⟨bs, hb⟩ := hst hl
  have hlen : j + 1 < (X.tr z).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr z)[j + 1]? = _ from hb)).1
  refine ⟨j, hjk, hall, hlen, ?_⟩
  obtain ⟨σ2, hσ2, hJ, hi, hev⟩ := ev_at hp hX (table_shape_of hp hFw)
    (table_followed hp hX hFw) hall.1 (by intro f hf; cases hf)
  obtain ⟨d2, n2, rfl⟩ := tev_res hJ hi hev rfl
  have hpre : IsPre (p := p) (L := L) (g := z) (.inr ⟨.mma, d2⟩, n2) := by
    rcases d2 with s | ⟨⟨⟩, d0⟩
    · trivial
    · exfalso
      have hpc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hall.1 hσ2 (fun f h =>
          by cases h)
      exact code_noalloc hev hpc
  have h0 := pre_bar2_zero hp hX hFw j _ hσ2 hpre
  rw [List.take_add_one, show (X.tr z)[j]? = _ from hall.1, Option.toList_some,
    List.countP_append, h0]
  rfl

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
