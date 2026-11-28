-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PreElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Bar

@[expose] public section

/-! # A lane of warp 4 or 5 before its election

The producer facts of the MMA and TMA lanes (`Mma/Export/{Time,Ring}.lean`,
`Tma/Export/Time.lean`) start from the elected lane's election event. When no lane of the warp
has elected, the lane the channels fall back to (`tmaThread`: thread `c * L.block + 160`; the
MMA analogue `c * L.block + 128`) is covered here: a lane of warp 4 (5) without an event at the
election's pc 1853 (2165) has no `exit` event and its glued time is at most `electSlot`
(`Lib/Slots.lean`: before the `q_utccp` slot and every block's frame), so it is short of every
channel event of the lag rows (`mma_preElect`, `tma_preElect`; per CTA for the warp's first lane
when no lane of the warp has elected: `mma_firstPre`, `tma_firstPre`).

How the lag rows use it (`Sched.LagN.early`: `threadTime < τ (count + δ)`; `exit`): with no
counted event the producer must be before `τ δ`; `electSlot < qUtccpSlot` covers `q_utccp`
(`τ _ = qUtccpSlot`) and `electSlot < frame r + o` (`elect_lt`) every ring slot (`raw_ready`
`rrArr`, `qk_done` `qkCommit`, `sv_done` `svCommit`); the `exit` obligation is vacuous.

Proof: `Common/PreElect.lean` (`pre_cls`, `pre_hist`) with the three cases of the glued time
(`time_last`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem el_time (r : SubEntry) (hw : ElWarp L g r) : elTime r ≤ electSlot := by
  cases r <;> simp only [ElWarp] at hw <;> simp [elTime, electSlot, idleBase, roleBase, tmaOrg]

/-- The principle: no exit, time at most `electSlot`. -/
private theorem pre_core (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) {r : SubEntry}
    (hw : ElWarp L g r) (hno : ∀ k e, X.get (g, k) = some e → e.pc ≠ elPc r) :
    (∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X g ≤ electSlot := by
  have hT := el_time r hw
  have hpost : ∀ i σ, Frame.stateAt (thread P L) X g i = some (some σ) → ¬ PostE r σ :=
    fun i σ hσ hP => by
      obtain ⟨j, -, e, he, hpc⟩ := pre_hist hp hX hFw hnu hg hw i σ hσ hP
      exact hno j e he hpc
  have hS := elect_le
  simp only [wg0Org] at hS
  refine ⟨fun k pc he => ?_, time_last (Q := fun t => t ≤ electSlot) (Nat.zero_le _)
    (fun σ hσ => ?_) fun σ f hσ hf _ => ?_⟩
  · have h103 := startup_exit hp hX hFw he
    obtain ⟨σ, hσ, -, hi, hev, hpc⟩ := ev_at hp hX hFw he (fun _ h => by cases h)
    rcases pre_cls hp hX hFw hg hw hσ with ⟨d, n, rfl, hx⟩ | ⟨s, n, rfl⟩ | h | ⟨-, h⟩
    · have := startup_pc_le (P := P) hx
      change pc = d.site.pc at hpc
      omega
    · have hx := hi.2
      cases s <;> simp [Code.gatedExit, wg1Enter, Wg1.exitOf] at hx <;>
        simp [table, Code.roleEv, fragEv, wg1Ev, Wg1.Ev] at hev
    · exact hpost k σ hσ h
    · exact hno k _ he (h _ he fun _ h => by cases h)
  · rcases pre_cls hp hX hFw hg hw hσ with ⟨d, n, rfl, hx⟩ | ⟨s, n, rfl⟩ | h | ⟨h, -⟩
    · have := Startup.time_lt (d := d) (by simpa [startupEnter] using hx)
      simp only [time]
      omega
    · have := Wg1.time_le s
      simp only [time, fragTime, wg1Time, roleBase]
      omega
    · exact (hpost _ σ hσ h).elim
    · omega
  · have he : X.get (g, (X.tr g).length - 1) = some f := hf
    have hu : ∀ fl, f.kind ≠ .ub fl := fun fl h => hnu ⟨_, f.pc, fl, by rw [he, ← h]⟩
    rcases pre_cls hp hX hFw hg hw hσ with ⟨d, n, rfl, hx⟩ | ⟨s, n, rfl⟩ | h | ⟨-, h⟩
    · have := Startup.time_lt (d := d) (by simpa [startupEnter] using hx)
      simp only [time]
      omega
    · have := Wg1.time_le s
      simp only [time, fragTime, wg1Time, roleBase]
      omega
    · exact (hpost _ σ hσ h).elim
    · exact (hno _ f he (h f hf hu)).elim

/-- **A lane of warp 4 before its election**: without an event at pc 1853 it has no `exit` event
and its glued time is at most `electSlot`. -/
theorem mma_preElect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) (hw : MbarRow.warp L g = 4)
    (hno : ∀ k e, X.get (g, k) = some e → e.pc ≠ 1853) :
    (∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X g ≤ electSlot := by
  have hw' : ElWarp L g .mma := by
    simp only [MbarRow.warp, tidOf_x_eq hp] at hw
    simp only [ElWarp, warpOf, tidOf_eq hp]
    exact hw
  exact pre_core hp hX hFw hnu hg hw' hno

/-- **A lane of warp 5 before its election**: without an event at pc 2165 it has no `exit` event
and its glued time is at most `electSlot`. -/
theorem tma_preElect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) (hg : g < L.threads) (hw : MbarRow.warp L g = 5)
    (hno : ∀ k e, X.get (g, k) = some e → e.pc ≠ 2165) :
    (∀ k pc, X.get (g, k) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (timed P L) X g ≤ electSlot := by
  have hw' : ElWarp L g .tma := by
    simp only [MbarRow.warp, tidOf_x_eq hp] at hw
    simp only [ElWarp, warpOf, tidOf_eq hp]
    exact hw
  exact pre_core hp hX hFw hnu hg hw' hno

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
