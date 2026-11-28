-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Common.WorkerBar
public import Kernels.InklingRelDecode.Proof.Common.FinalPrefix
import all Kernels.InklingRelDecode.Proof.Common.EndTime
import all Kernels.InklingRelDecode.Proof.Common.Time
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
import Kernels.InklingRelDecode.Proof.Softmax.Export.TcLag
import Kernels.InklingRelDecode.Proof.Prologue.Export.RegBand

@[expose] public section

/-! # The clock of every state against the final rendezvous

Every state before the final rendezvous of barrier 0 is no later than it, strictly unless it
stands at it, where it is exactly at the clock `finish + 292`. -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- What a state before the final rendezvous says about its clock. -/
def FinalCapAt (time pc : Nat) : Prop :=
  Lib.afterFinal pc = 0 → time ≤ Lib.Slots.finish + 292 ∧
    (Lib.finalSync pc = false → time < Lib.Slots.finish + 292) ∧
    (Lib.finalSync pc = true → time = Lib.Slots.finish + 292)

private theorem dispatch_final (d : Dispatch.D) (al : Dispatch.Allowed d) (n : Cls → Nat) (w x) :
    FinalCapAt (siteTime (Q := Q) (L := L) (g := g) (.inr ⟨.inl (.dispatch w x), .inl d⟩, n))
      d.site.pc := by
  unfold FinalCapAt
  obtain ⟨st, r⟩ := d
  rcases al with ⟨hr, hm⟩ | ⟨hr, hm⟩ <;> simp only at hr <;> subst hr <;>
    simp [Dispatch.round0, Dispatch.round1] at hm <;>
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [siteTime, siteClock, workerClock, dispatchClock, Dispatch.Site.pc, Lib.afterFinal,
      Lib.finalSync, Lib.Slots.publish, Lib.Slots.reuse, Lib.Slots.enter, Lib.Slots.finish,
      Lib.Slots.frame, Lib.Slots.stride]

private theorem pc_low {p t : Nat} (h : p < 2850) (ht : t ≤ Lib.Slots.finish + 284) :
    FinalCapAt t p := by
  intro _
  have a : Lib.finalSync p = false := by simp [Lib.finalSync]; omega
  exact ⟨by omega, fun _ => by omega, fun h => by simp [a] at h⟩

private theorem start_low (s : Startup.Site) : s.pc < 2850 := by
  cases s <;> first | decide | (rename_i r; cases r <;> decide)

private theorem loader_low (s : Loader.Site) : s.pc < 2850 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem mma_low (s : Mma.Site) : s.pc < 2850 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem epi_final (d : Epilogue.Control.D) :
    FinalCapAt (Epilogue.time d) d.site.pc := by
  intro h
  obtain ⟨s, v⟩ := d
  cases s
  case store k =>
    have := k.isLt
    simp [Epilogue.time, Epilogue.startTime, Epilogue.Site.position, Epilogue.Site.pc,
      Lib.afterFinal, Lib.finalSync, Epilogue.storePc] at h ⊢
    omega
  all_goals simp [Epilogue.time, Epilogue.startTime, Epilogue.Site.position,
    Epilogue.Site.pc, Lib.afterFinal, Lib.finalSync] at h ⊢

/-- **A state before the final rendezvous of barrier 0 is no later than it.** -/
theorem final_cap_state {k s} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (words : RoleBytes L X) (hg : g < L.threads)
    (hk : k ≤ (X.tr g).length) (hs : stateAt (thread Q L) X g k = some (some s))
    (nub : NoUbBefore X g k) :
    FinalCapAt (siteTime s) ((thread Q L g).pc s) := by
  have tbl := reached_table hf hg nub hs
  obtain ⟨rd, rl, rm⟩ := worker_rounds hp hX words hk hs nub
  obtain ⟨s, n⟩ := s
  rcases s with st | ⟨r, d⟩
  · exact pc_low (start_low st.site) (by
      have := (siteTime_startup (Q := Q) (L := L) (g := g) st n).1
      omega)
  rcases r with r | r
  swap
  · refine pc_low (show Startup.Entry.pc r < 2850 by cases r <;> decide) ?_
    simp [siteTime, siteClock]
  cases r with
  | dispatch w x =>
    rcases d with d | ⟨i, d⟩
    · exact dispatch_final d (rd w x d n rfl) n w x
    · cases i with
      | loader r0 =>
        obtain rfl := rl w x r0 d n rfl
        refine pc_low (loader_low d.site) ?_
        have := (Loader.time_bounds d).2
        simpa [siteTime, siteClock, workerClock] using this
      | mma r0 =>
        obtain rfl := rm w x r0 d n rfl
        refine pc_low (mma_low d.site) ?_
        have := (Mma.time_bounds (show Mma.Inv d from tbl.1.1)).2
        simpa [siteTime, siteClock, workerClock] using this
  | prologue w =>
    rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
    · refine pc_low (by have := Prologue.Site.pc_range d.site; change d.site.pc < 2850; omega) ?_
      have := (Prologue.Export.regBand d).1
      change Prologue.time d ≤ _
      omega
    · refine pc_low (by
        change d.site.pc < 2850
        rcases Softmax.Site.pc_range d.site with r | e
        · omega
        · rw [e]; decide) ?_
      have := (Softmax.Export.time_le_finish tbl.1.1).1
      exact this.trans (Nat.le_add_right _ _)
    · exact epi_final d

end

end PTX.Kernels.InklingRelDecode.Proof
