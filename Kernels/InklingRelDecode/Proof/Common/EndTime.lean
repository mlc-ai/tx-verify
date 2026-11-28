-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Common.Where
public import Kernels.InklingRelDecode.Proof.Loader.Time
public import Kernels.InklingRelDecode.Proof.Mma.Time
public import Kernels.InklingRelDecode.Proof.Softmax.Time
public import Kernels.InklingRelDecode.Proof.Epilogue.Time
import Kernels.InklingRelDecode.Proof.Prologue.Export.RegBand
import all Kernels.InklingRelDecode.Proof.Common.Time
public import Lemmas.Kernel.Progress.Blocked

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Sched

/-- The clock of a lane whose last state belongs to the Loader role. -/
public theorem loader_end {Q L X g w x r d n}
    (hs : Frame.stateAt (thread Q L) X g (X.tr g).length =
      some (some (workerState w x (.loader r) d n))) :
    threadTime (schedule Q L) X g = Loader.time d := threadTime_of (M := schedule Q L) hs

/-- The clock of a lane whose last state belongs to the Mma role. -/
public theorem mma_end {Q L X g w x r d n}
    (hs : Frame.stateAt (thread Q L) X g (X.tr g).length =
      some (some (workerState w x (.mma r) d n))) :
    threadTime (schedule Q L) X g = Mma.time d := threadTime_of (M := schedule Q L) hs

/-- The clock of a lane whose last state belongs to the Softmax role. -/
public theorem softmax_end {Q L X g w ent d n}
    (hs : Frame.stateAt (thread Q L) X g (X.tr g).length =
      some (some (softState w ent d n))) :
    threadTime (schedule Q L) X g = Softmax.time d := threadTime_of (M := schedule Q L) hs

/-- The clock of a lane whose last state belongs to the Epilogue role. -/
public theorem epilogue_end {Q L X g w ent d n}
    (hs : Frame.stateAt (thread Q L) X g (X.tr g).length =
      some (some (epiState w ent d n))) :
    threadTime (schedule Q L) X g = Epilogue.time d := threadTime_of (M := schedule Q L) hs

public noncomputable def siteTime {Q L g} (d : (thread Q L g).D) : Nat := siteClock d
public theorem siteTime_soft {Q L g w ent d n} : siteTime (Q := Q) (L := L) (g := g)
    (softState w ent d n) = Softmax.time d := by unfold siteTime siteClock; rfl
public theorem siteTime_epi {Q L g w ent d n} : siteTime (Q := Q) (L := L) (g := g)
    (epiState w ent d n) = Epilogue.time d := by unfold siteTime siteClock; rfl
public theorem siteTime_pro {Q L g w d n} : siteTime (Q := Q) (L := L) (g := g)
    (.inr ⟨.inl (.prologue w), .inl d⟩, n) ≤ 283 := by
  unfold siteTime siteClock; exact (Prologue.Export.regBand d).1
public theorem siteTime_pro_idx {Q L g w d n} : siteTime (Q := Q) (L := L) (g := g)
    (.inr ⟨.inl (.prologue w), .inl d⟩, n) = 100 + Prologue.allSites.idxOf d.site := by
  unfold siteTime siteClock
  change Prologue.time d = _
  rfl
public theorem siteTime_startup {Q L g} (d : Startup.D) (n) :
    let t := siteTime (Q := Q) (L := L) (g := g) (.inl d, n)
    t ≤ 26 ∧ (d.site = .allocWr → t = 4) ∧ (d.site = .bar0 → t = 10) := by
  obtain ⟨s,t,x,w⟩ := d; cases s
  case' enter r => cases r
  all_goals simp [siteTime,siteClock,startupClock]
public theorem siteTime_startup_pc {Q L g} (d : Startup.D) (n) :
    let t := siteTime (Q := Q) (L := L) (g := g) (.inl d, n)
    (d.site.pc = 11 → 2 ≤ t ∧ t ≤ 4) ∧ (d.site.pc = 15 → t = 22) := by
  obtain ⟨s,tm,x,w⟩ := d; cases s
  case' enter r => cases r
  all_goals simp [siteTime,siteClock,startupClock,Startup.Site.pc,Startup.Entry.pc]

public theorem siteTime_startup_early {Q L g} (d : Startup.D) (n) :
    let t := siteTime (Q := Q) (L := L) (g := g) (.inl d, n)
    (d.site = .alloc → t = 2) ∧ (d.site = .relinq → t = 22) ∧
      (d.site ≠ .alloc → d.site ≠ .relinq → d.site ≠ .shfl → (∀ r, d.site ≠ .enter r) →
        t ≤ 20) := by
  obtain ⟨s,tm,x,w⟩ := d; cases s
  case' enter r => cases r
  all_goals simp [siteTime,siteClock,startupClock]

public theorem siteTime_startup_succ {Q L g d d' ev} (n n')
    (hpc : d.site.pc = 11 ∨ d.site.pc = 15 ∨ d.site.pc = 12 ∨ d.site.pc = 14)
    (h : Startup.succ L g d ev = some (some d')) :
    siteTime (Q := Q) (L := L) (g := g) (.inl d, n) <
      siteTime (Q := Q) (L := L) (g := g) (.inl d', n') := by
  obtain ⟨s,tm,x,w⟩ := d; cases s
  case' enter r => cases r
  all_goals simp [Startup.succ, Startup.Site.pc] at h hpc
  all_goals subst h
  all_goals try split_ifs
  all_goals simp [siteTime,siteClock,startupClock]

public theorem end_time {Q L X g d} (hs : Frame.stateAt (thread Q L) X g (X.tr g).length =
    some (some d)) : threadTime (schedule Q L) X g = siteTime d :=
  threadTime_of (M := schedule Q L) hs
public theorem time_at {Q L X g k d} (hs : Frame.stateAt (thread Q L) X g k = some (some d)) :
    timeAt (schedule Q L) X g k = siteTime d := by
  have h : Frame.stateAt (schedule Q L).code X g k = some (some d) := hs
  unfold timeAt; rw [h]; rfl
public theorem alive_iff {Q L X h t} :
    (∃ d, Frame.stateAt (schedule Q L).code X h t = some (some d)) ↔
      ∃ d, Frame.stateAt (thread Q L) X h t = some (some d) := Iff.rfl
public theorem time_zero {Q L X g j} (h0 : Frame.stateAt (thread Q L) X g j = none)
    (h : Frame.stateAt (thread Q L) X g (j + 1) = none) :
    timeAt (schedule Q L) X g (j + 1) = 0 := by
  have h1 : Frame.stateAt (schedule Q L).code X g (j + 1) = none := h
  have h2 : Frame.stateAt (schedule Q L).code X g j = none := h0
  unfold timeAt
  rw [h1]
  simp only [Nat.add_sub_cancel, h2]
public theorem time_dead {Q L X g j d} (hs : Frame.stateAt (thread Q L) X g j = some (some d))
    (h : Frame.stateAt (thread Q L) X g (j + 1) = none) :
    timeAt (schedule Q L) X g (j + 1) = siteTime d + 1 := by
  have h1 : Frame.stateAt (schedule Q L).code X g (j + 1) = none := h
  have h0 : Frame.stateAt (schedule Q L).code X g j = some (some d) := hs
  unfold timeAt
  rw [h1]
  simp only [Nat.add_sub_cancel, h0]
  rfl
end PTX.Kernels.InklingRelDecode.Proof
