-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.NextState
import Kernels.InklingRelDecode.Proof.Common.EndTime

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow PTX.Sched

/-- Both waits have an outstanding block. The PV consumes block r in iteration r+1. -/
public theorem wait_time {Q L m X g p l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨p,.wait l q ok ac sc⟩)
    (pcs : p=2462 ∨ p=2510) :
    let r := pollRound p (X.tr g)
    r < Lib.blocksOf Q L (g/L.block) ∧ threadTime (schedule Q L) X g =
      (if p=2462 then Lib.Slots.readyWait r else Lib.Slots.probWait r) := by
  obtain ⟨s,hs,inv,pc,_⟩ := next_state hp hf hn (fun _ => nofun)
  change p = _ at pc
  obtain ⟨w,x,r,d,n,rfl⟩ := (pc ▸ state_role s).worker (by omega) (by omega) (by omega)
  cases r with
  | loader =>
    have no (s : Loader.Site) : 2462 ≠ s.pc ∧ 2510 ≠ s.pc := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    rcases pcs with rfl | rfl
    · exact ((no d.site).1 pc).elim
    · exact ((no d.site).2 pc).elim
  | mma =>
    obtain ⟨_,ref,ready,prob,-⟩ := inv.2
    have mach : Inv d := inv.1.1
    obtain ⟨site,i,v⟩ := d
    have only (s : Site) : (2462=s.pc → s=.kvWait) ∧ (2510=s.pc → s=.pWait) := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    have counted (p) : n (.poll p) = pollRound p (X.tr g) := by
      simpa only [List.take_length,cls,pollRound] using fcount hs (.poll p)
    rw [mma_end hs]
    rcases pcs with rfl | rfl
    · obtain rfl := (only site).1 pc
      have lim := ref_count ref (by rfl)
      change low v = Lib.blocksOf Q L (g/L.block) at lim
      change i < low v ∧ _ at mach
      change n (.poll 2462) = i at ready
      rw [counted] at ready
      simp only [ready,↓reduceIte]
      exact ⟨lim ▸ mach.1,rfl⟩
    · obtain rfl := (only site).2 pc
      have lim := ref_count ref (by rfl)
      change low v = Lib.blocksOf Q L (g/L.block) at lim
      change 0 < i ∧ i ≤ low v ∧ _ at mach
      change n (.poll 2510) = i-1 at prob
      rw [counted] at prob
      simp only [prob,show ¬ 2510=2462 by decide,↓reduceIte]
      refine ⟨by omega,?_⟩
      change Lib.Slots.mma i + 15 = Lib.Slots.mma (i-1+1) + 15
      rw [show i-1+1=i by omega]

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
