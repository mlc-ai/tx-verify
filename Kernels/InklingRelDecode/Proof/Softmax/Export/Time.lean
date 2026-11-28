-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
import Kernels.InklingRelDecode.Proof.Common.NextState
import Kernels.InklingRelDecode.Proof.Common.EndTime

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Sched

/-- The score poll begins in block zero. The first output poll is in block one. -/
private theorem wait_info {Q L m X g p l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨p,.wait l q ok ac sc⟩)
    (pcs : p=1257 ∨ p=2239) :
    let r := pollRound p (X.tr g)
    ((if p=1257 then r else r+1) < Lib.blocksOf Q L (g/L.block)) ∧
    threadTime (schedule Q L) X g =
      (if p=1257 then Lib.Slots.scoreWait r else Lib.Slots.doneWait (r+1)) := by
  obtain ⟨s,hs,inv,pc,_⟩ := next_state hp hf hn (fun _ => nofun)
  change p = _ at pc
  obtain ⟨w,ent,d,n,rfl⟩ := (pc ▸ state_role s).softmax (by omega) (by omega)
  have limit : ent.limit = Lib.blocksOf Q L (g/L.block) := by
    obtain ⟨Y,hY,pre,get⟩ := hn
    apply reached_limit hp hY (Frame.lt_of_get hY get) (List.getElem?_eq_some_iff.mp get).1.le
    exact (stateAt_congr (C := thread Q L) (X := X) (Y := Y) (by simpa using pre :
      (Y.tr g).take (X.tr g).length = (X.tr g).take (X.tr g).length)).trans hs
  have ctl : Control.Inv ent (g % L.block) d := inv.1.1
  have ref : Ref _ d (softCounts n) := inv.2
  have counted (p) : n (.poll p) = pollRound p (X.tr g) := by
    simpa only [List.take_length,cls,pollRound] using fcount hs (.poll p)
  obtain ⟨site,i,v⟩ := d
  have only (s : Site) : (1257=s.pc → s=.waitS) ∧ (2239=s.pc → s=.waitO) := by
    cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
  rw [softmax_end hs]
  rcases pcs with rfl | rfl
  · obtain rfl := (only site).1 pc
    have h := (counted 1257).symm.trans (congrArg Cnt.s ref.ledger)
    change pollRound 1257 (X.tr g) = i at h
    simp only [h,↓reduceIte]
    exact ⟨limit ▸ ctl.iter_lt (by decide),rfl⟩
  · obtain rfl := (only site).2 pc
    have h := (counted 2239).symm.trans (congrArg Cnt.o ref.ledger)
    change pollRound 2239 (X.tr g) = i-1 at h
    have pos : 0 < i := ref.oWait rfl
    have eq : i-1+1=i := by omega
    simp only [h,eq,show ¬ 2239=1257 by decide,↓reduceIte]
    exact ⟨limit ▸ ctl.iter_lt (by decide),rfl⟩

public theorem wait_time {Q L m X g p l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨p,.wait l q ok ac sc⟩)
    (pcs : p=1257 ∨ p=2239) :
    let r := pollRound p (X.tr g)
    threadTime (schedule Q L) X g =
      (if p=1257 then Lib.Slots.scoreWait r else Lib.Slots.doneWait (r+1)) :=
  (wait_info hp hf hn pcs).2

/-- An output poll waits for the preceding block, so its use count starts one behind. -/
public theorem wait_bound {Q L m X g p l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨p,.wait l q ok ac sc⟩)
    (pcs : p=1257 ∨ p=2239) :
    let r := pollRound p (X.tr g)
    (if p=1257 then r else r+1) < Lib.blocksOf Q L (g/L.block) :=
  (wait_info hp hf hn pcs).1

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
