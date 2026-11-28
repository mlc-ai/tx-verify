-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Time
public import Kernels.InklingRelDecode.Proof.Lib.Slots
public import Kernels.InklingRelDecode.Proof.Lib.Rounds
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.NextState
import Kernels.InklingRelDecode.Proof.Common.EndTime

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow PTX.Sched

/-- Each next empty wait is for a recurrent block that the loader still owes.
The bound is strict even when the preload exhausts the assigned split. -/
public theorem empty_wait_time {Q L m X g l q ok ac sc} (hp : Pre Q L m) (hf : Follow Q L X)
    (hn : NextEv L kernel Assumptions.all m X g ⟨2374,.wait l q ok ac sc⟩) :
    let block := Iface.preloadCount Q L (g/L.block) + pollRound 2374 (X.tr g)
    block < Lib.blocksOf Q L (g/L.block) ∧
      threadTime (schedule Q L) X g = Lib.Slots.emptyWait block := by
  obtain ⟨s,hs,inv,pc,_⟩ := next_state hp hf hn (fun _ => nofun)
  change 2374 = _ at pc
  obtain ⟨w,x,r,d,n,rfl⟩ := (pc ▸ state_role s).worker (by decide : 2344<2374)
    (by decide) (by decide)
  cases r with
  | mma =>
    have no (s : Mma.Site) : 2374 ≠ s.pc := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    exact (no d.site pc).elim
  | loader =>
    obtain ⟨_,ref,ord,_⟩ := inv.2
    obtain ⟨site,i,limit,a,b⟩ := d
    have only (s : Site) : 2374 = s.pc → s = .poll := by
      cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)
    obtain rfl := only site pc
    obtain ⟨j,low,high,word,_⟩ := ref_loop ref (by rfl)
    have hlim := Lib.blocksOf_lt hp hn.lt
    change j < Lib.blocksOf Q L (g/L.block) at high
    change i = _ at word
    subst i
    have bits : (bits (Proof.b32 j)).toNat = j := by
      rw [bits_b32 (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have counted := fcount hs (.poll 2374)
    change n (.poll 2374) = pollRound 2374 ((X.tr g).take (X.tr g).length) at counted
    rw [List.take_length] at counted
    change n (.poll 2374) = (Loader.bits (Proof.b32 j)).toNat - _ at ord
    rw [bits,counted] at ord
    have index : Iface.preloadCount Q L (g/L.block) + pollRound 2374 (X.tr g) = j := by omega
    dsimp only
    rw [index]
    refine ⟨high,?_⟩
    rw [loader_end hs,poll_time,bits]
    rfl

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
