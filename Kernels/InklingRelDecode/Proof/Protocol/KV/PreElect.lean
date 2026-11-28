-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Due
public import Kernels.InklingRelDecode.Proof.Common.Export.PreElect
import Kernels.InklingRelDecode.Proof.Mma.Export.Time

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched MbarRow

/-- A ready waiter needs a recurrent issue only after its preload. Before the
loader warp elects, its default producer is still early enough for this use. -/
theorem before_election_due {Q L m X g c s} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (words : RoleBytes L X) (hu : NoUbOutside L X) (hw : Waiting L m X .ready c s g)
    (zero : (X.tr (copyLane L X c 2)).countP isElectEv=0) :
    let l := Ring.ready.obj L c s
    Due Q L X g (copyLane L X c 2) (issuesTo l)
      (dueCp (preload Q L c s) (okPolls l (X.tr g)+1) 2) := by
  obtain ⟨rfl,q,sc,hn⟩ := hw
  let c := g/L.block
  let lo := Iface.preloadCount Q L c
  let r := pollRound 2462 (X.tr g)
  have ⟨bound,clock⟩ := Mma.Export.wait_time hp hf hn (Or.inl rfl)
  change r<Lib.blocksOf Q L c at bound
  change threadTime _ _ _=Lib.Slots.readyWait r at clock
  have hg := hn.lt
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cta,warp⟩ := leader_warp (X := X) hp hc (by decide : 6<8)
  by_cases short : r<lo
  · obtain ⟨Y,hY,pref,he⟩ := hn
    obtain ⟨_,_,_,hw,_,slot,_⟩ := wait_info (r := .ready) (rows Y hY) hg he
    have ord := poll_count (r := .ready) (rows Y hY) hg hw s (X.tr g).length
    change okPolls _ ((Y.tr g).take _) = visits 0 (pollRound 2462 ((Y.tr g).take _)) s at ord
    rw [pref] at ord
    change s=slot3 (pollRound 2462 ((Y.tr g).take _)) at slot
    rw [pref] at slot
    have maxPre : lo≤3 := Nat.min_le_left ..
    have sv : s.val=r := by
      rw [slot]; exact Nat.mod_eq_of_lt (by omega)
    have occupied : preload Q L c s=1 := ite_eq_left (sv ▸ short)
    change okPolls _ _ = visits 0 r s at ord
    have none : visits 0 r s=0 := by unfold visits; rw [sv]; omega
    rw [none] at ord
    dsimp only [c] at occupied
    simp [Due,dueCp,occupied,ord]
  · change (X.tr (leader L X c 6)).countP isElectEv=0 at zero
    have work : Iface.preloadCount Q L ((leader L X c 6)/L.block) <
        Lib.blocksOf Q L ((leader L X c 6)/L.block) := by rw [cta]; omega
    obtain ⟨live,early⟩ := Export.loader_pre_elect hp hX hf words hy warp work hu zero
    rw [cta] at early
    have order : Lib.Slots.readyCopy lo 0 false < Lib.Slots.readyWait r := by
      change 1000+400*lo+6<1000+400*r+100+1
      omega
    exact ⟨fun k pc he => (live k pc he).elim,fun late => False.elim
      ((early.trans_lt order).not_ge (clock ▸ late))⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
