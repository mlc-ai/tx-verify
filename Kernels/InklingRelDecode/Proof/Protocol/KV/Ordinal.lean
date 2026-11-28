-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.KV.Lag
import Kernels.InklingRelDecode.Proof.Lib.ShuffleCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.Coll
import Kernels.InklingRelDecode.Proof.Mma.Export.Count

import Kernels.InklingRelDecode.Proof.Protocol.KV.CommitBudget
import Kernels.InklingRelDecode.Proof.Protocol.Shared.ReadValues

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
open PTX PTX.Flow PTX.Sched MbarRow

/-- An empty-slot notification is behind the ready waiter's next use, even if
the elected producer's trace is longer. Every prior broadcast requires the waiter. -/
theorem commit_before_wait {Q L m X g c s k pc sp} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (followed : ∀ Y, Consistent L kernel Assumptions.all m Y → Follow Q L Y)
    (rows : ∀ Y, Consistent L kernel Assumptions.all m Y → MbarRows Q L Y)
    (wait : Waiting L m X .ready c s g)
    (he : X.get (leader L X c 7,k)=some ⟨pc,.tc (.commit sp)⟩)
    (obj : sp.mbar=Ring.empty.obj L c s) :
    ((X.tr (leader L X c 7)).take k).countP (commitsTo sp.mbar) <
      okPolls (Ring.ready.obj L c s) (X.tr g) := by
  obtain ⟨rfl,q,sc,hn⟩ := wait
  let c := g/L.block
  let y := leader L X c 7
  have hg := hn.lt
  have hc : c<L.grid := Nat.div_lt_of_lt_mul (by simpa [Launch.threads,Nat.mul_comm] using hg)
  obtain ⟨hy,cta,warp⟩ := leader_warp (X := X) hp hc (by decide : 7<8)
  obtain ⟨Y,hY,pref,evt⟩ := id hn
  obtain ⟨_,_,_,gw,_,_,_⟩ := wait_info (r := .ready) (rows Y hY) hg evt
  have same : SameWarp L g y := ⟨⟨hg,hy,cta.symm⟩,gw.trans warp.symm⟩
  have count := Lib.shuffle_credit hX same hn he
  have operand : Frame.MbarOf ⟨pc,.tc (.commit sp)⟩ (Ring.empty.obj L c s) := by
    obtain ⟨_,rfl,_⟩ := Mma.Export.commit hp hX (followed X hX) warp he
    exact ⟨0,by rw [←obj]; simp [TcCommit.target]⟩
  obtain bad|⟨_,_,bad⟩|⟨site,_,_⟩ := empty_use (rows X hX) hy he operand
  · cases bad
  · cases bad
  change pc=2546 at site
  subst pc
  have spent := commit_budget hp hX (followed X hX) (rows X hX)
    (fun h => Protocol.Shared.role_bytes hp hX h) he obj
  have producer := Mma.Export.empty_shuffles hp hX (followed X hX) warp he
  have waiter := Mma.Export.poll_shuffles hp hY (followed Y hY) gw evt (by simp) (.inl rfl)
  change ((Y.tr g).take _).countP Execution.isShfl =
    1+pollRound 2462 ((Y.tr g).take _)+(pollRound 2462 ((Y.tr g).take _)-1) at waiter
  rw [pref] at waiter
  have a := poll_count (r := .ready) (rows X hX) hy warp s k
  have b := poll_count (r := .ready) (rows Y hY) hg gw s (X.tr g).length
  change okPolls _ ((X.tr y).take k)=visits 0 (pollRound 2462 ((X.tr y).take k)) s at a
  change okPolls _ ((Y.tr g).take _)=visits 0 (pollRound 2462 ((Y.tr g).take _)) s at b
  rw [pref] at b
  rw [cta] at a
  dsimp only at producer
  change 1+pollRound 2462 ((X.tr y).take k)+(pollRound 2462 ((X.tr y).take k)-1) ≤
    ((X.tr y).take k).countP Execution.isShfl at producer
  change ((X.tr y).take k).countP Execution.isShfl ≤ _ at count
  change _+1 ≤ okPolls (Ring.ready.obj L c s) ((X.tr y).take k) at spent
  rw [a] at spent
  rw [b]
  have rounds : pollRound 2462 ((X.tr y).take k) ≤ pollRound 2462 (X.tr g) := by omega
  apply Nat.lt_of_lt_of_le (Nat.lt_of_succ_le spent)
  unfold visits
  exact Nat.sub_le_sub_right (Nat.div_le_div_right (Nat.sub_le_sub_right
    (Nat.add_le_add_right (Nat.add_le_add_left rounds _) _) _)) _

end PTX.Kernels.InklingRelDecode.Proof.Protocol.KV
