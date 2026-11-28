-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.KvPreload
public import Lemmas.Flow.PollRounds
import Kernels.InklingRelDecode.Proof.Common.WorkerEvent
public import Kernels.InklingRelDecode.Proof.Common.Occurs
import Kernels.InklingRelDecode.Proof.Mma.Shape

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g k pc q : Nat}
  {l : Loc} {ok acq : Bool} {sc : MbarScope}

private theorem poll_pc (s : Site) :
    (s.pc = 2462 → s = .kvWait) ∧ (s.pc = 2510 → s = .pWait) := by
  cases s <;> first | decide | (rename_i j; fin_cases j <;> decide)

/-- Both MMA poll objects, including the parity fed to try_wait, are determined by
the successful polls preceding the observation on this lane. -/
public theorem poll (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hw : g % L.block / 32 = 7) (hs : pc = 2462 ∨ pc = 2510)
    (he : Occurs L X g k ⟨pc, .wait l q ok acq sc⟩) :
    let n := pollRound pc ((X.tr g).take k)
    acq = true ∧ sc = .cta ∧
      (pc = 2462 ∧ l = Iface.kvReadyLoc L (g / L.block) ⟨n % 3, by omega⟩ ∧ q = n / 3 % 2 ∨
       pc = 2510 ∧ l = ⟨.shared, g / L.block, L.sharedBase + Iface.pReady ⟨n % 2, by omega⟩⟩ ∧
         q = n / 2 % 2) := by
  obtain ⟨w,x,⟨s,i,v⟩,t,ins,o,hat,_,hpc,hc,fire,hq,hp'⟩ :=
    mma_occ hp hX hf hw he (fun _ => nofun) (by change 2422 < pc; omega)
      (by change pc < 2557; omega)
  change pc = s.pc at hpc
  rcases hs with rfl | rfl
  · obtain rfl := (poll_pc s).1 hpc.symm
    obtain ⟨_,hk⟩ := ready_poll hp hat hc fire
    obtain ⟨hl,hpar,_,ha,hsc⟩ := Kind.wait.inj hk
    change pollRound 2462 _ = i at hq
    exact ⟨ha,hsc,.inl ⟨rfl,hq.symm ▸ hl,hq.symm ▸ hpar⟩⟩
  · obtain rfl := (poll_pc s).2 hpc.symm
    obtain ⟨_,hk⟩ := p_poll hp hat hc fire
    obtain ⟨hl,hpar,_,ha,hsc⟩ := Kind.wait.inj hk
    change pollRound 2510 _ = i - 1 at hp'
    dsimp only
    simp only [Iface.kvReadyLoc, Iface.kvReady, Iface.pReady, hp']
    exact ⟨ha,hsc,.inr ⟨trivial,hl,hpar⟩⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
