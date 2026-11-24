-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.StageRead
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
import Kernels.TmlFa4Fwd.Proof.SmWarp.Src
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The softmax lanes' polls at their shared reads -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

/-- **A shared read of a softmax lane** is a bias read: one more poll of the bias slot than
stage-barrier events precede it. -/
theorem soft_bias_rd (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h < 8) {pc : Nat} {a : Acc}
    {bs : List (Option Byte)} (he : X.get (h, k) = some ⟨pc, .rd a bs⟩)
    (hsh : a.loc.space = .shared) :
    okPolls (sobj L h 320) ((X.tr h).take k) =
      ((X.tr h).take k).countP
        (Execution.isBarId (stageId (Prologue.warpIndex L h / 4))) + 1 := by
  rcases SmWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev⟩
  · exact (start_mem hev hi.2 trivial).elim
  have hF : SmWarp.SFits p L h d (n .shfl) (n .vote) := (hR.2 h0).2
  have hFE := hF.1
  have hevR := SmWarp.fired_r hp hX he hσ (fun _ => nofun)
  have hev1 := hev.1
  have hsite : ∃ b c, d.scheduler.site = .bld b c := by
    by_contra hcon
    have hin : InWord p a := by
      cases hs : d.scheduler.site <;> simp only [Softmax.Ev, hs] at hev1
      case word | q0 | q1 =>
        simp only [SmWarp.EvR, hs] at hevR
        exact Epilogue.sched_rd hp hFE hevR rfl
      case uk =>
        simp only [SmWarp.EvR, hs] at hevR
        rcases hevR with ⟨bs, hk⟩ | ⟨f, h⟩
        · simp only [Epilogue.Fits, SmWarp.toE, hs, SmWarp.epi] at hFE
          obtain ⟨R, bal, hC, -, -⟩ := hFE
          exact Epilogue.usedK_rd rfl hk (Epilogue.usedK_addr hp hC)
        · cases h
      case bld b c => exact (hcon ⟨b, c, hs⟩).elim
      all_goals exfalso
      all_goals try simp only [Epilogue.Ev, Softmax.Site.toE, Softmax.tcLdOrUb] at hev1
      all_goals repeat' split at hev1
      all_goals simp_all
    obtain ⟨-, ⟨_, -, hl⟩ | ⟨_, -, hl⟩ | ⟨_, -, _, -, hl⟩⟩ := hin <;>
      (rw [hl] at hsh; cases hsh)
  obtain ⟨b, c, hs⟩ := hsite
  obtain ⟨-, -, hpolls, -⟩ := soft_bias_read hp hX hFw he hσ hs rfl
  exact hpolls

end
end PTX.Kernels.TmlFa4Fwd.Proof
