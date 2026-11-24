-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # A softmax lane's Tensor Memory accesses follow one barrier-2 event

At a score load or P store site (`Softmax.Site.isTc`) the softmax reference counts one barrier-2
event (`RefQ.cnt`: the barrier-2 points before the site, one, and none in a round: `tc_bar2`),
the thread's ledger counts the same (`SmWarp.Linked`), and the ledger's barrier-2 class is
`isBarId 2` (`cls_soft_bar2`). So the lane has made exactly one barrier-2 event before such a state
(`soft_tc_bar2`): its `bar1` rendezvous. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The softmax sites of a Tensor Memory load or store. -/
def Softmax.Site.isTc : Softmax.Site → Bool
  | .sld _ _ | .sldw _ | .pst _ _ => true
  | _ => false

theorem tc_bar2_all (b : Bool) :
    (Softmax.allSites.filter Softmax.Site.isTc).all (fun s =>
      (Softmax.ptsOf b .bar2).countP (Softmax.before s) == 1) = true ∧
    (Softmax.ptsOf b .bar2).countP Softmax.inBias = 0 ∧
    (Softmax.ptsOf b .bar2).countP Softmax.inPlain = 0 := by
  cases b <;> decide +kernel

/-- **One barrier-2 point before a Tensor Memory site, none in a round.** -/
theorem tc_bar2 (b : Bool) {s : Softmax.Site} (hs : s.isTc = true) (rb rp : Nat) :
    Softmax.passed (Softmax.ptsOf b .bar2) s rb rp = 1 := by
  obtain ⟨h1, h2, h3⟩ := tc_bar2_all b
  have := List.all_eq_true.mp h1 s (List.mem_filter.mpr ⟨Softmax.mem_allSites s, hs⟩)
  simp only [beq_iff_eq] at this
  simp only [Softmax.passed, this, h2, h3, Nat.mul_zero, Nat.add_zero]

/-- The ledger's barrier-2 class of the softmax warps is `isBarId 2`. -/
theorem cls_soft_bar2 (h8 : g % L.block / 32 < 8) :
    cls L g (.soft .bar2) = Execution.isBarId 2 := by
  funext e
  have hp : Softmax.Cnt.bar2.pointed = true := rfl
  simp only [cls, hp, h8, decide_true, Bool.and_true]
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | bar id cnt mode =>
    simp only [Softmax.cls, Execution.isBarId]
    by_cases hi : id = 2 <;> simp [hi]
  | _ => rfl

/-- **A softmax lane at a Tensor Memory site has made one barrier-2 event.** -/
theorem soft_tc_bar2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k : Nat} {e : Event}
    {d : Softmax.Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)))
    (hs : d.scheduler.site.isTc = true) :
    ((X.tr g).take k).countP (Execution.isBarId 2) = 1 := by
  have hg := Frame.lt_of_get hX he
  have hJ : JR p L g (SmWarp.sinj p L g d n) := (goodR hp hX hFw hg k).2 _ hσ
  have h8 := jr_soft hJ
  have hR : SmWarp.Ref p L (Prologue.warpIndex L g) g (SmWarp.sinj p L g d n) := by
    simpa only [JR_eq, h8, ite_true] using hJ
  obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := hR.2 (ub_zero hX he hσ)
  have h1 := hQ.cnt .bar2 rfl
  rw [tc_bar2 _ hs] at h1
  rw [← cls_soft_bar2 (by simpa [Prologue.warpIndex] using h8), count hσ, ← hLk .bar2 rfl]
  exact h1

end
end PTX.Kernels.TmlFa4Fwd.Proof
