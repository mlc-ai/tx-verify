-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Machine
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Arrive
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.BitVec
import Kernels.TmlFa4Fwd.Proof.Top.Register

@[expose] public section

/-! # A correction lane's Tensor Memory accesses follow one barrier-2 event

At a rescale load or store, or a final load (`Correction.Site.isTc`), the correction reference
counts one barrier-2 event (`RefQ.cnt`: one barrier-2 point before the site, none in a round:
`ctc_bar2`), the thread's ledger counts the same (`CorrWarp.rc`), and the ledger's barrier-2
class is `isBarId 2` (`cls_corr_bar2`). So the lane has made exactly one barrier-2 event before
such a state (`corr_tc_bar2`): its `bar1` rendezvous. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The correction sites of a Tensor Memory load or store. -/
def Correction.Site.isTc : Correction.Site → Bool
  | .rld _ _ | .rldw _ _ | .rst _ _ | .fld _ _ => true
  | _ => false

theorem ctc_bar2_all :
    (Correction.allSites.filter Correction.Site.isTc).all (fun s =>
      (Correction.ptsOf .bar2).countP (Correction.before s) == 1) = true ∧
    (Correction.ptsOf .bar2).countP Correction.inRound = 0 := by
  decide +kernel

/-- **One barrier-2 point before a Tensor Memory site, none in a round.** -/
theorem ctc_bar2 {s : Correction.Site} (hs : s.isTc = true) (r : Nat) :
    Correction.passed (Correction.ptsOf .bar2) s r = 1 := by
  obtain ⟨h1, h2⟩ := ctc_bar2_all
  have := List.all_eq_true.mp h1 s (List.mem_filter.mpr ⟨Correction.mem_allSites s, hs⟩)
  simp only [beq_iff_eq] at this
  simp only [Correction.passed, this, h2, Nat.mul_zero, Nat.add_zero]

/-- The ledger's barrier-2 class of the correction warps is `isBarId 2`. -/
theorem cls_corr_bar2 : cls L g (.corr .bar2) = Execution.isBarId 2 := by
  funext e
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | bar id cnt mode =>
    simp only [cls, Correction.cls, Execution.isBarId]
    by_cases hi : id = 2 <;> simp [hi]
  | _ => rfl

/-- **A correction lane at a Tensor Memory site has made one barrier-2 event.** -/
theorem corr_tc_bar2 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {k : Nat} {e : Event}
    {d : Correction.Control.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hs : d.scheduler.site.isTc = true) :
    ((X.tr g).take k).countP (Execution.isBarId 2) = 1 := by
  have hg := Frame.lt_of_get hX he
  have hJ : JR p L g (CorrWarp.cinj p L g d n) := (goodR hp hX hFw hg k).2 _ hσ
  have hw := jr_corr hJ (Prologue.warpIndex_lt hp g)
  have hR := jr_corrRef hJ hw
  obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := (hR (ub_zero hX he hσ)).1
  have h1 := hQ.cnt .bar2 (by decide)
  rw [ctc_bar2 hs] at h1
  rw [← cls_corr_bar2 (L := L) (g := g), count hσ]
  exact h1

end
end PTX.Kernels.TmlFa4Fwd.Proof
