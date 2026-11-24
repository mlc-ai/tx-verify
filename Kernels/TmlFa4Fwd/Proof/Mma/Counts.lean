-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # An MMA lane's counts before an event, in the trace

`mma_counts`: an event of a lane of warp 12 that is not undefined behaviour is fired from the
startup, the allocation prefix, or a role state with its reference counts, which are the trace's
(`mma_okPolls`, `mma_commits`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

theorem mma_okPolls (l : Loc) :
    okPolls l ((X.tr g).take k) = ((X.tr g).take k).countP (cls L g (.mma (.acquire l))) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | wait m par ok acq sc => cases ok <;> simp [okPoll, sourceWaitSuccess, cls, Mma.cls]
  | _ => simp [okPoll, sourceWaitSuccess, cls, Mma.cls]

theorem mma_commits (l : Loc) :
    ((X.tr g).take k).countP (commitsTo l) =
      ((X.tr g).take k).countP (cls L g (.mma (.commit l))) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | tc t => cases t <;> simp [commitsTo, cls, Mma.cls]
  | _ => simp [commitsTo, cls, Mma.cls]

/-- **An MMA lane's counts before an event.** -/
theorem mma_counts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 12)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (∃ s n, StartAt L 12 s n ∧ Startup.Ev L g s e ∧ exit L g s = none) ∨ Mma.PreEv e ∨
      ∃ d n r w, Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)) ∧
        Mma.RefQ p L g d.site.ord d.v (Mma.rc n) r w ∧ (d.site.ord ∈ Mma.cmQ → w = true) ∧
        Mma.MFits p L g d (n .shfl) (n .vote) ∧ Mma.Ev p L g d e := by
  rcases Mma.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, hJ, hi, hev⟩ | ⟨s, n, -, -, -, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · have hR : Mma.Ref p L g (.inl s, n) := by
      have h8 : ¬ Prologue.warpIndex L g < 8 := by omega
      simp only [JR_eq, h8, ite_false] at hJ
      unfold RefAll at hJ
      simpa only [hw, ite_true] using hJ
    exact .inl ⟨s, n, hR.1, hev, hi.2⟩
  · exact .inr (.inl hev)
  · obtain ⟨⟨r, w, hQ, hc⟩, hF⟩ := hR h0
    exact .inr (.inr ⟨d, n, r, w, hσ, hQ, hc, hF, hev⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof
