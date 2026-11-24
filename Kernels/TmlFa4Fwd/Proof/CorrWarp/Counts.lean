-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A correction lane's counts before an event, in the trace

`corr_counts`: an event of a correction lane that is not undefined behaviour is fired from the
startup or from a role state whose reference counts are the trace's counts of the role's classes
(the ledger). The class of an arrival, a successful poll and a named-barrier event is the trace's
(`arrivals`, `okPolls`, `isBarId`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

theorem corr_nbW (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (s : Fin 2) : (Correction.nbOf L g s).toNat = Prologue.warpIndex L g - 5 + 4 * s.val := by
  have key : ∀ w, 8 ≤ w → w < 12 → (Epilogue.addi (Epilogue.andi (BitVec.ofNat 64 w) 3) 3).toNat =
      w - 5 ∧ (Epilogue.addi (Epilogue.andi (BitVec.ofNat 64 w) 3) 7).toNat = w - 1 := by
    intro w h1 h2
    interval_cases w <;> decide
  obtain ⟨k0, k1⟩ := key _ hw (by omega)
  fin_cases s
  · exact k0
  · have h : (Correction.nbOf L g 1).toNat = Prologue.warpIndex L g - 1 := k1
    show (Correction.nbOf L g 1).toNat = Prologue.warpIndex L g - 5 + 4 * 1
    rw [h]
    omega

theorem corr_okPolls (o : Nat) :
    okPolls (obj L g o) ((X.tr g).take k) =
      ((X.tr g).take k).countP (cls L g (.corr (.acquire o))) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | wait m par ok acq sc =>
    cases ok <;> simp [okPoll, sourceWaitSuccess, cls, Correction.cls, Correction.bl]
  | _ => simp [okPoll, sourceWaitSuccess, cls, Correction.cls]

theorem corr_arrivals (o : Nat) :
    arrivals (obj L g o) ((X.tr g).take k) =
      ((X.tr g).take k).countP (cls L g (.corr (.arrive o))) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [arrivesOn, sourceArrive, cls, Correction.cls, Correction.bl]

theorem corr_isBarId (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (s : Fin 2) :
    ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * s.val)) =
      ((X.tr g).take k).countP (cls L g (.corr (.nb s))) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [Execution.isBarId, cls, Correction.cls, corr_nbW hw hw1,
    beq_iff_eq, decide_eq_true_eq]

theorem corr_isBar2 :
    ((X.tr g).take k).countP (Execution.isBarId 2) =
      ((X.tr g).take k).countP (cls L g (.corr .bar2)) := by
  refine List.countP_congr fun e _ => ?_
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Correction.cls]

/-- **A correction lane's counts before an event.** -/
theorem corr_counts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (∃ s, Startup.Ev L g s e ∧ exit L g s = none) ∨
      ∃ d : Correction.Control.D, ∃ c r ℓ ns nv, Correction.RefQ p L g d c r ℓ ∧ CorrWarp.CFits p
          L g d ns nv ∧
        Correction.Control.Ev p L g d e ∧
        ∀ c', ((X.tr g).take k).countP (cls L g (.corr c')) = c c' := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev, -⟩
  · exact .inl ⟨s, hev, hi.2⟩
  · obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hR h0
    exact .inr ⟨d, _, r, ℓ, _, _, hQ, hF, hev, fun c' => count hσ _⟩

theorem corr_counts_nonvote (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hv : ∀ pred b, e.kind ≠ .vote (2^32-1) pred b) :
    (∃ s, Startup.Ev L g s e ∧ exit L g s = none) ∨
      ∃ d c r ℓ ns nv, Correction.RefQ p L g d c r ℓ ∧ CorrWarp.CFits p L g d ns nv ∧
        Correction.Ev p L g d e ∧
        ∀ c', ((X.tr g).take k).countP (cls L g (.corr c')) = c c' := by
  rcases corr_counts hp hX hFw hw hw1 he hub with h | ⟨d,c,r,l,ns,nv,hQ,hF,hE,hc⟩
  · exact .inl h
  · rcases hE.data_or_vote with h | ⟨pred,b,h⟩
    · exact .inr ⟨d.scheduler,c,r,l,ns,nv,hQ,hF,h,hc⟩
    · exact (hv pred b h).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof
