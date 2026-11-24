-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Open
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane's counts before an event, in the trace

`soft_counts`: an event of a softmax lane that is not undefined behaviour is fired from the startup
or from a role state whose reference counts are the trace's counts of the role's classes (the
ledger). The class of an arrival, a successful poll and a named-barrier event is the trace's
(`arrivals`, `okPolls`, `isBarId`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

theorem soft_stS (hw : Prologue.warpIndex L g < 8) :
    Softmax.stS L g = 8 * (Prologue.warpIndex L g / 4) := by
  have key : ∀ w < 8, (if Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 then 8 else 0) =
      8 * (w / 4) := by
    decide
  exact key _ hw

theorem soft_nbW (hw : Prologue.warpIndex L g < 8) :
    (Softmax.nbW L g).toNat = Prologue.warpIndex L g + 3 := by
  have key : ∀ w < 8, (Epilogue.addi (Epilogue.add32 (Epilogue.sub32 (BitVec.ofNat 64 w)
      (Epilogue.andi (Epilogue.add32 (BitVec.ofNat 64 w)
        (Epilogue.shru (Epilogue.shrs (BitVec.ofNat 64 w) 31) 30)) (-4)))
      (Epilogue.sel (Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3) (Epilogue.i32 4)
        (Epilogue.i32 0))) 3).toNat = w + 3 := by
    decide
  exact key _ hw

/-- The stage's barrier at offset `a` of a softmax lane as an object of its CTA. -/
theorem soft_bl (hw : Prologue.warpIndex L g < 8) (a : Nat) :
    Softmax.bl L g a = obj L g (8 * (Prologue.warpIndex L g / 4) + a) := by
  simp only [Softmax.bl, soft_stS hw]

theorem soft_okPolls (hw : Prologue.warpIndex L g < 8) (a : Nat) :
    okPolls (obj L g (8 * (Prologue.warpIndex L g / 4) + a)) ((X.tr g).take k) =
      ((X.tr g).take k).countP (cls L g (.soft (.acquire a))) := by
  rw [← soft_bl hw]
  refine List.countP_congr fun e _ => ?_
  have hw' : g % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | wait m par ok acq sc =>
    cases ok <;> simp [okPoll, sourceWaitSuccess, cls, Softmax.cls, Softmax.Cnt.pointed, hw']
  | _ => simp [okPoll, sourceWaitSuccess, cls, Softmax.cls]

theorem soft_arrivals (hw : Prologue.warpIndex L g < 8) {a : Nat} (ha : a ≠ 112) :
    arrivals (obj L g (8 * (Prologue.warpIndex L g / 4) + a)) ((X.tr g).take k) =
      ((X.tr g).take k).countP (cls L g (.soft (.arrive a))) := by
  rw [← soft_bl hw]
  refine List.countP_congr fun e _ => ?_
  have hw' : g % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [arrivesOn, sourceArrive, cls, Softmax.cls, Softmax.Cnt.pointed, hw', ha]

theorem soft_isBarId (hw : Prologue.warpIndex L g < 8) :
    ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g + 3)) =
      ((X.tr g).take k).countP (cls L g (.soft .nb)) := by
  refine List.countP_congr fun e _ => ?_
  have hw' : g % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw', soft_nbW hw]

theorem soft_isBar2 (hw : Prologue.warpIndex L g < 8) :
    ((X.tr g).take k).countP (Execution.isBarId 2) =
      ((X.tr g).take k).countP (cls L g (.soft .bar2)) := by
  refine List.countP_congr fun e _ => ?_
  have hw' : g % L.block / 32 < 8 := hw
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp [Execution.isBarId, cls, Softmax.cls, Softmax.Cnt.pointed, hw']

/-- **A softmax lane's counts before an event.** -/
theorem soft_counts (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g < 8)
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) :
    (∃ s, Startup.Ev L g s e ∧ exit L g s = none) ∨
      ∃ d c rb rp ns nv, Softmax.RefQ p L g d c rb rp ∧ SmWarp.SFits p L g d ns nv ∧
        Softmax.Ev p L g d e ∧
        ∀ c', c'.pointed = true → ((X.tr g).take k).countP (cls L g (.soft c')) = c c' := by
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · exact .inl ⟨s, hev, hi.2⟩
  · obtain ⟨⟨c, ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, hF⟩ := hR.2 h0
    exact .inr ⟨d, c, rb, rp, _, _, hQ, hF, hev.1, fun c' hc' => by rw [count hσ, ← hLk c' hc']⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
