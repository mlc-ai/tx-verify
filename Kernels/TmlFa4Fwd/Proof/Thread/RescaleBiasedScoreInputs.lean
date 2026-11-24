-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescalePackedInput
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasFma
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedMaximum
import Kernels.TmlFa4Fwd.Flow.Code.Part086

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private theorem biasCompareInPrefix {l : Launch} {g : Nat} {t : TState}
    {events : List Event} {ending : Option TState} {target : Event}
    (ht : At t 5535 []) (hRun : Run kernel Assumptions.all l g t events ending)
    (hHead : events[0]? = some target) (hDifferent : target.pc ≠ 5535) :
    ∃ u, At u (repeatedMaxStart true) [] ∧
      Run kernel Assumptions.all l g u events ending ∧
      (∀ r, r ≠ 634 → u.regs r = t.regs r) ∧
      (∃ mixed : Bool, u.regs 634 = some (.pred mixed)) ∧ Tau kernel Assumptions.all l g t u := by
  have hReach : ∃ s, Tau kernel Assumptions.all l g t s := by
    have hasTau {u : TState} {e : Event} {o : Option TState}
        (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
        (he : EStep kernel Assumptions.all l g u e o) (h : e = target) :
        ∃ s, Tau kernel Assumptions.all l g t s := by
      rcases Relation.ReflTransGen.cases_head hPath with rfl | ⟨s,hs,_⟩
      · exact (hDifferent (h ▸ (estep_source_pc he).trans ht.1)).elim
      · exact ⟨s,hs⟩
    cases hRun with
    | nil => simp at hHead
    | step hPath he _ => exact hasTau hPath he (Option.some.inj hHead)
    | last hPath he => exact hasTau hPath he (Option.some.inj hHead)
  obtain ⟨u,hu⟩ := hReach
  obtain ⟨ins,hCode,_,hLocal⟩ := tauScoreSource hu
  rw [ht.1,Flow.code_5535] at hCode
  obtain rfl := Option.some.inj hCode
  rcases hLocal with ⟨rfl,hGuard⟩ | ⟨_,_,hExec⟩
  · cases hGuard
  · rcases scoreExecLocal hExec with hFrame | ⟨seg,hSite,hM,hS⟩
    · have hp : u.pc = t.pc+1 := hFrame.pc.resolve_right (by simp [BrxTarget])
      have hAt : At u (repeatedMaxStart true) [] :=
        ⟨hp.trans (congrArg (·+1) ht.1),hFrame.sub.trans ht.2.1,hFrame.acc.trans ht.2.2.1,
          hFrame.fault.trans ht.2.2.2.1,trivial⟩
      have hMore : events ≠ [] := by intro e; simp [e] at hHead
      refine ⟨u,hAt,hRun.after_local_nonempty (.single hu) hMore,
        fun r hR => hFrame.regs r (by change r ∉ [634]; simpa only [List.mem_singleton] using hR),
        ?_,hu⟩
      have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1 ▸ (by decide)
      rw [Assumptions.execLocalA_all_eq_numeric,
        Assumptions.execLocalA_eq_nil hOff rfl,execLocalA_nil,execLocal_int rfl] at hExec
      change (do
        let a ← readBits l g t 32 (.reg 7249)
        let b ← readBits l g t 32 (.reg 1361)
        pure (next (setReg t 634 (.pred (compare .lt .u 32 a b))))) = .ok u at hExec
      cases ha : readBits l g t 32 (.reg 7249) with
      | error f => simp [ha,bind,Except.bind] at hExec
      | ok a =>
        cases hb : readBits l g t 32 (.reg 1361) with
        | error f => simp [ha,hb,bind,Except.bind] at hExec
        | ok b =>
          simp [ha,hb,bind,Except.bind,pure,Except.pure] at hExec
          obtain rfl := hExec
          exact ⟨compare .lt .u 32 a b,by simp [next,setReg]⟩
    · exact ((by decide : 5535 ∉ Assumptions.swExp2Sites) (ht.1 ▸ hSite)).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) {g pos : Nat}
    {t : TState} {ending : Option TState} {a : Acc} {data : List Byte} (old : Option ℝ)
    (bias : Nat → Option ℝ) (dot : Nat → ℝ) (ht : At t (biasBodyStart true) [])
    (hInvScale : readERealPair l g t (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hBias : ∀ i : Fin 16, BiasUnpacked true i t (fun k =>
      biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))))
    (hDots : ∀ pair < 64,
      readERealPair l g t (.reg (7367+pair)) =
        some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal))))
    (hOld : t.regs 7251 = some (scoreValue old)) (hScale : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (he : StatisticsStore X (g,pos) (rescaleStore true) a data)
include hp old bias dot ht hInvScale hBias hDots hOld hScale hr he

/-- Canonical raw QK and Bias values at the actual affine entry supply a candidate
maximum and the typed rescale result. The score pairs cover physical padding as well. -/
theorem rescaleBiasedArithmeticEntryOfAffineInputsWithPath :
    let scores := fun col => affineScore (abiFloat p.invScaleBits) (dot col) (bias col)
    RescaleArithmeticEntryWith p l X (g,pos) true (fun w =>
      (∀ i ∈ biasBodyItems true,
        w.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
          (scoreValue (scores (2*(i.qk-7367)+1))))) ∧
      (∃ mixed : Bool, w.regs 634 = some (.pred mixed)) ∧
      (∀ r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes ++ 634 :: rescaleMaxWrites true,
        w.regs r = t.regs r) ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t w) := by
  have hHead : ((X.tr g).drop pos)[0]? =
      some ⟨(statsStore (rescaleStore true)).pc,.wr a data⟩ := by
    rw [List.getElem?_drop,Nat.add_zero]
    exact he
  have hPresent : (X.tr g).drop pos ≠ [] := by
    intro h
    simp [h] at hHead
  let scores := fun col => affineScore (abiFloat p.invScaleBits) (dot col) (bias col)
  obtain ⟨u,hu,hFma,hKeep,hScores⟩ :=
    laterBiasBodyOfCanonicalInputs hp bias dot ht hInvScale hBias hDots
  obtain ⟨v,hv,hTail,hFrame,hMixed,hCompare⟩ := biasCompareInPrefix hu
    (hr.after_local_nonempty hFma hPresent) hHead (by change 5682 ≠ 5535; decide)
  have hScaleV : v.regs 7132 = some (b32 p.scaleLog2Bits) :=
    (hFrame _ (by decide)).trans ((hKeep _ (by decide +kernel)).trans hScale)
  have hOldV : v.regs 7251 = some (scoreValue old) :=
    (hFrame _ (by decide)).trans ((hKeep _ (by decide +kernel)).trans hOld)
  have hScoresV : ∀ i ∈ biasBodyItems true,
      v.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1)))) := by
    intro i hi
    have hNot : i.result ≠ 634 := by
      have hKeys : (biasBodyItems true).all (fun x => x.result != 634) = true := by decide +kernel
      exact bne_iff_ne.mp (List.all_eq_true.mp hKeys _ hi)
    exact (hFrame _ hNot).trans (hScores i hi)
  have hEntry := rescaleArithmeticEntryOfPackedScoresWithFrame hp true
    (biasCombinedScores scores old) hv
    (biasedMaximumWords scores old hScoresV hOldV) hScaleV hTail he
  refine hEntry.mono (fun w hw => ⟨?_,?_,?_,?_⟩)
  · intro i hi
    have hFree : i.result ∉ rescaleMaxWrites true := by
      have hAudit : (biasBodyItems true).all (fun item =>
          !(rescaleMaxWrites true).contains item.result) = true := by decide +kernel
      simpa using List.all_eq_true.mp hAudit i hi
    exact (hw.2 _ hFree).trans (hScoresV i hi)
  · obtain ⟨mixed,hMixed⟩ := hMixed
    exact ⟨mixed,(hw.2 _ (by decide +kernel)).trans hMixed⟩
  · intro r hr
    simp only [List.mem_append,List.mem_cons,not_or] at hr
    exact (hw.2 _ hr.2.2).trans ((hFrame _ hr.2.1).trans (hKeep _ hr.1))
  · exact (hFma.tail hCompare).trans hw.1

theorem rescaleBiasedArithmeticEntryOfAffineInputsWithPairs :
    let scores := fun col => affineScore (abiFloat p.invScaleBits) (dot col) (bias col)
    RescaleArithmeticEntryWith p l X (g,pos) true (fun w =>
      (∀ i ∈ biasBodyItems true,
        w.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
          (scoreValue (scores (2*(i.qk-7367)+1))))) ∧
      (∃ mixed : Bool, w.regs 634 = some (.pred mixed)) ∧
      ∀ r ∉ (biasBodyItems true).flatMap BiasAffineItem.writes ++ 634 :: rescaleMaxWrites true,
        w.regs r = t.regs r) := by
  exact (rescaleBiasedArithmeticEntryOfAffineInputsWithPath hp old bias dot ht hInvScale
    hBias hDots hOld hScale hr he).mono (fun _ h => ⟨h.1,h.2.1,h.2.2.1⟩)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
