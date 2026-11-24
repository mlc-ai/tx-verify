-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasBoxes
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmBiasExpectationProgress
import Lemmas.Flow.LoadShared
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The election that selects the issuer of a warm stage's transaction expectation. -/
def warmBiasExpectSite (stage : Fin 2) : Fin 6 :=
  ⟨3*stage.val,by have := stage.isLt; omega⟩

private theorem warmStageOneExpectationOut {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {t : Nat} {s : TState}
    (hs : At s 1182 [(2054,b32 32768),(2535,b32 l.sharedBase)]) :
    out kernel Assumptions.all l t s = .ev (.arrive (biasReadyObject l (t/l.block) 1)
      32768 (next (mbarStateDest s (some 7703))) 1 true .cta) := by
  rw [loaderOutCore (by rw [hs.1]; decide) (by rw [hs.1]; decide)]
  rw [out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_1182) rfl rfl]
  have hBase : l.sharedBase+328 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+328)%8 = 0 := by have := hp.shared.1; omega
  have hEff : effAddr l t s .shared 2535 328 = .ok (biasReadyObject l (t/l.block) 1) := by
    simpa [biasReadyObject] using effAddr_b32_off (off := 328) hs.2.2.2.2.2.1 hBase
  have hLoc : mbarLoc l t s 2535 328 = .ok (biasReadyObject l (t/l.block) 1) := by
    simp [mbarLoc,hEff,biasReadyObject,hAlign,bind,Except.bind,pure,Except.pure]
  have hOne : readBits l t s 32 (.imm 1) = .ok 1#64 := rfl
  simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hs.2.2.2.2.1 (by decide),
    hOne,bind,Except.bind,pure,Except.pure,ofExec]

private theorem warmExpectCode (stage : Fin 2) :
    kernel.code[warmBiasSite (warmBiasExpectSite stage)]? = some ⟨none,.warp {
      kind := .elect, ty := none,
      dsts := [some (2040+13*stage.val),some (186+6*stage.val)],
      srcs := [], mask := some (.imm (-1)) }⟩ := by
  fin_cases stage
  · exact Flow.code_1149
  · exact Flow.code_1178

set_option maxRecDepth 4096 in
private theorem expectFrameFresh (p : Params) (l : Launch) (g batch round : Nat)
    (stage : Fin 2) (lane : Nat) :
    ∀ pair ∈ warmRoundBiasStageFrame p l g batch round stage lane,
      pair.1 ≠ 2040+13*stage.val ∧ pair.1 ≠ 186+6*stage.val ∧ pair.1 ≠ 187+6*stage.val := by
  intro pair hm
  have h : ((warmRoundBiasStageFrame p l g batch round stage lane).map Prod.fst).all
      (fun r => decide (r ≠ 2040 ∧ r ≠ 2053 ∧ (r < 186 ∨ 197 < r))) = true := by
    fin_cases stage <;> (set_option maxRecDepth 100000 in rfl)
  have := of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))
  have := stage.isLt
  refine ⟨?_,by omega,by omega⟩
  fin_cases stage <;> simp <;> omega

private theorem warmExpectChoice {l : Launch} {t : Nat} {F : List (Nat × Value)}
    (stage : Fin 2) (take : Bool) (hFresh : ∀ pair ∈ F, pair.1 ≠ 187+6*stage.val)
    {s : TState} (hs : At s (warmBiasSite (warmBiasExpectSite stage)+1)
      ((186+6*stage.val,.pred take)::F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l t) s u ∧
      At u (if take then warmBiasSite (warmBiasExpectSite stage)+3
        else warmBiasSite (warmBiasExpectSite stage)+5) F := by
  fin_cases stage
  · exact inputBoxChoice take (pc := 1149) (endPc := 1154)
      (by decide) (by decide) Flow.code_1150 Flow.code_1151 hFresh hs
  · exact inputBoxChoice take (pc := 1178) (endPc := 1183)
      (by decide) (by decide) Flow.code_1179 Flow.code_1180 hFresh hs

set_option maxRecDepth 4096 in
private theorem warmExpectLeader {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch round : Nat} (stage : Fin 2) (lane : Nat) {s : TState}
    (hs : At s (warmBiasSite (warmBiasExpectSite stage)+1)
      ((186+6*stage.val,.pred true)::warmRoundBiasStageFrame p l g batch round stage lane)) :
    ∃ a u, a.pc = warmBiasSite (warmBiasExpectSite stage)+4 ∧
      At u (warmBiasSite (warmBiasExpectSite stage)+4+1)
        (warmRoundBiasStageFrame p l g batch round stage lane) ∧
      Next kernel Assumptions.all l (warpLane l g lane) s a
        (.arrive (biasReadyObject l ((warpLane l g lane)/l.block) stage) 32768 u 1 true .cta) := by
  let F := warmRoundBiasStageFrame p l g batch round stage lane
  obtain ⟨u,hu,hU⟩ := warmExpectChoice (l := l) (t := warpLane l g lane) stage true
    (fun pair hm => (expectFrameFresh p l g batch round stage lane pair hm).2.2) hs
  fin_cases stage
  · have hSeg : Seg kernel [] l (warpLane l g lane) 1 1152 [] 1153 [(2041,b32 32768)] := by
      intro t ht
      seg_fp ht using decide
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSeg
      (show At u 1152 ([]++F) from hU)
    have hRoot : v.regs 1140 = some (b32 (l.sharedBase+320)) :=
      holds_mem hV.2.2.2.2 (by simp [F,warmRoundBiasStageFrame,warmRoundBiasFrame])
    let w := next (mbarStateDest v (some 7698))
    have hV' : At v 1153 [(2041,b32 32768),(1140,b32 (l.sharedBase+320))] :=
      hV.mono ⟨hV.2.2.2.2.1,hRoot,trivial⟩
    have hw : At w 1154 F := by
      refine ⟨by simp [w,next,mbarStateDest,hV.1],hV.2.1,hV.2.2.1,hV.2.2.2.1,?_⟩
      exact hV.2.2.2.2.2
    exact ⟨v,w,hV.1,hw,hu.trans (run_rtg hv),warmBiasExpectationOut hp hV'⟩
  · have hSeg : Seg kernel [] l (warpLane l g lane) 1 1181 [] 1182 [(2054,b32 32768)] := by
      intro t ht
      seg_fp ht using decide
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSeg
      (show At u 1181 ([]++F) from hU)
    have hRoot : v.regs 2535 = some (b32 l.sharedBase) :=
      holds_mem hV.2.2.2.2 (by
        simp [F,warmRoundBiasStageFrame,warmRoundBiasFrame,warmRoundValueCarry,
          warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,openingWarmFrame,warmStartFrame])
    let w := next (mbarStateDest v (some 7703))
    have hV' : At v 1182 [(2054,b32 32768),(2535,b32 l.sharedBase)] :=
      hV.mono ⟨hV.2.2.2.2.1,hRoot,trivial⟩
    have hw : At w 1183 F := by
      refine ⟨by simp [w,next,mbarStateDest,hV.1],hV.2.1,hV.2.2.1,hV.2.2.2.1,?_⟩
      exact hV.2.2.2.2.2
    exact ⟨v,w,hV.1,hw,hu.trans (run_rtg hv),warmStageOneExpectationOut hp hV'⟩

set_option maxRecDepth 4096 in
/-- The transaction expectation of a warm Bias stage: the warp elects its issuer, the
issuer arrives on the stage's Bias-ready object, and every lane continues. -/
theorem warmRoundBiasExpectOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (stage : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasSite (warmBiasExpectSite stage))
      (warmRoundBiasStageFrame p l g batch round stage) shuffles votes ends)
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round)
    (hLower : ∀ lane < 32, round ≤
      warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) (warmBiasExpectSite stage)) :
    ∃ next : SchedulerWarpReached l X g (warmBiasSite (warmBiasExpectSite stage)+4+1)
        (warmRoundBiasStageFrame p l g batch round stage) shuffles votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        QuietSpan X (warpLane l g lane) (cur.pos lane) (next.pos lane) ∧
        round+1 ≤ warmBiasSiteCount X (warpLane l g lane) (next.pos lane)
          (warmBiasExpectSite stage)) ∧
      ∃ issue, issue.1/l.block = g/l.block ∧
        X.get issue = some ⟨warmBiasSite (warmBiasExpectSite stage)+4,
          .arrive (biasReadyObject l (g/l.block) stage) 32768 1 true .cta⟩ ∧
        ((X.tr issue.1).take issue.2).countP Execution.isShfl = shuffles := by
  obtain ⟨leader,done,hDone⟩ := consumeWarmBiasElection hp hMax hFrame hg (by omega) hb hLo
    hHi (warmBiasExpectSite stage) cur hRank hLower (warmExpectCode stage)
    (fun lane _ pair hm => ⟨(expectFrameFresh p l g batch round stage lane pair hm).1,
      (expectFrameFresh p l g batch round stage lane pair hm).2.1⟩)
  have hLeaderAt := done.checkpoint leader leader.isLt
  simp only [beq_self_eq_true] at hLeaderAt
  obtain ⟨next,hPos,hGet⟩ := expectationAtElectedWarp hp hMax hg
    (fun cta => biasReadyObject l cta stage)
    (site := warmBiasSite (warmBiasExpectSite stage)+4) done leader
    (warmExpectLeader hp stage leader hLeaderAt)
    (fun lane hl hLeader => by
      have h := done.checkpoint lane hl
      simp only [beq_eq_false_iff_ne.mpr hLeader] at h
      exact warmExpectChoice (l := l) (t := warpLane l g lane) stage false
        (fun pair hm => (expectFrameFresh p l g batch round stage lane pair hm).2.2) h)
  refine ⟨next,fun lane hl => ?_,⟨warpLane l g leader,done.pos leader⟩,?_,hGet,?_⟩
  · obtain ⟨hStep,hCount,inst,he⟩ := hDone lane hl
    have hNext := hPos lane hl
    have hMono := countP_take_mono (ElectOrd.atSites (fun pc => pc == warmBiasSite
      (warmBiasExpectSite stage))) (X.tr (warpLane l g lane))
      (show done.pos lane ≤ next.pos lane by split at hNext <;> omega)
    refine ⟨by split at hNext <;> omega,?_,?_⟩
    · have hElect := QuietSpan.single (X := X) he (fun _ _ h => by cases h)
        (fun _ _ _ h => by cases h)
      by_cases hLeader : lane = leader.val
      · subst lane
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hNext
        have hIssue := QuietSpan.single (X := X) hGet (fun _ _ h => by cases h)
          (fun _ _ _ h => by cases h)
        rw [hNext,hStep]
        rw [hStep] at hIssue
        exact hElect.trans hIssue
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hLeader)] at hNext
        rw [hNext,hStep]
        exact hElect
    · unfold warmBiasSiteCount ElectOrd.siteOrdinal at hCount ⊢
      omega
  · exact (Step.sameWarp_lane (by rw [hp.block]) hg leader.isLt).1.1.2.2.symm
  · exact done.ordinals.shfl leader leader.isLt

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
