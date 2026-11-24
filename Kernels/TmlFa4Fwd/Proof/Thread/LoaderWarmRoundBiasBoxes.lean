-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasGate
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundBiasElect
public import Kernels.TmlFa4Fwd.Proof.LoaderRepeatedBiasCoordinates
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmBiasExpectationProgress
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The election that selects the issuer of one warm Bias half. -/
def warmBiasBoxSite (stage half : Fin 2) : Fin 6 :=
  ⟨3*stage.val+1+half.val,by have := stage.isLt; have := half.isLt; omega⟩

/-- The instruction after the guarded issue of one warm Bias half. -/
def warmBiasBoxEnd (stage half : Fin 2) : Nat :=
  if stage = 0 then (if half = 0 then 1164 else 1174)
  else (if half = 0 then 1192 else 1201)

/-- The frame that both Bias stages of a warm round carry while they issue boxes. -/
def warmRoundBiasStageFrame (p : Params) (l : Launch) (g batch round : Nat) :
    Fin 2 → Nat → List (Nat × Value)
  | 0 => fun lane => (7289,warmBiasMap) :: warmRoundBiasFrame p l g batch round lane
  | 1 => fun lane => (2052,b32 (l.sharedBase+344)) :: (7289,warmBiasMap) ::
      warmRoundBiasFrame p l g batch round lane

/-- The Bias tensor row of a stage. -/
def warmBiasStageRow (row : Nat) (stage : Fin 2) : Nat := row+128*stage.val

/-- The Bias-ready barrier operand of a stage's tensor issues. -/
def warmBiasStageBarrier (l : Launch) (stage : Fin 2) : Nat :=
  if stage = 0 then l.sharedBase+320 else l.sharedBase

/-- The launch coordinates that the warm Bias boxes use. -/
def warmBiasRow (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  p.qOffset batch+256*(assignedCoordinates p batch (g/l.block)).1

def warmBiasHead (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  (assignedCoordinates p batch (g/l.block)).2

def warmBiasBit (p : Params) (l : Launch) (g batch : Nat) : Nat :=
  vPrimingResidual p batch (assignedCoordinates p batch (g/l.block)).1/2^31

theorem warmBiasPhaseWord (round : Nat) :
    loaderPhaseWord (warmBiasPhase 14 round) = b32 (round%2) := by
  have h := Nat.mod_two_eq_zero_or_one round
  rcases h with h | h <;> simp [loaderPhaseWord,warmBiasPhase,h]

set_option maxRecDepth 4096 in
private theorem stageFrameMem {p : Params} {l : Launch} {g batch round lane : Nat}
    (stage : Fin 2) {r : Nat} {v : Value}
    (h : (r,v) ∈ (7289,warmBiasMap) :: warmRoundBiasFrame p l g batch round lane) :
    (r,v) ∈ warmRoundBiasStageFrame p l g batch round stage lane := by
  fin_cases stage
  · exact h
  · exact List.mem_cons_of_mem _ h

set_option maxRecDepth 4096 in
private theorem stageRoots {p : Params} {l : Launch} {g batch round lane : Nat}
    (stage : Fin 2) {s : TState}
    (hs : Holds s.regs (warmRoundBiasStageFrame p l g batch round stage lane)) :
    Holds s.regs [(1090,b32 0),(7174,b32 round),
      (1117,b32 (warmBiasBit p l g batch)),(7289,warmBiasMap),(2535,b32 l.sharedBase),
      (1087,b32 (warmBiasRow p l g batch)),(7169,b32 (warmBiasHead p l g batch)),
      (1140,b32 (l.sharedBase+320))] := by
  have m (r : Nat) (v : Value)
      (h : (r,v) ∈ (7289,warmBiasMap) :: warmRoundBiasFrame p l g batch round lane) :
      s.regs r = some v := holds_mem hs (stageFrameMem stage h)
  refine ⟨m _ _ ?_,m _ _ ?_,m _ _ ?_,m _ _ ?_,m _ _ ?_,m _ _ ?_,m _ _ ?_,m _ _ ?_,trivial⟩ <;>
    simp [warmRoundBiasFrame,warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,
      warmRoundFrame,openingWarmFrame,warmStartFrame,warmBiasRoots,warmBiasBit,warmBiasRow,
      warmBiasHead]

set_option maxRecDepth 4096 in
private theorem warmBiasBoxTail {l : Launch} {t round bit row head : Nat}
    (stage half : Fin 2) (hRow : row+128 < 2^31) :
    let site := inputSite (warmBiasInputSite stage half)
    let col := warmBiasColumn stage half round bit
    Seg kernel [] l t (site.pc-(warmColumnStart stage half+warmColumnLength stage))
      (warmColumnStart stage half+warmColumnLength stage)
      [(site.colReg,b32 col),(7289,warmBiasMap),(2535,b32 l.sharedBase),(1087,b32 row),
        (7169,b32 head),(1140,b32 (l.sharedBase+320))]
      site.pc
      (inputSiteFacts l site col (warmBiasStageRow row stage) head
        (warmBiasStageBarrier l stage) 0) := by
  have hFit : row+128 < 2^32 := by omega
  dsimp only
  fin_cases stage <;> fin_cases half <;> intro w hw <;>
    dsimp [warmColumnStart,warmColumnLength,warmBiasInputSite,inputSite,inputSiteFacts,
      warmBiasStageRow,warmBiasStageBarrier,inputParam,warmBiasMap] at hw ⊢
  all_goals seg_fp hw using (first | rfl | norm_bits [Nat.mod_eq_of_lt hFit])

/-- The destination and predicate registers of the election of one warm Bias half. -/
def warmBiasBoxDst (stage half : Fin 2) : Nat :=
  if stage = 0 then (if half = 0 then 2042 else 2047) else (if half = 0 then 2055 else 2059)

def warmBiasBoxPred (stage half : Fin 2) : Nat := 188+2*half.val+6*stage.val

private theorem warmBiasBoxChoice {l : Launch} {t : Nat} {F : List (Nat × Value)}
    (stage half : Fin 2) (take : Bool)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ warmBiasBoxPred stage half+1) {s : TState}
    (hs : At s (warmBiasSite (warmBiasBoxSite stage half)+1)
      ((warmBiasBoxPred stage half,.pred take)::F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l t) s u ∧
      At u (if take then warmColumnStart stage half else warmBiasBoxEnd stage half) F := by
  fin_cases stage <;> fin_cases half
  · exact inputBoxChoice take (pc := 1154) (endPc := 1164)
      (by decide) (by decide) Flow.code_1155 Flow.code_1156 hFresh hs
  · exact inputBoxChoice take (pc := 1164) (endPc := 1174)
      (by decide) (by decide) Flow.code_1165 Flow.code_1166 hFresh hs
  · exact inputBoxChoice take (pc := 1183) (endPc := 1192)
      (by decide) (by decide) Flow.code_1184 Flow.code_1185 hFresh hs
  · exact inputBoxChoice take (pc := 1192) (endPc := 1201)
      (by decide) (by decide) Flow.code_1193 Flow.code_1194 hFresh hs

private theorem warmBiasBoxCode (stage half : Fin 2) :
    kernel.code[warmBiasSite (warmBiasBoxSite stage half)]? = some ⟨none,.warp {
      kind := .elect, ty := none,
      dsts := [some (warmBiasBoxDst stage half),some (warmBiasBoxPred stage half)],
      srcs := [], mask := some (.imm (-1)) }⟩ := by
  fin_cases stage <;> fin_cases half
  · exact Flow.code_1154
  · exact Flow.code_1164
  · exact Flow.code_1183
  · exact Flow.code_1192

set_option maxRecDepth 4096 in
private theorem stageFrameKeys (p : Params) (l : Launch) (g batch round : Nat)
    (stage : Fin 2) (lane : Nat) :
    ∀ pair ∈ warmRoundBiasStageFrame p l g batch round stage lane,
      pair.1 ≠ 2042 ∧ pair.1 ≠ 2047 ∧ pair.1 ≠ 2055 ∧ pair.1 ≠ 2059 ∧
        (pair.1 < 188 ∨ 197 < pair.1) := by
  intro pair hm
  have h : ((warmRoundBiasStageFrame p l g batch round stage lane).map Prod.fst).all
      (fun r => decide (r ≠ 2042 ∧ r ≠ 2047 ∧ r ≠ 2055 ∧ r ≠ 2059 ∧
        (r < 188 ∨ 197 < r))) = true := by
    fin_cases stage <;> (set_option maxRecDepth 100000 in rfl)
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))

private theorem stageFrameFresh (p : Params) (l : Launch) (g batch round : Nat)
    (stage half : Fin 2) (lane : Nat) :
    ∀ pair ∈ warmRoundBiasStageFrame p l g batch round stage lane,
      pair.1 ≠ warmBiasBoxDst stage half ∧ pair.1 ≠ warmBiasBoxPred stage half ∧
        pair.1 ≠ warmBiasBoxPred stage half+1 := by
  intro pair hm
  have h := stageFrameKeys p l g batch round stage lane pair hm
  have hs := stage.isLt
  have hh := half.isLt
  unfold warmBiasBoxPred
  refine ⟨?_,by omega,by omega⟩
  fin_cases stage <;> fin_cases half <;> simp [warmBiasBoxDst] <;> omega

set_option maxRecDepth 4096 in
/-- One warm Bias half of a stage: the warp elects its issuer, the issuer records the
tensor box, and every lane continues past the guarded issue. -/
theorem warmRoundBiasBoxOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hRound : round < warmRounds p l g batch) (stage half : Fin 2)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (warmBiasSite (warmBiasBoxSite stage half))
      (warmRoundBiasStageFrame p l g batch round stage) shuffles votes ends)
    (hRank : shuffles = primingSearchShuffleCount batch+96+64*round)
    (hLower : ∀ lane < 32, round ≤
      warmBiasSiteCount X (warpLane l g lane) (cur.pos lane) (warmBiasBoxSite stage half)) :
    ∃ next : SchedulerWarpReached l X g (warmBiasBoxEnd stage half)
        (warmRoundBiasStageFrame p l g batch round stage) shuffles votes ends,
      (∀ lane < 32, cur.pos lane < next.pos lane ∧
        QuietSpan X (warpLane l g lane) (cur.pos lane) (next.pos lane) ∧
        round+1 ≤ warmBiasSiteCount X (warpLane l g lane) (next.pos lane)
          (warmBiasBoxSite stage half)) ∧
      ∃ issue, issue.1/l.block = g/l.block ∧
        X.get issue = some ⟨warmBiasIssueSite stage half,.tensorIssue p.biasMapAddress
          (inputSiteSpec p l issue.1 (inputSite (warmBiasInputSite stage half))
            (warmBiasColumn stage half round (warmBiasBit p l g batch))
            (warmBiasStageRow (warmBiasRow p l g batch) stage) (warmBiasHead p l g batch)
            (warmBiasStageBarrier l stage))⟩ ∧
        ((X.tr issue.1).take issue.2).countP Execution.isShfl = shuffles := by
  let F := warmRoundBiasStageFrame p l g batch round stage
  let co := assignedCoordinates p batch (g/l.block)
  let row := warmBiasRow p l g batch
  let head := warmBiasHead p l g batch
  let bit := warmBiasBit p l g batch
  have hBounds := assignedCoordinates_valid hp hLo hHi
  have hRow : row+128 < 2^31 := by
    have h := hp.packedRow_lt hb hBounds.1
    have := hp.shape.2.2.2.2.2
    dsimp [row,warmBiasRow]
    omega
  have hHead : head < 2^31 := hBounds.2.trans hp.heads_signed
  have hBit : bit ≤ 1 := warmBiasResidualBit_le p batch co.1
  have hIter : round < 9 := by unfold warmRounds at hRound; omega
  obtain ⟨leader,done,hDone⟩ := consumeWarmBiasElection hp hMax hFrame hg (by omega) hb hLo
    hHi (warmBiasBoxSite stage half) cur hRank hLower (warmBiasBoxCode stage half)
    (fun lane _ pair hm => ⟨(stageFrameFresh p l g batch round stage half lane pair hm).1,
      (stageFrameFresh p l g batch round stage half lane pair hm).2.1⟩)
  let site := warmBiasInputSite stage half
  let col := warmBiasColumn stage half round bit
  have hCol : col < 2^31 := by
    have hHalf := half.isLt
    have hStage := stage.isLt
    simp only [col,warmBiasColumn]
    split <;> omega
  have hRow' : warmBiasStageRow row stage < 2^31 := by
    have := stage.isLt
    unfold warmBiasStageRow
    omega
  have hBar : warmBiasStageBarrier l stage+(inputSite site).barrierOffset < 2^32 := by
    have := hp.shared.2.1
    fin_cases stage <;> fin_cases half <;>
      simp [warmBiasStageBarrier,site,warmBiasInputSite,inputSite] <;> omega
  have hAlign : warmBiasStageBarrier l stage%8 = 0 := by
    have := hp.shared.1
    fin_cases stage <;> simp [warmBiasStageBarrier] <;> omega
  have hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite site))
      (inputCoordinate col (warmBiasStageRow row stage) head) := by
    fin_cases stage <;> fin_cases half <;>
      simp [TensorDescriptor.BoxAligned,inputMap,inputSite,site,warmBiasInputSite,col,
        warmBiasColumn,Params.biasMap,inputCoordinate,TensorDescriptor.Format.bytes]
    all_goals omega
  have hEnd : (inputSite site).pc+1 = warmBiasBoxEnd stage half := by
    fin_cases stage <;> fin_cases half <;> rfl
  have hMap : inputMapAddress p (inputSite site) = p.biasMapAddress := by
    fin_cases stage <;> fin_cases half <;> rfl
  have hLeaderAt := done.checkpoint leader leader.isLt
  simp only [beq_self_eq_true] at hLeaderAt
  obtain ⟨v,hv,hV⟩ := warmBiasBoxChoice (l := l) (t := warpLane l g leader) stage half true
    (fun pair hm => (stageFrameFresh p l g batch round stage half leader pair hm).2.2)
    hLeaderAt
  have hRoots := stageRoots stage hV.2.2.2.2
  have hColIn : At v (warmColumnStart stage half)
      ([(1090,b32 0),(7174,b32 round),(1117,b32 bit)] ++ F leader) :=
    hV.mono ((holds_append ..).mpr ⟨⟨hRoots.1,hRoots.2.1,hRoots.2.2.1,trivial⟩,hV.2.2.2.2⟩)
  obtain ⟨u,hu,hU⟩ := roundStraightFrame
    (by fin_cases stage <;> fin_cases half <;> decide)
    (by fin_cases stage <;> fin_cases half <;> decide)
    (by fin_cases stage <;> fin_cases half <;>
      (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases stage <;> fin_cases half <;>
      (set_option maxRecDepth 100000 in kernel_rfl))
    (warmBiasColumnSegment (l := l) (g := warpLane l g leader) stage half hIter hBit) hColIn
  have hTailIn : At u (warmColumnStart stage half+warmColumnLength stage)
      ([((inputSite site).colReg,b32 col),(7289,warmBiasMap),(2535,b32 l.sharedBase),
        (1087,b32 row),(7169,b32 head),(1140,b32 (l.sharedBase+320))] ++ F leader) := by
    have hParts := (holds_append ..).mp hU.2.2.2.2
    have hR := stageRoots stage hParts.2
    exact hU.mono ((holds_append ..).mpr ⟨⟨hParts.1.1,hR.2.2.2.1,hR.2.2.2.2.1,
      hR.2.2.2.2.2.1,hR.2.2.2.2.2.2.1,hR.2.2.2.2.2.2.2.1,trivial⟩,hParts.2⟩)
  obtain ⟨w,hw',hW⟩ := roundStraightFrame
    (by fin_cases stage <;> fin_cases half <;> decide)
    (by fin_cases stage <;> fin_cases half <;> decide)
    (by fin_cases stage <;> fin_cases half <;>
      (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases stage <;> fin_cases half <;>
      (set_option maxRecDepth 100000 in kernel_rfl))
    (warmBiasBoxTail (l := l) (t := warpLane l g leader) (round := round) (bit := bit)
      (head := head) stage half hRow) hTailIn
  obtain ⟨next,hPos,hGet⟩ := inputBoxIssueAtElection hp hMax hg site hCol hRow' hHead hBar
    hAlign (by decide : 0 < 2^64) hBox hEnd (F := F) leader done
    ⟨w,hv.trans ((run_rtg hu).trans (run_rtg hw')),hW⟩
    (fun lane hl hLeader => by
      have h := done.checkpoint lane hl
      simp only [beq_eq_false_iff_ne.mpr hLeader] at h
      exact warmBiasBoxChoice (l := l) (t := warpLane l g lane) stage half false
        (fun pair hm => (stageFrameFresh p l g batch round stage half lane pair hm).2.2) h)
  refine ⟨next,fun lane hl => ?_,⟨warpLane l g leader,done.pos leader⟩,?_,?_,?_⟩
  · obtain ⟨hStep,hCount,inst,he⟩ := hDone lane hl
    have hNext := hPos lane hl
    have hMono := countP_take_mono (ElectOrd.atSites (fun pc => pc == warmBiasSite
      (warmBiasBoxSite stage half))) (X.tr (warpLane l g lane))
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
  · rw [← hMap,← warmBiasInputSite_pc stage half]
    exact hGet
  · exact done.ordinals.shfl leader leader.isLt

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
