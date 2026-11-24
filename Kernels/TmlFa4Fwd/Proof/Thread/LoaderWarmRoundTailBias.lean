-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailBranch
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundTailFloor
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasBoxes
public import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasEntry
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
import Lemmas.Flow.LoadShared
import Lemmas.Flow.ReturningPrefix
import Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasEntry
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.MBarrier Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The readiness of warp 14's tail Bias-empty wait. At the wait, a lane whose remaining trace
consists of failed polls finds the stage-zero object in the phase that lets the poll pass. -/
def WarmTailBiasReady (p : Params) (l : Launch) (X : Execution) (g batch : Nat) : Prop :=
  ∀ {F : Nat → List (Nat × Value)} {shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1361 F shuffles votes ends),
    shuffles = primingSearchShuffleCount batch+64+64*warmRounds p l g batch →
    (∀ lane < 32, Holds (cur.state lane).regs [(2535,b32 l.sharedBase),(1062,b32 14)]) →
    ∀ lane < 32,
      (∀ e ∈ (X.tr (warpLane l g lane)).drop (cur.pos lane),
        ∃ loc, e.kind = .wait loc (warmRounds p l g batch%2) false true .cta) →
      let log := X.objects (biasEmptyObject l (g/l.block) 0)
      ∃ s, stateBefore log log.length = some s ∧ s.phase%2 ≠ warmRounds p l g batch%2

/-- The tail Bias packet: its transaction expectation and both stage-zero halves. -/
structure TailBiasIssued (p : Params) (l : Launch) (X : Execution) (g batch : Nat) : Prop where
  expectation : ∃ e, X.get e =
    some ⟨1368,.arrive (biasReadyObject l (g/l.block) 0) 32768 1 true .cta⟩
  boxes : ∀ half : Fin 2, ∃ issue, issue.1/l.block = g/l.block ∧
    X.get issue = some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue p.biasMapAddress
      (inputSiteSpec p l issue.1 (inputSite (tailBiasInputSite half)) (64*half.val)
        (warmBiasRow p l g batch) (warmBiasHead p l g batch) (l.sharedBase+320))⟩

def tailBiasFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  [(1142,b32 (l.sharedBase+320)),(2121,b32 (l.sharedBase+336)),(7289,warmBiasMap)] ++
    warmTailFrame p l g batch lane

def tailBoxFrame (p : Params) (l : Launch) (g batch lane : Nat) : List (Nat × Value) :=
  (1143,b32 1152) :: tailBiasFrame p l g batch lane

variable {p : Params}

private theorem tailExpectationOut {l : Launch} {m : Mem0} (hp : Pre p l m) {t : Nat} {s : TState}
    (hs : At s 1368 [(2123,b32 32768),(1142,b32 (l.sharedBase+320))]) :
    out kernel Assumptions.all l t s = .ev (.arrive (biasReadyObject l (t/l.block) 0)
      32768 (next (mbarStateDest s (some 7753))) 1 true .cta) := by
  rw [loaderOutCore (by rw [hs.1]; decide) (by rw [hs.1]; decide)]
  rw [out_event hs.2.2.2.1 (by rw [hs.1]; exact Flow.code_1368) rfl rfl]
  have hBase : l.sharedBase+320 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+320)%8 = 0 := by have := hp.shared.1; omega
  have hEff : effAddr l t s .shared 1142 0 = .ok (biasReadyObject l (t/l.block) 0) := by
    simpa [biasReadyObject] using effAddr_b32_off (off := 0) hs.2.2.2.2.2.1 hBase
  have hLoc : mbarLoc l t s 1142 0 = .ok (biasReadyObject l (t/l.block) 0) := by
    simp [mbarLoc,hEff,biasReadyObject,hAlign,bind,Except.bind,pure,Except.pure]
  have hOne : readBits l t s 32 (.imm 1) = .ok 1#64 := rfl
  simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hs.2.2.2.2.1 (by decide),
    hOne,bind,Except.bind,pure,Except.pure,ofExec]

set_option maxRecDepth 4096 in
private theorem tailKeys (p : Params) (l : Launch) (g batch lane : Nat) :
    ∀ pair ∈ tailBoxFrame p l g batch lane,
      pair.1 ≠ 9616 ∧ pair.1 ≠ 2122 ∧ pair.1 ≠ 2124 ∧ pair.1 ≠ 2126 ∧
        (pair.1 < 203 ∨ 208 < pair.1) := by
  intro pair hm
  have h : ((tailBoxFrame p l g batch lane).map Prod.fst).all
      (fun r => decide (r ≠ 9616 ∧ r ≠ 2122 ∧ r ≠ 2124 ∧ r ≠ 2126 ∧ (r < 203 ∨ 208 < r))) =
        true := by
    set_option maxRecDepth 100000 in rfl
  exact of_decide_eq_true (List.all_eq_true.mp h _ (List.mem_map_of_mem hm))

private theorem tailBiasKeys (p : Params) (l : Launch) (g batch lane : Nat) :
    ∀ pair ∈ tailBiasFrame p l g batch lane,
      pair.1 ≠ 9616 ∧ pair.1 ≠ 2122 ∧ pair.1 ≠ 2124 ∧ pair.1 ≠ 2126 ∧
        (pair.1 < 203 ∨ 208 < pair.1) :=
  fun pair hm => tailKeys p l g batch lane pair (List.mem_cons_of_mem _ hm)

/-- A first full-warp election of the tail. -/
private theorem tailElection {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g site dst pred shuffles votes : Nat}
    (hg : g < l.threads) (hSite : TailFloor (site+1)) (hlo : 174 ≤ site) (hhi : site < 1906)
    (hCode : kernel.code[site]? = some ⟨none,.warp {
      kind := .elect, ty := none, dsts := [some dst,some pred],
      srcs := [], mask := some (.imm (-1)) }⟩) {F : Nat → List (Nat × Value)}
    {ends : Nat → Option TState}
    (hFresh : ∀ lane < 32, ∀ pair ∈ F lane, pair.1 ≠ dst ∧ pair.1 ≠ pred)
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    ∃ leader : Fin 32, Nonempty (SchedulerWarpReached l X g (site+1)
      (fun lane => (pred,.pred (lane == leader.val)) :: F lane) shuffles votes ends) := by
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hFirst (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < cur.pos lane)
      (mask inst leader : Nat) : ¬ X.Elect (warpLane l g lane,j) site mask inst leader := by
    intro he
    have hTrace := (cur.recorded lane hl).returning_reach.append
      (TraceReach.of_local (cur.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (cur.pos lane))[j]? =
        some ⟨site,.elect mask inst leader⟩ := by rwa [List.getElem?_take_of_lt hj]
    exact inputElectionFresh (fun hPc hF => inputElectOut hPc hF hlo hhi hCode)
      (fun h hu => tailFloorReach hSite h hu) hTrace (cur.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,done,_⟩ := cur.consumeElection hp hMax hg
    (fun lane ld => inputElectReturn l (warpLane l g lane) (cur.state lane) dst pred ld)
    (fun lane ld => (pred,.pred (lane == ld)) :: F lane) hFirst
    (fun lane hl => inputElectOut (cur.checkpoint lane hl).1 (cur.checkpoint lane hl).2.2.2.1
      hlo hhi hCode)
    (fun lane hl ld => by
      have hs := cur.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      refine ⟨by simp [inputElectReturn,next,setReg,hs.1],hs.2.1,hs.2.2.1,hs.2.2.2.1,?_,?_⟩
      · simp [inputElectReturn,next,setReg,hLane]
      · exact holds_update (holds_update hs.2.2.2.2 (fun q hq => (hFresh lane hl q hq).1))
          (fun q hq => (hFresh lane hl q hq).2))
  exact ⟨leader,⟨done⟩⟩

set_option maxRecDepth 4096 in
private theorem tailBoxSeg {l : Launch} {t row head : Nat} (half : Fin 2) :
    Seg kernel [] l t 3 (1373+7*half.val)
      [(1143,b32 1152),(7289,warmBiasMap),(2535,b32 l.sharedBase),(1087,b32 row),
        (7169,b32 head),(1142,b32 (l.sharedBase+320))]
      (inputSite (tailBiasInputSite half)).pc
      (inputSiteFacts l (inputSite (tailBiasInputSite half)) (64*half.val) row head
        (l.sharedBase+320) 0) := by
  fin_cases half <;> intro w hw <;>
    dsimp [tailBiasInputSite,inputSite,inputSiteFacts,inputParam,warmBiasMap] at hw ⊢
  all_goals seg_fp hw using rfl

private theorem tailBoxChoice {l : Launch} {t : Nat} {F : List (Nat × Value)}
    (half : Fin 2) (take : Bool) (hFresh : ∀ pair ∈ F, pair.1 ≠ 206+2*half.val)
    {s : TState} (hs : At s (1370+7*half.val+1) ((205+2*half.val,.pred take)::F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l t) s u ∧
      At u (if take then 1373+7*half.val else 1377+7*half.val) F := by
  fin_cases half
  · exact inputBoxChoice take (pc := 1370) (endPc := 1377)
      (by decide) (by decide) Flow.code_1371 Flow.code_1372 hFresh hs
  · exact inputBoxChoice take (pc := 1377) (endPc := 1384)
      (by decide) (by decide) Flow.code_1378 Flow.code_1379 hFresh hs

private theorem tailBoxCode (half : Fin 2) :
    kernel.code[1370+7*half.val]? = some ⟨none,.warp {
      kind := .elect, ty := none, dsts := [some (2124+2*half.val),some (205+2*half.val)],
      srcs := [], mask := some (.imm (-1)) }⟩ := by
  fin_cases half
  · exact Flow.code_1370
  · exact Flow.code_1377

set_option maxRecDepth 4096 in
/-- One half of the tail Bias packet: the warp elects its issuer, which records the box. -/
private theorem tailBoxOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (half : Fin 2) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g (1370+7*half.val) (tailBoxFrame p l g batch) shuffles
      votes ends) :
    Nonempty (SchedulerWarpReached l X g (1377+7*half.val) (tailBoxFrame p l g batch) shuffles
        votes ends) ∧
      ∃ issue, issue.1/l.block = g/l.block ∧
        X.get issue = some ⟨(inputSite (tailBiasInputSite half)).pc,.tensorIssue
          p.biasMapAddress (inputSiteSpec p l issue.1 (inputSite (tailBiasInputSite half))
            (64*half.val) (warmBiasRow p l g batch) (warmBiasHead p l g batch)
            (l.sharedBase+320))⟩ := by
  let F := tailBoxFrame p l g batch
  let row := warmBiasRow p l g batch
  let head := warmBiasHead p l g batch
  have hBounds := assignedCoordinates_valid hp hLo hHi
  have hRow : row < 2^31 := by
    have h := hp.packedRow_lt hb hBounds.1
    have := hp.shape.2.2.2.2.2
    dsimp [row,warmBiasRow]
    omega
  have hHead : head < 2^31 := hBounds.2.trans hp.heads_signed
  have hFresh (lane : Nat) (pair : Nat × Value) (hm : pair ∈ F lane) :=
    tailKeys p l g batch lane pair hm
  obtain ⟨leader,⟨done⟩⟩ := tailElection hp hMax hg (site := 1370+7*half.val)
    (by unfold TailFloor; fin_cases half <;> decide) (by fin_cases half <;> decide)
    (by fin_cases half <;> decide) (tailBoxCode half)
    (fun lane _ pair hm => by
      have h := hFresh lane pair hm
      have := half.isLt
      constructor <;> fin_cases half <;> simp <;> omega) cur
  have hLeaderAt := done.checkpoint leader leader.isLt
  simp only [beq_self_eq_true] at hLeaderAt
  obtain ⟨v,hv,hV⟩ := tailBoxChoice (l := l) (t := warpLane l g leader) half true
    (fun pair hm => by
      have h := hFresh leader pair hm
      have := half.isLt
      fin_cases half <;> simp <;> omega) hLeaderAt
  have hR (r : Nat) (x : Value) (hm : (r,x) ∈ F leader) : v.regs r = some x :=
    holds_mem hV.2.2.2.2 hm
  have hIn : At v (1373+7*half.val)
      ([(1143,b32 1152),(7289,warmBiasMap),(2535,b32 l.sharedBase),(1087,b32 row),
        (7169,b32 head),(1142,b32 (l.sharedBase+320))] ++ F leader) := by
    refine hV.mono ((holds_append ..).mpr ⟨⟨hR _ _ ?_,hR _ _ ?_,hR _ _ ?_,hR _ _ ?_,hR _ _ ?_,
      hR _ _ ?_,trivial⟩,hV.2.2.2.2⟩) <;>
      simp [F,tailBoxFrame,tailBiasFrame,warmTailFrame,warmRoundCarry,openingWarmFrame,
        warmStartFrame,warmBiasRoots,row,head,warmBiasRow,warmBiasHead]
  obtain ⟨w,hw',hW⟩ := roundStraightFrame (by fin_cases half <;> decide)
    (by fin_cases half <;> decide)
    (by fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (by fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl))
    (tailBoxSeg (l := l) (t := warpLane l g leader) (row := row) (head := head) half) hIn
  have hCol : 64*half.val < 2^31 := by have := half.isLt; omega
  have hBar : l.sharedBase+320+(inputSite (tailBiasInputSite half)).barrierOffset < 2^32 := by
    have := hp.shared.2.1
    fin_cases half <;> simp [tailBiasInputSite,inputSite] <;> omega
  have hAlign : (l.sharedBase+320)%8 = 0 := by have := hp.shared.1; omega
  have hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite (tailBiasInputSite half)))
      (inputCoordinate (64*half.val) row head) := by
    fin_cases half <;>
      simp [TensorDescriptor.BoxAligned,inputMap,inputSite,tailBiasInputSite,
        Params.biasMap,inputCoordinate,TensorDescriptor.Format.bytes]
  have hEnd : (inputSite (tailBiasInputSite half)).pc+1 = 1377+7*half.val := by
    fin_cases half <;> rfl
  obtain ⟨next,_,hGet⟩ := inputBoxIssueAtElection hp hMax hg (tailBiasInputSite half) hCol hRow
    hHead hBar hAlign (by decide : 0 < 2^64) hBox hEnd (F := F) leader done
    ⟨w,hv.trans (run_rtg hw'),hW⟩
    (fun lane hl hLeader => by
      have h := done.checkpoint lane hl
      simp only [beq_eq_false_iff_ne.mpr hLeader] at h
      exact tailBoxChoice (l := l) (t := warpLane l g lane) half false (fun pair hm => by
        have h := hFresh lane pair hm
        have := half.isLt
        fin_cases half <;> simp <;> omega) h)
  have hMap : inputMapAddress p (inputSite (tailBiasInputSite half)) = p.biasMapAddress := by
    fin_cases half <;> rfl
  refine ⟨⟨next⟩,⟨warpLane l g leader,done.pos leader⟩,
    (Step.sameWarp_lane (by rw [hp.block]) hg leader.isLt).1.1.2.2.symm,?_⟩
  rw [← hMap]
  exact hGet

set_option maxRecDepth 4096 in
/-- Warp 14 runs the tail Bias block when the tile has more than ten trips and an odd
residual Bias half: it passes the stage-zero Bias-empty wait, records the expectation and
both halves of the tail packet, and reaches the steady counter gate. -/
theorem WarmRoundsDone.tailBiasOfMaximal {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (hSkip : warmTailSkips p l g batch = false)
    (hReady : WarmTailBiasReady p l X g batch) (d : WarmRoundsDone p l X g batch) :
    Nonempty (WarmTailDone p l X g batch) ∧ TailBiasIssued p l X g batch := by
  have hRole : 14 ≤ warpIndex l g := by omega
  have hLong : 10 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
    unfold warmTailSkips at hSkip
    simp only [hw,ne_eq,not_true_eq_false,decide_false,Bool.false_or,Bool.not_eq_eq_eq_not,
      Bool.not_false,Bool.and_eq_true,decide_eq_true_eq] at hSkip
    exact hSkip.1
  have hW9 : warmRounds p l g batch = 9 := by unfold warmRounds; omega
  have hFive : 5 ≤ d.shuffles := by rw [d.rank]; omega
  obtain ⟨entry,hEntry⟩ := d.tailBiasEntry hp hRole hb hLo hHi hSkip
  obtain ⟨pre,_⟩ := entry.advanceLocalWithPosition (pc' := 1361)
    (G := fun lane => [(1142,b32 (l.sharedBase+320)),(2121,b32 (l.sharedBase+336))] ++
      warmTailFrame p l g batch lane) (by
    intro lane hl
    have hs := entry.checkpoint lane hl
    have hRoot : (entry.state lane).regs 2535 = some (b32 l.sharedBase) :=
      holds_mem hs.2.2.2.2 (by simp [warmTailFrame,drainCarry])
    have hSeg : Seg kernel [] l (warpLane l g lane) 2 1359 [(2535,b32 l.sharedBase)] 1361
        [(1142,b32 (l.sharedBase+320)),(2121,b32 (l.sharedBase+336))] := by
      have hMem := hp.shared.2.1
      have hBase : l.sharedBase < 2^32 := by omega
      have hReady : l.sharedBase+320 < 2^32 := by omega
      have hEmpty : l.sharedBase+336 < 2^32 := by omega
      intro s h
      seg_fp h using norm_bits [Nat.mod_eq_of_lt hBase,Nat.mod_eq_of_lt hReady,
        Nat.mod_eq_of_lt hEmpty]
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (F := warmTailFrame p l g batch lane) (by decide)
      (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSeg (hs.mono ⟨hRoot,hs.2.2.2.2⟩)
    exact ⟨v,run_rtg hv,hV⟩)
  obtain ⟨gate,_⟩ := pre.advanceLocalWithPosition (pc' := 1361) (G := tailBiasFrame p l g batch)
    (fun lane hl => by
      have hs := (pre.checkpoint lane hl).2.2.2.2
      exact ⟨pre.state lane,.refl,(pre.checkpoint lane hl).mono
        ⟨hs.1,hs.2.1,warmBiasMapAt hp hMax.1 hg hRole (by decide) hFive pre lane hl,hs.2.2⟩⟩)
  -- The stage-zero Bias-empty wait.
  let site : DrainWaitSite := ⟨1361,9616,2121,7177⟩
  have hAddr : l.sharedBase+336 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+336)%8 = 0 := by have := hp.shared.1; omega
  have hRegs (lane : Nat) (hl : lane < 32) :
      Holds (gate.state lane).regs [(2535,b32 l.sharedBase),(1062,b32 14)] := by
    have hs := (gate.checkpoint lane hl).2.2.2.2
    refine ⟨holds_mem hs ?_,holds_mem hs ?_,trivial⟩
    · simp [tailBiasFrame,warmTailFrame,drainCarry]
    · simp [tailBiasFrame,warmTailFrame,warmRoundCarry,openingWarmFrame,warmStartFrame,hw]
  obtain ⟨waited,_⟩ := loaderWarpWaitOfBlockedPhaseTrace hMax hg (by rw [hp.block]) (site := site)
    ⟨Flow.code_1361,Flow.code_1362,Flow.code_1363⟩ (by decide) hAddr hAlign
    (Nat.mod_lt (warmRounds p l g batch) (by decide)) gate
    (fun lane _ pair hm => (tailBiasKeys p l g batch lane pair hm).1)
    (fun lane _ => by simp [site,tailBiasFrame])
    (fun lane _ => by
      have hWord := warmBiasPhaseWord (warmRounds p l g batch)
      simp [site,tailBiasFrame,warmTailFrame,warmRoundCarry,hw,← hWord])
    (fun lane hl {_ _} _ _ _ hFailed => by
      obtain ⟨s,hState,hPh⟩ := hReady gate d.rank hRegs lane hl (by
        intro e hE
        exact ⟨_,congrArg Event.kind (hFailed _ hE)⟩)
      exact ⟨s,hState,by rwa [Nat.mod_mod]⟩)
  -- The transaction expectation.
  obtain ⟨leader,⟨elected⟩⟩ := tailElection hp hMax hg (site := 1364) (.inl rfl) (by decide)
    (by decide) Flow.code_1364
    (fun lane _ pair hm => ⟨(tailBiasKeys p l g batch lane pair hm).2.1,by
      have := (tailBiasKeys p l g batch lane pair hm).2.2.2.2; omega⟩) waited
  have hLeaderAt := elected.checkpoint leader leader.isLt
  simp only [beq_self_eq_true] at hLeaderAt
  obtain ⟨⟨boxes⟩,expect,hExpect⟩ := expectationOfElectedWarp hp hMax hg
    (fun cta => biasReadyObject l cta 0) (site := 1368) (F := tailBiasFrame p l g batch)
    elected leader (by
      let F := tailBiasFrame p l g batch leader
      obtain ⟨u,hu,hU⟩ := inputBoxChoice (l := l) (g := warpLane l g leader) true
        (pc := 1364) (endPc := 1369) (by decide) (by decide) Flow.code_1365 Flow.code_1366
        (fun pair hm => by have := (tailBiasKeys p l g batch leader pair hm).2.2.2.2; omega)
        hLeaderAt
      have hSeg : Seg kernel [] l (warpLane l g leader) 1 1367 [] 1368 [(2123,b32 32768)] := by
        intro t ht
        seg_fp ht using decide
      obtain ⟨v,hv,hV⟩ := roundStraightFrame (by decide) (by decide)
        (by set_option maxRecDepth 100000 in kernel_rfl) rfl hSeg
        (show At u 1367 ([]++F) from hU)
      have hRoot : v.regs 1142 = some (b32 (l.sharedBase+320)) :=
        holds_mem hV.2.2.2.2 (by simp [F,tailBiasFrame])
      let w := next (mbarStateDest v (some 7753))
      have hV' : At v 1368 [(2123,b32 32768),(1142,b32 (l.sharedBase+320))] :=
        hV.mono ⟨hV.2.2.2.2.1,hRoot,trivial⟩
      have hw' : At w 1369 F := by
        refine ⟨by simp [w,next,mbarStateDest,hV.1],hV.2.1,hV.2.2.1,hV.2.2.2.1,?_⟩
        exact hV.2.2.2.2.2
      exact ⟨v,w,hV.1,hw',hu.trans (run_rtg hv),tailExpectationOut hp hV'⟩)
    (fun lane hl hLeader => by
      have h := elected.checkpoint lane hl
      simp only [beq_eq_false_iff_ne.mpr hLeader] at h
      exact inputBoxChoice (l := l) (g := warpLane l g lane) false (pc := 1364) (endPc := 1369)
        (by decide) (by decide) Flow.code_1365 Flow.code_1366
        (fun pair hm => by have := (tailBiasKeys p l g batch lane pair hm).2.2.2.2; omega) h)
  -- The tail column offset.
  obtain ⟨first⟩ := boxes.advanceLocal (pc' := 1370) (G := tailBoxFrame p l g batch) (by
    intro lane hl
    have hs := boxes.checkpoint lane hl
    have hCounter : (boxes.state lane).regs 7181 = some (b32 9) := by
      rw [← hW9]
      exact holds_mem hs.2.2.2.2 (by simp [tailBiasFrame,warmTailFrame])
    have hSeg : Seg kernel [] l (warpLane l g lane) 1 1369 [(7181,b32 9)] 1370
        [(1143,b32 1152)] := by
      intro t ht
      seg_fp ht using decide
    obtain ⟨v,hv,hV⟩ := roundStraightFrame (F := tailBiasFrame p l g batch lane) (by decide)
      (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl) hSeg (hs.mono ⟨hCounter,hs.2.2.2.2⟩)
    exact ⟨v,run_rtg hv,hV⟩)
  obtain ⟨⟨second⟩,b0,hB0Cta,hB0⟩ := tailBoxOfMaximal hp hMax hg hb hLo hHi 0 first
  obtain ⟨⟨last⟩,b1,hB1Cta,hB1⟩ := tailBoxOfMaximal hp hMax hg hb hLo hHi 1 second
  obtain ⟨done⟩ := last.advanceLocal (pc' := 1384) (G := warmTailFrame p l g batch)
    (fun lane hl => ⟨last.state lane,.refl,(last.checkpoint lane hl).mono
      (last.checkpoint lane hl).2.2.2.2.2.2.2.2⟩)
  refine ⟨⟨⟨d.shuffles,d.votes,d.ends,done,d.rank⟩⟩,⟨expect,hExpect⟩,fun half => ?_⟩
  fin_cases half
  · exact ⟨b0,hB0Cta,hB0⟩
  · exact ⟨b1,hB1Cta,hB1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
