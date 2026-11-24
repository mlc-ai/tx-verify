-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RowDrainFirstWords
import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.RowDrainRole
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Epilogue Mma

def scan : RowDrainRole → GroupScan
  | .softmax => .softmaxDrain
  | .correction => .correctionDrain

private def laterExit (role : RowDrainRole) : Nat := (scanSite role.scan).compare+3

private def laneIndexReg : RowDrainRole → Nat
  | .softmax => 1609
  | .correction => 1660

private def laneGuardReg : RowDrainRole → Nat
  | .softmax => 664
  | .correction => 755

private def laterAddressReg : RowDrainRole → Nat
  | .softmax => 8984
  | .correction => 9533

private def laterDst : RowDrainRole → Nat
  | .softmax => 7261
  | .correction => 7281

private theorem readAdvances {l : Launch} {X : Execution} {g pos j pc dst : Nat}
    {s t : TState} {ending : Option TState} {F : List (Nat × Value)}
    {a : Acc} {target : Event}
    (hDest : ∀ pair ∈ F, pair.1 ≠ dst) (ht : At t pc F)
    (hn : Next kernel Assumptions.all l g s t (.read a (afterLoad t [dst])))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hBefore : pos < j) (he : X.get (g,j) = some target)
    (hSafe : ∀ f, target.kind ≠ .ub f) :
    ∃ u, At u (pc+1) F ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+1)) ending := by
  obtain ⟨_,u,_,⟨bytes,_,rfl,hReturn⟩,hTail⟩ := hn.continuing_at_nonempty
    (by rintro _ ⟨_,_,_,hBad⟩; cases hBad) hr (Loader.traceAfterObservedEvent he hBefore.le)
  obtain rfl := Option.some.inj hReturn
  cases hv : rebuild 3 bytes with
  | error f =>
    have hFault : (afterLoad t [dst] bytes).fault = some f := by rw [afterLoad,hv]
    have hIndex : ((X.tr g).drop (pos+1))[j-(pos+1)]? = some target := by
      rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
      exact he
    exact (hSafe f (hTail.eventOfFault hFault hIndex)).elim
  | ok v =>
    refine ⟨_,?_,hTail⟩
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hv]
    have hu : At (next (setReg t dst v)) (pc+1) ((dst,v)::F) := ht.set hDest
    simpa only [next,setReg,ht.2.1,ht.2.2.1] using
      (hu.mono hu.2.2.2.2.2 : At (next (setReg t dst v)) (pc+1) F)

private theorem afterFirstRead (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) :
    ∃ pos ≤ j, ∃ s ending, At s (role.firstRead+1) (role.roots p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  obtain ⟨pos,hPos,t,ending,ht,hr⟩ := role.checkpointOfRead hp hX hCuQ (.inr rfl) he
  obtain ⟨pos',hPos',u,hu,hTail⟩ := role.firstGate hp ht hr hPos he (.inr rfl)
  obtain ⟨v,hLocal,hv⟩ := role.firstBranch hu
  by_cases hi : laneOf l g ≤ p.batch
  · have hAt : At v (role.firstRead-2) (role.roots p l g) := by
      simpa only [ite_eq_right (Nat.not_lt_of_ge hi)] using hv
    obtain ⟨s,hs,hn⟩ := role.firstTemplate hp hi hAt
    have hRun := hTail.after_local_nonempty hLocal (Loader.traceAfterObservedEvent he hPos')
    have hn0 := hn.continuing_at_nonempty
      (by rintro _ ⟨_,_,_,hBad⟩; cases hBad) hRun (Loader.traceAfterObservedEvent he hPos')
    obtain ⟨_,_,hRead,⟨_,_,rfl,_⟩,_⟩ := hn0
    have hStrict : pos' < j := by
      rcases Nat.eq_or_lt_of_le hPos' with hEq | hLt
      · have hPc := congrArg Event.pc (Option.some.inj ((hEq ▸ hRead).symm.trans he))
        have hNe : role.firstRead ≠ role.laterRead := by cases role <;> decide
        exact (hNe (hs.1.symm.trans hPc)).elim
      · exact hLt
    obtain ⟨w,hw,hRest⟩ := readAdvances
      (by cases role <;> simp [roots,frame,batchReg,laneReg,ctaReg,loadDst])
      (hs.mono hs.2.2.2.2.2) hn hRun hStrict he (by intro _ h; cases h)
    exact ⟨_,hStrict,w,ending,hw,hRest⟩
  · exact ⟨pos',hPos',v,ending,
      by simpa only [ite_eq_left (Nat.lt_of_not_ge hi)] using hv,
      hTail.after_local_nonempty hLocal (Loader.traceAfterObservedEvent he hPos')⟩

private theorem drainLoopCta {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} (hg : g < l.threads) {s : TState}
    (hs : At s 7659 (RowDrainRole.softmax.roots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 7660 ((1606,b32 (g/l.block)) :: RowDrainRole.softmax.roots p l g) := by
  have hCta : g/l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hGrid := hp.grid.2.2
  have hCta32 : g/l.block < 2^32 := by omega
  have hCoord : ((l.ctaidOf (g/l.block)).get .x) = g/l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  obtain ⟨u,hr,hu⟩ : ∃ u, run kernel [] l g 1 s = some u ∧
      At u 7660 ((1606,b32 (g/l.block)) :: RowDrainRole.softmax.roots p l g) := by
    dsimp only [roots,frame,batchReg,laneReg,ctaReg] at hs ⊢
    seg_fp hs using simp only [hCoord,b32,truncBits_ofNat hCta32 (by decide)]
  exact ⟨u,RowDrainRole.softmax.drainLocals (by decide) (by decide) hs.1 (by simp) hr,hu⟩

private theorem afterFirstToLoopSetup (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g pos j : Nat} {s : TState} {ending : Option TState}
    {a : Acc} {bytes : List (Option Byte)} (hg : g < l.threads)
    (hs : At s (role.firstRead+1) (role.roots p l g))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) (hPos : pos ≤ j)
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) :
    ∃ next ≤ j, ∃ t, At t ((scanSite role.scan).head-3)
        (((scanSite role.scan).cta,b32 (g/l.block)) :: role.roots p l g) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop next) ending := by
  cases role
  case softmax =>
    let toCta : RowDrainSpan := ⟨7622,7659,7720⟩
    obtain ⟨n,hn,t,ht,hTail⟩ := toCta.replayTo hp (by decide)
      (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel)
      (toCta.segmentKeeps_of_audit _
        (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel))
      (fun path h => toCta.traceAboveExit path (by decide +kernel) (by decide) h)
      Flow.code_7659 rfl hs hr hPos he (by intro _ h; cases h)
      (show ¬ (7622 ≤ 7677 ∧ 7677 < 7659) ∧ 7677 < 7720 by decide)
    obtain ⟨v,hLocal,hV⟩ := drainLoopCta hp hg ht
    let toSetup : RowDrainSpan := ⟨7660,7663,7720⟩
    exact toSetup.replayTo hp (by decide)
      (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel)
      (toSetup.segmentKeeps_of_audit _
        (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel))
      (fun path h => toSetup.traceAboveExit path (by decide +kernel) (by decide) h)
      Flow.code_7663 rfl hV
      (hTail.after_local_nonempty hLocal (Loader.traceAfterObservedEvent he hn))
      hn he (by intro _ h; cases h)
      (show ¬ (7660 ≤ 7677 ∧ 7677 < 7663) ∧ 7677 < 7720 by decide)
  case correction =>
    let toSetup : RowDrainSpan := ⟨9090,9130,9187⟩
    obtain ⟨n,hn,t,ht,hTail⟩ := toSetup.replayTo hp (by decide)
      (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel)
      (toSetup.segmentKeeps_of_audit _
        (by simp only [roots,frame,List.map_cons,List.map_nil]; decide +kernel))
      (fun path h => toSetup.traceAboveExit path (by decide +kernel) (by decide) h)
      Flow.code_9130 rfl hs hr hPos he (by intro _ h; cases h)
      (show ¬ (9090 ≤ 9144 ∧ 9144 < 9130) ∧ 9144 < 9187 by decide)
    exact ⟨n,hn,t,ht.mono ⟨ht.2.2.2.2.2.2.2.1,ht.2.2.2.2⟩,hTail⟩

private theorem initTwo (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {s : TState}
    (hs : At s ((scanSite role.scan).head-3)
      (((scanSite role.scan).cta,b32 (g/l.block)) :: role.roots p l g)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u ((scanSite role.scan).head-1)
        (groupScanFacts role.scan 0 p.batch (g/l.block) ++ role.roots p l g) := by
  let cta := g/l.block
  have hCta : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hGrid := hp.grid.2.2
  have hCta32 : g/l.block < 2^32 := by change cta < 2^32; omega
  have hSum32 : g/l.block+1 < 2^32 := by change cta+1 < 2^32; omega
  have hOne : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
  have hZero : truncBits 32 (BitVec.ofInt 64 0) = 0#64 := rfl
  have hLocal : ∃ u, run kernel [] l g 2 s = some u ∧
      At u ((scanSite role.scan).head-1)
        (groupScanFacts role.scan 0 p.batch (g/l.block) ++ role.roots p l g) := by
    cases role <;> dsimp only [scan,scanSite,groupScanFacts,roots,frame,batchReg,laneReg,ctaReg,
      List.cons_append,List.nil_append] at hs ⊢
    all_goals seg_fp hs using simp only [b32,hOne,hZero,← BitVec.ofNat_add,
      truncBits_ofNat hCta32 (by decide),truncBits_ofNat hSum32 (by decide)]
  obtain ⟨u,hr,hu⟩ := hLocal
  exact ⟨u,run_rtg (groupScanLocalRun role.scan (by cases role <;> decide)
    (by cases role <;> decide) hs.1 (by cases role <;> decide +kernel) hr),hu⟩

private theorem laterStarts (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g j : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) :
    ∃ pos ≤ j, ∃ s ending, At s (scanSite role.scan).head
        (groupScanFacts role.scan 0 p.batch (g/l.block) ++ role.roots p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  have hg : g < l.threads := event_thread_lt hX he
  obtain ⟨n,hn,s,ending,hs,hTail⟩ := role.afterFirstRead hp hX hCuQ he
  obtain ⟨k,hk,t,ht,hRun⟩ := role.afterFirstToLoopSetup hp hg hs hTail hn he
  obtain ⟨v,hLocal,hV⟩ := role.initTwo hp hg ht
  have hVRun := hRun.after_local_nonempty hLocal (Loader.traceAfterObservedEvent he hk)
  let site := scanSite role.scan
  let span : RowDrainSpan := ⟨site.head-1,site.head,role.laterExit⟩
  have hCode : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected
        ((groupScanFacts role.scan 0 p.batch (g/l.block) ++ role.roots p l g).map Prod.fst)
        i.op) = true := by
    simp only [groupScanFacts,roots,frame,List.map_append,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hSegments : span.segmentKeeps
      ((groupScanFacts role.scan 0 p.batch (g/l.block) ++ role.roots p l g).map Prod.fst) := by
    apply span.segmentKeeps_of_audit
    simp only [groupScanFacts,roots,frame,List.map_append,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hStop : ∃ i, kernel.code[span.stop]? = some i ∧ i.op.isLocal = true := by
    cases role
    · exact ⟨_,Flow.code_7666,rfl⟩
    · exact ⟨_,Flow.code_9133,rfl⟩
  obtain ⟨i,hi,hLocalStop⟩ := hStop
  have hBand : ¬ (span.lo ≤ role.laterRead ∧ role.laterRead < span.stop) ∧
      role.laterRead < span.bypass := by cases role <;> decide
  obtain ⟨pos,hPos,u,hU,hSuffix⟩ := span.replayTo hp (by cases role <;> decide)
    hCode hSegments
    (fun path h => span.traceAboveExit path (by cases role <;> decide +kernel)
      (by cases role <;> decide) h)
    hi hLocalStop hV hVRun hk he (by intro _ h; cases h) hBand
  exact ⟨pos,hPos,u,ending,hU,hSuffix⟩


private def loopFrame (role : RowDrainRole) (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) := groupScanFacts role.scan first p.batch (g/l.block) ++ role.roots p l g

private theorem laterBranch (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first : Nat} (hFirst : first < p.batch) {s : TState}
    (hs : At s ((scanSite role.scan).head+5)
      (((scanSite role.scan).advanced,b32 first) :: role.loopFrame p l g first)) :
    let ix := first + laneOf l g
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < ix then role.laterRead+1 else role.laterRead-2)
        ((role.laneIndexReg,b32 ix) :: role.loopFrame p l g first) := by
  dsimp only
  let site := scanSite role.scan
  let ix := first + laneOf l g
  let F := role.loopFrame p l g first
  have hLaunch := hp.shape.2.2
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hIndex : first + laneOf l g < 2^31 := by omega
  have hBatch := hp.shape.2.1
  have hFirst32 : first < 2^32 := by omega
  have hIdx32 : first + laneOf l g < 2^32 := by omega
  have hLane32 : laneOf l g < 2^32 := by omega
  have hBatch32 : p.batch < 2^32 := by omega
  have hLocal : ∃ u, run kernel [] l g 3 s = some u ∧
      At u (site.head+8)
        ((role.laneGuardReg,.pred (decide (p.batch < ix))) :: (role.laneIndexReg,b32 ix) :: F) := by
    dsimp only [site,F,loopFrame] at hs ⊢
    cases role <;>
      dsimp only [scan,scanSite,groupScanFacts,roots,frame,batchReg,laneReg,ctaReg,
        laneGuardReg,laneIndexReg,List.cons_append,List.nil_append] at hs ⊢
    all_goals seg_fp hs using simp only [ix,b32,← BitVec.ofNat_add,
      truncBits_ofNat hFirst32 (by decide),
      truncBits_ofNat hIdx32 (by decide),truncBits_ofNat hLane32 (by decide),
      truncBits_ofNat hBatch32 (by decide),compare,Option.getD_some,signedWord hIndex,
      signedWord hBatch,Int.ofNat_lt,gt_iff_lt]
  obtain ⟨t,hr,ht⟩ := hLocal
  have hPath := run_rtg (groupScanLocalRun role.scan (by cases role <;> decide)
    (by cases role <;> decide) hs.1 (by cases role <;> decide +kernel) hr)
  cases role
  · obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_7674 _ ht ht.2.2.2.2.1 (by simp)
    refine ⟨u,hPath.trans (run_rtg (groupScanLocalRun .softmaxDrain (by decide) (by decide)
      ht.1 (by simp) hu)),?_⟩
    simpa only [decide_eq_true_eq,laterRead] using hU.mono hU.2.2.2.2.2
  · obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
      Flow.code_9141 _ ht ht.2.2.2.2.1 (by simp)
    refine ⟨u,hPath.trans (run_rtg (groupScanLocalRun .correctionDrain (by decide) (by decide)
      ht.1 (by simp) hu)),?_⟩
    simpa only [decide_eq_true_eq,laterRead] using hU.mono hU.2.2.2.2.2

private theorem laterTemplate (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {g first index : Nat} {s : TState} (hi : index ≤ p.batch)
    (hs : At s (role.laterRead-2)
      ((role.laneIndexReg,b32 index) :: role.loopFrame p l g first)) :
    let a : Acc := {loc := globalLoc (p.cuQBase + 4*index), size := 4}
    ∃ t, At t role.laterRead
        ((role.laterAddressReg,b64 (p.cuQBase+4*index)) :: role.loopFrame p l g first) ∧
      Next kernel Assumptions.all l g s t (.read a (afterLoad t [role.laterDst])) := by
  dsimp only
  have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch+1) ≤ 2^64 at hRange
  have h32 : index < 2^32 := by have := hp.shape.2.1; omega
  have h31 : index < 2^31 := by have := hp.shape.2.1; omega
  have hOff : 4 * index < 2^64 := by omega
  have hBase : p.cuQBase < 2^64 := by omega
  have hAddr : p.cuQBase+4*index < 2^64 := by omega
  have h4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hOffset : BitVec.ofInt 64 ((index : Int)*4) = BitVec.ofNat 64 (4*index) := by
    change BitVec.ofInt 64 ((index : Int) * ((4 : Nat) : Int)) = _
    rw [← Int.natCast_mul,BitVec.ofInt_natCast,Nat.mul_comm]
  have hLocal : ∃ t, run kernel [] l g 2 s = some t ∧ At t role.laterRead
      ((role.laterAddressReg,b64 (p.cuQBase+4*index)) :: role.loopFrame p l g first) := by
    cases role <;>
      dsimp only [laterRead,laterAddressReg,laneIndexReg,loopFrame,scan,scanSite,
        groupScanFacts,roots,frame,batchReg,laneReg,ctaReg,List.cons_append,List.nil_append] at hs ⊢
    all_goals seg_fp hs using simp only [b64,truncBits_ofNat h32 (by decide),signedWord h31,h4,
      show (some IType.s == some IType.s) = true from rfl, ↓reduceIte, show 2*32 = 64 from rfl,
      hOffset,truncBits_ofNat hOff (by decide),
      truncBits_ofNat hBase (by decide),← BitVec.ofNat_add,truncBits_ofNat hAddr (by decide)]
  obtain ⟨t,hr,ht⟩ := hLocal
  have hPath := role.drainLocals (lo := role.laterRead-2) (n := 2)
    (by cases role <;> decide) (by cases role <;> decide) hs.1 (by cases role <;> decide +kernel) hr
  have hCore := role.drainCore (l := l) (s := t) (g := g)
    (by rw [ht.1]; cases role <;> decide) (by rw [ht.1]; cases role <;> decide)
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have hAligned : (p.cuQBase + 4*index) % 4 = 0 := by omega
  refine ⟨t,ht,⟨hPath,?_⟩⟩
  rw [hCore]
  cases role
  · rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_7677) rfl rfl]
    exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 hAddr (by decide) hAligned)
  · rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_9144) rfl rfl]
    exact congrArg Out.ev (loadTmpl_global ht.2.1 ht.2.2.2.2.1 hAddr (by decide) hAligned)


private theorem laterAbsentAfterExit (role : RowDrainRole) {l : Launch} {X : Execution}
    {g pos j : Nat} {s : TState} {ending : Option TState} {a : Acc} {bytes : List (Option Byte)}
    (hs : role.laterExit ≤ s.pc) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : pos ≤ j) (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) : False := by
  have hCode : (kernel.code.drop role.laterExit).all (fun i => staysPastEvent role.laterExit i.op) =
      true := by cases role <;> decide +kernel
  have hSites : ∀ pc ∈ Assumptions.swExp2Sites, pc < role.laterExit := by cases role <;> decide
  obtain ⟨_,hw⟩ := Mma.walkFromRun hr
  have hMem : (⟨role.laterRead,.rd a bytes⟩ : Event) ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := j-pos)
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  have hFalse : ¬ role.laterExit ≤ role.laterRead := by cases role <;> decide
  exact hFalse (eventTailEventsOfSegmentFloor hCode
    (fun pc hLo hm _ _ => (Nat.not_lt_of_ge hLo (hSites pc hm)).elim) hw hs _ hMem)

private theorem laterContinue (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g pos j first : Nat} {s : TState} {ending : Option TState}
    {a : Acc} {bytes : List (Option Byte)}
    (hs : At s (role.laterRead+1) (role.loopFrame p l g first))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) (hPos : pos ≤ j)
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) :
    ∃ next ≤ j, ∃ t, At t (scanSite role.scan).head (role.loopFrame p l g first) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop next) ending := by
  let site := scanSite role.scan
  let span : RowDrainSpan := ⟨role.laterRead+1,site.compare+2,role.laterExit⟩
  let F := role.loopFrame p l g first
  have hBranch : ∃ pred,
      kernel.code[span.stop]? = some ⟨some (pred,false),.bra site.head false⟩ := by
    cases role
    · exact ⟨_,Flow.code_7719⟩
    · exact ⟨_,Flow.code_9186⟩
  obtain ⟨pred,hStop⟩ := hBranch
  have hCode : ((kernel.code.drop span.lo).take (span.stop-span.lo)).all
      (fun i => span.inspected (F.map Prod.fst) i.op) = true := by
    simp only [F,loopFrame,groupScanFacts,roots,frame,List.map_append,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hSegments : span.segmentKeeps (F.map Prod.fst) := by
    apply span.segmentKeeps_of_audit
    simp only [F,loopFrame,groupScanFacts,roots,frame,List.map_append,List.map_cons,List.map_nil]
    cases role <;> decide +kernel
  have hBand : ¬ (span.lo ≤ role.laterRead ∧ role.laterRead < span.stop) ∧
      role.laterRead < span.bypass := by cases role <;> decide
  obtain ⟨next,hNext,u,hu,hTail⟩ := span.replayTo hp (by cases role <;> decide) hCode
    hSegments (fun path h => span.traceAboveExit path (by cases role <;> decide +kernel)
      (by cases role <;> decide) h)
    hStop rfl hs hr hPos he (by intro _ h; cases h) hBand
  have hIndexed : ((X.tr g).drop next)[j-next]? = some ⟨role.laterRead,.rd a bytes⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hNext]
    exact he
  obtain ⟨v,_,hPath,hEvent⟩ := hTail.before_event hIndexed
  have hV := (estep_source_pc hEvent).symm
  have hDecoded := hu.1.symm ▸ hStop
  have hTau : ∃ w, Tau kernel Assumptions.all l g u w := by
    generalize ((X.tr g).drop next).take (j-next) = events at hPath
    cases hPath with
    | refl =>
      have hNe : span.stop ≠ role.laterRead := by cases role <;> decide
      exact (hNe (hu.1.symm.trans hV)).elim
    | tau ht _ => exact ⟨_,ht⟩
    | event hs _ =>
      obtain ⟨i,hc,hLocal,_⟩ := estep_event_source hs
      obtain rfl := Option.some.inj (hDecoded.symm.trans hc)
      cases hLocal
  obtain ⟨w,hw⟩ := hTau
  have hRun := hTail.after_local_nonempty (.single hw) (Loader.traceAfterObservedEvent he hNext)
  have hCore : Tau kernel [] l g u w := by
    unfold Tau at hw ⊢
    rwa [← role.drainCore (by rw [hu.1]; cases role <;> decide)
      (by rw [hu.1]; cases role <;> decide)]
  rcases tau_core_frame hDecoded hCore with rfl | hFrame
  · have hPc : role.laterExit ≤ (skip u).pc := by
      change role.laterExit ≤ u.pc+1
      rw [hu.1]
      cases role <;> decide
    exact (role.laterAbsentAfterExit hPc hRun hNext he).elim
  · have hPc : w.pc = site.head := by simpa [nextPc,BrxTarget] using hFrame.pc
    have hRegs : w.regs = u.regs := by
      funext r
      exact hFrame.regs r (by simp [writesRegs])
    exact ⟨next,hNext,w,⟨hPc,hFrame.sub.trans hu.2.1,hFrame.acc.trans hu.2.2.1,
      hFrame.fault.trans hu.2.2.2.1,hRegs.symm ▸ hu.2.2.2.2⟩,hRun⟩

private theorem candidateReadOrSkip (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g pos j first : Nat} {s : TState} {ending : Option TState}
    {a : Acc} {bytes : List (Option Byte)} (hFirst : first < p.batch)
    (hs : At s ((scanSite role.scan).head+5)
      (((scanSite role.scan).advanced,b32 first) :: role.loopFrame p l g first))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) (hPos : pos ≤ j)
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩) :
    (∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4}) ∨
    (∃ next ≤ j, ∃ t, At t (role.laterRead+1) (role.loopFrame p l g first) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop next) ending) := by
  let ix := first + laneOf l g
  obtain ⟨u,hPath,hU⟩ := role.laterBranch hp hFirst hs
  have hUrun := hr.after_local_nonempty hPath (Loader.traceAfterObservedEvent he hPos)
  by_cases hIndex : first + laneOf l g ≤ p.batch
  · have hu : At u (role.laterRead-2) ((role.laneIndexReg,b32 ix)::role.loopFrame p l g first) := by
      simpa only [ite_eq_right (Nat.not_lt_of_ge hIndex)] using hU
    obtain ⟨v,hv,hn⟩ := role.laterTemplate hp hIndex hu
    rcases Nat.eq_or_lt_of_le hPos with rfl | hStrict
    · obtain ⟨_,_,hGet,⟨_,_,rfl,_⟩,_⟩ := hn.continuing_at_nonempty
        (by rintro _ ⟨_,_,_,hBad⟩; cases hBad) hUrun
        (Loader.traceAfterObservedEvent he le_rfl)
      rw [he] at hGet
      exact .inl ⟨ix,hIndex,(Kind.rd.inj (congrArg Event.kind (Option.some.inj hGet))).1⟩
    · obtain ⟨w,hw,hRun⟩ := readAdvances
        (by cases role <;> simp [loopFrame,groupScanFacts,roots,frame,scan,scanSite,
          batchReg,ctaReg,laneReg,laterDst])
        (hv.mono hv.2.2.2.2.2) hn hUrun hStrict he (by intro _ hh; cases hh)
      exact .inr ⟨_,hStrict,w,hw,hRun⟩
  · have hu : At u (role.laterRead+1) (role.loopFrame p l g first) := by
      simpa only [ite_eq_left (Nat.lt_of_not_ge hIndex)] using hU.mono hU.2.2.2.2.2
    exact .inr ⟨_,hPos,u,hu,hUrun⟩

private theorem laterReadWord (role : RowDrainRole) {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g : Nat} (hg : g < l.threads)
    {j : Nat} {a : Acc} {bytes : List (Option Byte)}
    (he : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩)
    (fuel first pos : Nat) (hFuel : p.batch-first = fuel) (hFirst : first ≤ p.batch)
    {s : TState} {ending : Option TState}
    (hs : At s (scanSite role.scan).head (role.loopFrame p l g first))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending) (hPos : pos ≤ j) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  induction fuel using Nat.strong_induction_on generalizing first pos s with
  | h fuel ih =>
    let site := scanSite role.scan
    let cta := g/l.block
    have hc : cta < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
    have hCta : cta+1 < 2^31 := by have := hp.grid.2.2; omega
    have hLaunch := hp.shape.2.2
    have hNext : first+31 < 2^31 := by omega
    have hStatic : ((kernel.code.drop site.head).take 5).all
        (fun i => ((role.roots p l g).map Prod.fst).all
          (fun r => !(writesRegs i.op).contains r)) = true := by
      simp only [roots,frame,List.map_cons,List.map_nil]
      cases role <;> decide +kernel
    obtain ⟨u,hu,hU⟩ := advanceGroupScanPreserving role.scan hNext hp.shape.2.1 hStatic hs
    have hUrun := hr.after_local_nonempty (run_rtg hu) (Loader.traceAfterObservedEvent he hPos)
    by_cases hClip : p.batch ≤ first+31
    · have hAt : At u site.compare [(site.work,b32 (cta+1)),(site.cta,b32 cta)] := by
        have h := hU.2.2.2.2
        rw [List.cons_append,List.cons_append,holds_cons,holds_cons,holds_append] at h
        have hPc := hU.1
        rw [ite_eq_left hClip] at hPc
        exact ⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,⟨h.2.1,h.2.2.1.2.2.2.1,trivial⟩⟩
      obtain ⟨v,hv,hV⟩ := exhaustedGroupScan role.scan hCta hAt
      exact (role.laterAbsentAfterExit hV.1.ge
        (hUrun.after_local_nonempty (run_rtg hv) (Loader.traceAfterObservedEvent he hPos))
        hPos he).elim
    have hMore : first+31 < p.batch := Nat.lt_of_not_ge hClip
    have hReady : At u (site.head+5)
        ((site.advanced,b32 (first+31))::role.loopFrame p l g (first+31)) := by
      have h := hU.2.2.2.2
      rw [List.cons_append,List.cons_append,holds_cons,holds_cons] at h
      have hPc := hU.1
      rw [ite_eq_right hClip] at hPc
      refine ⟨hPc,hU.2.1,hU.2.2.1,hU.2.2.2.1,?_⟩
      refine ⟨h.1,?_⟩
      simpa only [loopFrame,Nat.min_eq_left hMore.le] using h.2.2
    rcases role.candidateReadOrSkip hp hMore hReady hUrun hPos he with hWord | hContinue
    · exact hWord
    · obtain ⟨next,hBefore,v,hV,hTail⟩ := hContinue
      obtain ⟨k,hK,w,hW,hRest⟩ := role.laterContinue hp hV hTail hBefore he
      exact ih (p.batch-(first+31)) (by omega) (first+31) k rfl hMore.le hW hRest hK

/-- An optional request lookup during a later drain group. -/
@[no_expose] def LaterCuQRead (role : RowDrainRole) (X : Execution) (i : EvId)
    (a : Acc) (bytes : List (Option Byte)) : Prop := X.get i = some ⟨role.laterRead,.rd a bytes⟩

/-- Every observed later drain lookup addresses an in-range launch word. -/
theorem LaterCuQRead.word {role : RowDrainRole} {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {i : EvId} {a : Acc} {bytes : List (Option Byte)}
    (he : LaterCuQRead role X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  obtain ⟨g,j⟩ := i
  have hGet : X.get (g,j) = some ⟨role.laterRead,.rd a bytes⟩ := he
  obtain ⟨pos,hPos,s,ending,hs,hr⟩ := role.laterStarts hp hX hCuQ hGet
  exact role.laterReadWord hp (event_thread_lt hX hGet) hGet p.batch 0 pos rfl (Nat.zero_le _)
    hs hr hPos

end PTX.Kernels.TmlFa4Fwd.Thread.RowDrainRole
