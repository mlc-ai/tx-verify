-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCollectiveRanks

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyBroadcast
public import Kernels.TmlFa4Fwd.Proof.MmaInitialKeyPack
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.InitialScoreBroadcast
import Kernels.TmlFa4Fwd.Proof.Thread.QkIssueFlags
import Kernels.TmlFa4Fwd.Proof.MmaPvPrefixCut
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.Final
import Lemmas.Flow.Tc
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma (initialMmaTrace firstKLow pvRoleAfterEvent
  RoleShape normalBeforeLaterEvent initialQkBlock qkPc qkBReg qkSetupPc qkFirstSetupCount
  initialKeyPackFrame initialKeyPackFragment initialKeyPackSeed initialKeyPackStart pvCutCode
  initialKeyAddLocal initialKeyWordFrame initialKeyLowReg
  pvWalkCut requireReadySegmentNonempty localRun out_eq_core
  sharedDescriptor sharedDescriptorWord sharedDescriptor_decode sharedDescriptorWord_lt
  kvStart kvSlot qkFragment qkCode QueryOperandFragment advanceWalkLocals
  qkOperands qkStage qkKCopyByteLoc qkByteIndex qkLoaderLane qkLoaderByte qkIssueEvent)

open Prologue (warpIndex)
open PTX.Kernels.TmlFa4Fwd.Mma (SharedOperandRange qkOperandRange)

noncomputable section

set_option maxRecDepth 100000 in
private theorem keyReplyTail :
    (kernel.code.drop 2152).all (fun i => staysPastEvent 2152 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem keyReplySegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2152 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

variable {p : Params} {l : Launch}

private theorem keyReplyContinuation {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g send index : Nat} {valid : Bool}
    (hSend : InitialKeyBroadcast l X (g,send) (b32 (firstKLow l)) valid) {target : Event}
    (hTarget : X.get (g,index) = some target) (hLate : 2152 < target.pc) :
    ∃ t visits, At t 2152 [(2564,b32 (firstKLow l)),(1062,b32 12)] ∧
      Walk kernel Assumptions.all l g t ((X.tr g).drop (send+1)) visits ∧
      target ∈ (X.tr g).drop (send+1) := by
  let word := b32 (firstKLow l)
  let e : Event := ⟨2151,.shfl .idx word 0 31 word valid⟩
  have hGet : X.get (g,send) = some e := hSend
  have hBefore := traceOrderOfPcFloor hX keyReplyTail keyReplySegments hGet hTarget
    (show 2151 < 2152 by decide) hLate.le
  have hLength : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp hTarget).1
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ :=
    initialMmaTrace hp hX hGet (show 2145 ≤ 2151 by decide) (show 2151 < 2768 by decide)
  let es := (X.tr g).drop (base+1)
  have hLookup : es[send-(base+1)]? = some e := by
    dsimp only [es]
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
  have hRel : send-(base+1)+1 < es.length := by
    dsimp only [es]
    rw [List.length_drop]
    omega
  have hSRole : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
    ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
  obtain ⟨t,u,visits,hStep,hShape,hUWalk⟩ :=
    pvRoleAfterEvent hWalk (by rw [hs.1]; decide) hSRole hLookup hRel (show 2151 < 2768 by decide)
  have ht : t.pc = 2151 := (estep_source_pc hStep).symm
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source hStep
  rw [ht,Flow.code_2151] at hCode
  obtain rfl := Option.some.inj hCode
  obtain ⟨sent,b,c,recv,ok,hEvent,hu⟩ := fires_shfl (p := none) hFires
  have hWord : recv = word := by
    have hType := congrArg Event.kind hEvent
    exact (Kind.shfl.inj hType).2.2.2.2.1.symm
  subst recv
  have hU : u.pc = 2152 := by rw [hu]; exact congrArg (·+1) ht
  have hRegister : u.regs 2564 = some word := by
    rw [hu]
    simp [next,setReg]
  have hSuffix : es.drop (send-(base+1)+1) = (X.tr g).drop (send+1) := by
    rw [show es = (X.tr g).drop (base+1) from rfl,List.drop_drop,
      show base+1+(send-(base+1)+1) = send+1 by omega]
  rw [hSuffix] at hUWalk
  have hLater : target ∈ (X.tr g).drop (send+1) := by
    apply List.mem_of_getElem? (i := index-(send+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hBefore]
  have huAt : At u 2152 [(2564,word),(1062,b32 12)] :=
    ⟨hU,hShape.1.2.2 (by rw [hU]; decide),hShape.1.2.1,
      normalBeforeLaterEvent hUWalk hLater (hU.symm ▸ hLate),hRegister,hShape.2,trivial⟩
  exact ⟨u,visits,huAt,hUWalk,hLater⟩

set_option maxRecDepth 100000 in
private theorem keyFrameAtIssue {m : Mem0} (hp : Pre p l m) (stage : Fin 2) (frag : Fin 8) {g : Nat}
    {t : TState} {es : List Event} {vs : List Visit}
    (ht : At t 2152 [(2564,b32 (firstKLow l)),(1062,b32 12)])
    (hw : Walk kernel Assumptions.all l g t es vs) {e : Event} (he : e ∈ es)
    (hePc : e.pc = qkPc (initialQkBlock stage) + frag.val) :
    ∃ s rem post, s.pc = qkPc (initialQkBlock stage)+frag.val ∧
      s.regs (qkBReg (initialQkBlock stage)+frag.val) =
        some (b64 (sharedDescriptorWord (kvStart l 0+qkFragment frag) 16)) ∧
      Walk kernel Assumptions.all l g s rem post ∧ e ∈ rem := by
  let block := initialQkBlock stage
  let seed := qkSetupPc block 0-2
  let start := initialKeyPackStart block frag
  let finish := qkSetupPc block frag+qkFirstSetupCount frag
  let issue := qkPc block+frag.val
  let F := [(2564,b32 (firstKLow l)),(1062,b32 12)]
  let G := initialKeyPackFrame l block
  let H := [(qkBReg block+frag.val,
    b64 (sharedDescriptorWord (kvStart l 0+qkFragment frag) 16)),(1062,b32 12)]
  have hBounds : 2152 ≤ seed ∧ seed+2 ≤ start ∧ start < finish ∧ finish < issue ∧
      issue < 2768 := by
    fin_cases stage <;> fin_cases frag <;> decide
  have hShape : RoleShape t ∧ t.regs 1062 = some (b32 12) :=
    ⟨⟨ht.2.1.symm ▸ Nat.zero_le _,ht.2.2.1,fun _ => ht.2.1⟩,ht.2.2.2.2.2.1⟩
  have hCheck : ((kernel.code.drop 2152).take (seed-2152)).all
      (pvCutCode 2152 seed (F.map Prod.fst)) = true := by
    fin_cases stage <;> kernel_rfl
  obtain ⟨a,_,r,visits,_,haPc,haShape,haFacts,haWalk,haMem,_⟩ :=
    pvWalkCut (by decide) (by omega) hCheck hw (by rw [ht.1]; omega) hShape
      ht.2.2.2.2 he (by change e.pc = issue at hePc; omega)
  have ha : At a seed F := ⟨haPc,haShape.1.2.2 (by omega),haShape.1.2.1,
    normalBeforeLaterEvent haWalk haMem (by change e.pc = issue at hePc; omega),haFacts⟩
  obtain ⟨b,hSeed,hB⟩ := initialKeyPackSeed l g stage a ha
  have hSeedStraight : ((kernel.code.drop seed).take (2-1)).all
      (fun i => Epilogue.schedulerFallsThrough i.op) = true := by
    fin_cases stage <;> kernel_rfl
  have hSeedReal := localRun (by omega) (by omega) ha.1 hSeedStraight hSeed
  rcases advanceWalkLocals hSeedReal haWalk with hNil | ⟨_,_,_,hbWalk⟩
  · rw [hNil] at haMem
    cases haMem
  have hbShape : RoleShape b ∧ b.regs 1062 = some (b32 12) :=
    ⟨⟨hB.2.1.symm ▸ Nat.zero_le _,hB.2.2.1,fun _ => hB.2.1⟩,hB.2.2.2.2.2.2.1⟩
  let begin := qkSetupPc block 0
  have hFrom : begin = seed+2 := by fin_cases stage <;> decide
  have hCheck' : ((kernel.code.drop begin).take (start-begin)).all
      (pvCutCode begin start (G.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases frag <;> kernel_rfl
  obtain ⟨c,_,r,visits,_,hcPc,hcShape,hcFacts,hcWalk,hcMem,_⟩ :=
    pvWalkCut (show 1907 ≤ begin by omega) (show start < 2768 by omega) hCheck' hbWalk
      (by have hPc : b.pc = begin := hB.1; rw [hPc]; omega) hbShape hB.2.2.2.2
      haMem (by change e.pc = issue at hePc; omega)
  have hc : At c start G := ⟨hcPc,hcShape.1.2.2 (by omega),hcShape.1.2.1,
    normalBeforeLaterEvent hcWalk hcMem (by change e.pc = issue at hePc; omega),hcFacts⟩
  have hPackEntry :
      ∃ v rest visits, At v (finish-1) (initialKeyWordFrame l block frag) ∧
        Walk kernel Assumptions.all l g v rest visits ∧ e ∈ rest := by
    by_cases hFrag : frag.val = 0
    · have hZero : frag = 0 := Fin.ext hFrag
      subst frag
      have hAt : start = finish-1 := by fin_cases stage <;> decide
      have hFacts : G = initialKeyWordFrame l block 0 := by
        simp [G,initialKeyPackFrame,initialKeyWordFrame,initialKeyLowReg,qkFragment]
      exact ⟨c,_,_,hAt ▸ hFacts ▸ hc,hcWalk,hcMem⟩
    · obtain ⟨v,hAdd,hV⟩ := initialKeyAddLocal hp g stage frag hFrag c hc
      have hAddReal := localRun (show 1904 ≤ start by omega) (show start+1 ≤ 2768 by omega)
        hc.1 rfl hAdd
      rcases advanceWalkLocals hAddReal hcWalk with hNil | ⟨_,_,_,hvWalk⟩
      · rw [hNil] at hcMem
        cases hcMem
      have hOne : start+1 ≤ finish-1 := by
        fin_cases stage <;> fin_cases frag <;> first | exact (hFrag rfl).elim | decide
      have hAudit : ((kernel.code.drop (start+1)).take (finish-1-(start+1))).all
          (pvCutCode (start+1) (finish-1) ((initialKeyWordFrame l block frag).map Prod.fst)) =
          true := by
        fin_cases stage <;> fin_cases frag <;> kernel_rfl
      have hVShape : RoleShape v ∧ v.regs 1062 = some (b32 12) :=
        ⟨⟨hV.2.1.symm ▸ Nat.zero_le _,hV.2.2.1,fun _ => hV.2.1⟩,hV.2.2.2.2.2.2.1⟩
      obtain ⟨w,_,rest,visits,_,hPc,hSh,hF,hWalk,hM,_⟩ :=
        pvWalkCut (show 1907 ≤ start+1 by omega) (show finish-1 < 2768 by omega) hAudit
          hvWalk (by have hV' : v.pc = start+1 := hV.1; rw [hV']; omega)
          hVShape hV.2.2.2.2 hcMem (by change e.pc = issue at hePc; omega)
      have hw : At w (finish-1) (initialKeyWordFrame l block frag) :=
        ⟨hPc,hSh.1.2.2 (by omega),hSh.1.2.1,
          normalBeforeLaterEvent hWalk hM (by change e.pc = issue at hePc; omega),hF⟩
      exact ⟨w,rest,visits,hw,hWalk,hM⟩
  obtain ⟨pack,rPack,_,hPackAt,hPackWalk,hPMem⟩ := hPackEntry
  obtain ⟨d,hPack,hd⟩ := initialKeyPackFragment hp g stage frag pack hPackAt
  have hPackReal := localRun (show 1904 ≤ finish-1 by omega) (show finish-1+1 ≤ 2768 by omega)
    hPackAt.1 rfl hPack
  rcases advanceWalkLocals hPackReal hPackWalk with hNil | ⟨_,_,_,hdWalk⟩
  · rw [hNil] at hPMem
    cases hPMem
  have hdShape : RoleShape d ∧ d.regs 1062 = some (b32 12) :=
    ⟨⟨hd.2.1.symm ▸ Nat.zero_le _,hd.2.2.1,fun _ => hd.2.1⟩,hd.2.2.2.2.2.1⟩
  have hCheck'' : ((kernel.code.drop finish).take (issue-finish)).all
      (pvCutCode finish issue (H.map Prod.fst)) = true := by
    fin_cases stage <;> fin_cases frag <;> kernel_rfl
  obtain ⟨w,_,rem,post,_,hwPc,hwShape,hwFacts,hwWalk,hwMem,_⟩ :=
    pvWalkCut (show 1907 ≤ finish by omega) (show issue < 2768 by omega) hCheck'' hdWalk
      (by have hp : d.pc = finish := hd.1; rw [hp]; omega) hdShape hd.2.2.2.2
      hPMem (by change e.pc = issue at hePc; exact hePc.symm.le)
  exact ⟨w,rem,post,hwPc,hwFacts.1,hwWalk,hwMem⟩

set_option maxRecDepth 100000 in
private theorem qkIssueTail (stage : Fin 2) (frag : Fin 8) :
    (kernel.code.drop (qkPc (initialQkBlock stage)+frag.val+1)).all
      (fun i => staysPastEvent (qkPc (initialQkBlock stage)+frag.val+1) i.op) = true := by
  fin_cases stage <;> fin_cases frag <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem qkSegmentFloor : Assumptions.swExp2Sites.all (fun pos =>
    match cuteExp2.matchAt kernel pos with
    | some seg => decide (2267 ≤ seg.stop)
    | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
/-- A pending matching initial QK event must occur at its actual checkpoint. -/
theorem qkInitialStepAtCheckpoint {l : Launch} {g : Nat} (stage : Fin 2) (frag : Fin 8)
    {t : TState} {es : List Event} {vs : List Visit} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (ht : t.pc = qkPc (initialQkBlock stage)+frag.val)
    (hw : Walk kernel Assumptions.all l g t es vs)
    (he : (⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩ : Event) ∈ es) :
    ∃ u, EStep kernel Assumptions.all l g t
      ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩ (some u) := by
  let block := initialQkBlock stage
  let site := qkPc block+frag.val
  let floor := site+1
  let e : Event := ⟨site,.tc (.mma d op accum mask)⟩
  have hTail := qkIssueTail stage frag
  have hSeg : Assumptions.swExp2Sites.all (fun pos => match cuteExp2.matchAt kernel pos with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
    have hFloor : floor ≤ 2267 := by fin_cases stage <;> fin_cases frag <;> decide
    apply List.all_eq_true.mpr
    intro pos hPos
    have h := List.all_eq_true.mp qkSegmentFloor pos hPos
    cases hMatch : cuteExp2.matchAt kernel pos with
    | none => simp [hMatch] at h
    | some seg =>
      simp only [hMatch,decide_eq_true_eq] at h ⊢
      exact hFloor.trans h
  have hNot {u : TState} {events : List Event} {visits : List Visit}
      (hu : u.pc = t.pc+1) (hw : Walk kernel Assumptions.all l g u events visits) :
      e ∉ events := by
    intro he
    have hBound : floor ≤ u.pc := by rw [hu,ht]
    have h := eventTailEvents hTail hSeg hw hBound e he
    exact Nat.not_succ_le_self _ h
  have hCode := qkCode block frag
  change t.pc = qkPc block+frag.val at ht
  rw [← ht] at hCode
  have hLo : 1904 ≤ t.pc := by rw [ht]; fin_cases stage <;> fin_cases frag <;> decide
  have hHi : t.pc < 2768 := by rw [ht]; fin_cases stage <;> fin_cases frag <;> decide
  change e ∈ es at he
  cases hw with
  | stop => cases he
  | @tau t u es vs h hWalk =>
    have hCore : Tau kernel [] l g t u := by
      unfold Tau at h ⊢
      rwa [← out_eq_core hLo hHi]
    rcases tau_core_frame hCode hCore with rfl | hFrame
    · exact (hNot rfl hWalk he).elim
    · have hPc : u.pc = t.pc+1 := by
        simpa [nextPc,BrxTarget] using hFrame.pc
      exact (hNot hPc hWalk he).elim
  | ev h hWalk =>
    obtain ⟨i,hi,_,hFires⟩ := estep_event_source h
    have hInstr := Option.some.inj (hi.symm.trans hCode)
    subst i
    have hPc := congrArg TState.pc (fires_tcMma (.inr (.inl rfl)) hFires)
    rcases List.mem_cons.mp he with rfl | hm
    · exact ⟨_,h⟩
    · exact (hNot hPc hWalk hm).elim
  | last h =>
    obtain rfl := List.mem_singleton.mp he
    obtain ⟨tm,_,hFires⟩ := h
    rcases fires_none_ends hFires with ⟨f,hBad⟩ | hBad <;> cases hBad

set_option maxRecDepth 100000 in
/-- No lane can issue the same initial QK fragment twice. -/
theorem initialQkIssueIndexUnique {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (frag : Fin 8) {g i j d d' : Nat}
    {op op' : TcMma.OperandSpec} {accum accum' : Bool} {mask mask' : List Nat}
    (hi : X.get (g,i) = some ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d op accum mask)⟩)
    (hj : X.get (g,j) = some ⟨qkPc (initialQkBlock stage)+frag.val,.tc (.mma d' op' accum' mask')⟩)
    : i = j := by
  let block := initialQkBlock stage
  let site := qkPc block+frag.val
  have hBounds : 2145 ≤ site ∧ site < 2768 ∧ site+1 ≤ 2267 := by
    fin_cases stage <;> fin_cases frag <;> decide
  have hSeg : Assumptions.swExp2Sites.all (fun pos => match cuteExp2.matchAt kernel pos with
      | some seg => decide (site+1 ≤ seg.stop)
      | none => false) = true := by
    apply List.all_eq_true.mpr
    intro pos hPos
    have h := List.all_eq_true.mp qkSegmentFloor pos hPos
    cases hMatch : cuteExp2.matchAt kernel pos with
    | none => simp [hMatch] at h
    | some seg =>
      simp only [hMatch,decide_eq_true_eq] at h ⊢
      exact hBounds.2.2.trans h
  have noLater {a b dst : Nat} {o : TcMma.OperandSpec} {c : Bool} {masks : List Nat}
      {target : Event} (ha : X.get (g,a) = some ⟨site,.tc (.mma dst o c masks)⟩)
      (hb : X.get (g,b) = some target) (hPc : target.pc = site) (hOrder : a < b) : False := by
    obtain ⟨base,s,_,hBase,hs,hWalk⟩ := initialMmaTrace hp hX ha hBounds.1 hBounds.2.1
    let es := (X.tr g).drop (base+1)
    have hLookup : es[a-(base+1)]? = some ⟨site,.tc (.mma dst o c masks)⟩ := by
      dsimp only [es]
      rwa [List.getElem?_drop,Nat.add_sub_of_le hBase]
    have hLen : b < (X.tr g).length := (List.getElem?_eq_some_iff.mp hb).1
    have hRel : a-(base+1)+1 < es.length := by
      dsimp only [es]
      rw [List.length_drop]
      omega
    have hShape : RoleShape s ∧ s.regs 1062 = some (b32 12) :=
      ⟨⟨hs.2.1.symm ▸ Nat.zero_le _,hs.2.2.1,fun _ => hs.2.1⟩,hs.2.2.2.2.1⟩
    obtain ⟨t,u,_,hStep,_,hUWalk⟩ :=
      pvRoleAfterEvent hWalk (by rw [hs.1]; decide) hShape hLookup hRel hBounds.2.1
    have ht : t.pc = site := (estep_source_pc hStep).symm
    obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source hStep
    rw [ht,qkCode block frag] at hCode
    obtain rfl := Option.some.inj hCode
    have hu : site+1 ≤ u.pc := by
      have hNext := congrArg TState.pc (fires_tcMma (.inr (.inl rfl)) hFires)
      change u.pc = t.pc+1 at hNext
      rw [hNext,ht]
    have hSuffix : es.drop (a-(base+1)+1) = (X.tr g).drop (a+1) := by
      rw [show es = (X.tr g).drop (base+1) from rfl,List.drop_drop,
        show base+1+(a-(base+1)+1) = a+1 by omega]
    rw [hSuffix] at hUWalk
    have hLater : target ∈ (X.tr g).drop (a+1) := by
      apply List.mem_of_getElem? (i := b-(a+1))
      rwa [List.getElem?_drop,Nat.add_sub_of_le hOrder]
    have hPast := eventTailEvents (qkIssueTail stage frag) hSeg hUWalk hu _ hLater
    change site+1 ≤ target.pc at hPast
    omega
  rcases lt_trichotomy i j with h | rfl | h
  · exact (noLater hi hj rfl h).elim
  · rfl
  · exact (noLater hj hi rfl h).elim

private def keyTemplate (b : TcShared.Descriptor) : Tmpl → Prop
  | .tc (.mma _ op _ _) _ => op.b = b ∧ op.collector = {}
  | .ub _ => True
  | _ => False

private theorem keyTemplateOfExec {b : TcShared.Descriptor} {r : Exec Tmpl}
    (h : AllOk (keyTemplate b) r) : keyTemplate b (ofExec r) := by
  cases r
  · trivial
  · exact h

private theorem bindOk {α β : Type} (x : α) (f : α → Exec β) :
    (Except.ok x : Exec α) >>= f = f x := rfl

private theorem keyTemplateDecode {l : Launch} {g : Nat} {t : TState} {d r : Nat}
    {a id en : Opnd} {masks : List Opnd} {word : Nat} {kd : TcShared.Descriptor}
    (hRead : readBits l g t 64 (.reg r) = .ok (BitVec.ofNat 64 word))
    (hWord : (BitVec.ofNat 64 word).toNat = word)
    (hDecode : TcShared.decode word = some kd) :
    keyTemplate kd (eventTmpl Assumptions.all l g t
      (.tcMma (.dense .one false .f16 d (.smem a) (.reg r) id masks en))) := by
  simp only [eventTmpl,tcTmpl_tcMma_smem (.inr (.inl rfl)),mmaSmemTmpl]
  apply keyTemplateOfExec
  simp only [hRead,bindOk,hWord,hDecode]
  by_cases hg : g < l.threads
  · simp only [hg,↓reduceIte]
    apply allOk_bind (r := readBits l g t 32 (.reg d))
    intro dst
    apply allOk_bind (r := readBits l g t 64 a)
    intro aBits
    apply allOk_bind (r := readBits l g t 32 id)
    intro iBits
    apply allOk_bind (r := masks.mapM (readBits l g t 32))
    intro values
    by_cases hCount : masks.length = 4 * CtaGroup.one.size
    · simp only [hCount,↓reduceIte]
      apply allOk_bind (r := mmaEnable t en)
      intro enabled
      apply allOk_bind (r := zeroColumnMaskOk l g t none)
      intro zcm
      cases hA : TcShared.decode aBits.toNat with
      | none => trivial
      | some da =>
        cases hD : TcMma.decode .one false .f16 iBits.toNat with
        | none => trivial
        | some desc =>
          cases hMade : TcMma.makeOperands l (g/l.block) desc da kd with
          | none => simp only [hMade]; trivial
          | some spec =>
            simp only [hMade]
            unfold TcMma.makeOperands at hMade
            obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp hMade
            obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
            exact ⟨congrArg TcMma.OperandSpec.b (Option.some.inj h).symm,rfl⟩
    · simp only [hCount,↓reduceIte]
      trivial
  · simp only [hg,↓reduceIte]
    trivial

private theorem keyTemplateFires {pc dst : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} {m : Tmpl} {u : TState} {b : TcShared.Descriptor}
    (h : keyTemplate b m) (he : Fires pc m ⟨pc,.tc (.mma dst op accum mask)⟩ (some u)) :
    op.b = b ∧ op.collector = {} := by
  cases m <;> simp only [keyTemplate] at h
  case tc k _ =>
    cases k <;> try contradiction
    cases congrArg Event.kind he.1
    exact h
  case ub => cases he.2

private theorem initialKeyIssueFields {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {commit : EvId} {spec : TcCommit.Spec}
    (hCommit : SecondOutputCommit X commit spec) (stage : Fin 2) :
    ∃ base : Nat, ∀ frag : Fin 8, ∃ wait op,
      let issue : EvId := (commit.1,base+frag.val)
      X.get issue = some ⟨qkPc (initialQkBlock stage)+frag.val,
        .tc (.mma (scoreColumn stage) op (decide (frag.val ≠ 0)) (List.replicate 4 0))⟩ ∧
      TraceBefore X issue commit ∧
      QueryOperandFragment l commit.1 stage frag op ∧
      Mma.ReadyPoll l X commit.1 wait 0 0 true .cta ∧ TraceBefore X (commit.1,wait) issue ∧
      (Mma.atPrefix l X commit.1 wait).kvAcquires 0 = 0 ∧
      op.b = sharedDescriptor (kvStart l 0+qkFragment frag) 16 ∧ op.collector = {} := by
  obtain ⟨g,j⟩ := commit
  obtain ⟨send,valid,hSend,_⟩ := initialKeyReplyBeforeSecondOutputCommit hp hX hCommit
  obtain ⟨base,hFrags⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.initialQueryOperandsBeforeFinalCommit hp hX (.inr rfl)
      hCommit.decoded stage
  refine ⟨base,?_⟩
  intro frag
  obtain ⟨d,op,accum,mask,hBefore,hGet,hOp⟩ := hFrags frag
  let block := initialQkBlock stage
  let e : Event := ⟨qkPc block+frag.val,.tc (.mma d op accum mask)⟩
  have hSite : 2152 < e.pc := by
    change 2152 < qkPc block+frag.val
    fin_cases stage <;> simp [block,initialQkBlock,qkPc] <;> omega
  obtain ⟨t,vs,ht,hw,he⟩ := keyReplyContinuation hp hX hSend hGet hSite
  obtain ⟨s,rem,post,hPc,hReg,hsWalk,hsMem⟩ := keyFrameAtIssue hp stage frag ht hw he rfl
  obtain ⟨u,hStep⟩ := qkInitialStepAtCheckpoint stage frag hPc hsWalk hsMem
  let b := kvStart l 0+qkFragment frag
  have hShared : b < 2^18 ∧ b % 16 = 0 := by
    have := hp.shared.2.1
    have := hp.shared.1
    have hFrag : qkFragment frag < 16496 ∧ qkFragment frag % 16 = 0 := by
      fin_cases frag <;> decide
    simp only [b,kvStart,show kvSlot 0 = 0 from rfl,Nat.mul_zero,Nat.add_zero]
    omega
  have hBound := sharedDescriptorWord_lt hShared.1 hShared.2 (.inl rfl)
  have hRead := readBits_b64 (L := l) (g := g) hReg hBound
  have hWord := toNat_ofNat_lt hBound
  have hDecode := sharedDescriptor_decode hShared.1 hShared.2 (.inl rfl)
  obtain ⟨i,hCode,_,hFires⟩ := estep_event_source hStep
  rw [hPc,qkCode block frag] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  have hB := keyTemplateFires (keyTemplateDecode hRead hWord hDecode) hFires
  obtain ⟨wait,hWaitBefore,loc,parity,acq,scope,hWait,_⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.pendingReadyOrdinal hp hX 0 hGet
      (by
        change (PTX.Kernels.TmlFa4Fwd.Mma.slotWait 0).pc+3 ≤ qkPc block+frag.val ∧
          qkPc block+frag.val ≤ (PTX.Kernels.TmlFa4Fwd.Mma.slotElect 0).pc
        fin_cases stage <;> fin_cases frag <;> decide)
  obtain ⟨rfl,rfl,rfl,rfl⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.initialReadyPollOperands hp hX hWait
  obtain ⟨td,_,_,hDstPc,hDReg,hDWalk,hDMem⟩ :=
    initialScoreDestinationFrame hp hX hCommit stage frag hGet rfl
  obtain ⟨ud,hDStep⟩ := qkInitialStepAtCheckpoint stage frag hDstPc hDWalk hDMem
  have hD32 : scoreColumn stage < 2^32 := by fin_cases stage <;> decide
  obtain ⟨hD,hAcc,hMask⟩ := qkStepFields block frag (dst := some (scoreColumn stage))
    (fun col hc => by
      have hc' : scoreColumn stage = col := by simpa using hc
      subst col
      exact ⟨hDReg,hD32⟩) hDStep
  have hDst := hD (scoreColumn stage) (by simp)
  subst d
  subst accum
  subst mask
  refine ⟨wait,op,hGet,⟨rfl,hBefore,?_⟩,hOp,⟨_,hWait,rfl⟩,
    ⟨rfl,hWaitBefore,?_⟩,initialKeyWaitOrdinal hp hX hCommit hWait,hB⟩
  · exact (List.getElem?_eq_some_iff.mp hCommit.decoded).1
  · exact (List.getElem?_eq_some_iff.mp hGet).1

/-- Both initial QK issue banks use the physical slot-zero key descriptor. -/
theorem initialKeyIssuesWithDescriptorBeforeSecondOutputCommit {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {commit : EvId}
    {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) (stage : Fin 2) :
    ∃ base : Nat, ∀ frag : Fin 8, ∃ wait d op accum mask,
      let issue : EvId := (commit.1,base+frag.val)
      X.MmaIssue issue d op accum mask ∧ TraceBefore X issue commit ∧
      QueryOperandFragment l commit.1 stage frag op ∧
      Mma.ReadyPoll l X commit.1 wait 0 0 true .cta ∧ TraceBefore X (commit.1,wait) issue ∧
      (Mma.atPrefix l X commit.1 wait).kvAcquires 0 = 0 ∧
      op.b = sharedDescriptor (kvStart l 0+qkFragment frag) 16 := by
  obtain ⟨base,hFrags⟩ := initialKeyIssueFields hp hX hCommit stage
  refine ⟨base,?_⟩
  intro frag
  obtain ⟨wait,op,hMma,hOrder,hOp,hReady,hAcquire,hFirst,hB,_⟩ := hFrags frag
  exact ⟨wait,_,op,_,_,⟨_,hMma⟩,hOrder,hOp,hReady,hAcquire,hFirst,hB⟩

/-- The observed final O1 issuer emitted both initial score banks with the resolved
operands, destination, and clear/accumulate flags. -/
theorem initialCanonicalQkIssuesBeforeSecondOutputCommit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {commit : EvId} {spec : TcCommit.Spec}
    (hCommit : SecondOutputCommit X commit spec) (stage : Fin 2) :
    ∃ base : Nat, ∀ frag : Fin 8, ∃ wait,
      let issue : EvId := (commit.1,base+frag.val)
      X.get issue = some (qkIssueEvent l commit.1 (initialQkBlock stage) frag 0) ∧
      TraceBefore X issue commit ∧ Mma.ReadyPoll l X commit.1 wait 0 0 true .cta ∧
      TraceBefore X (commit.1,wait) issue ∧ (Mma.atPrefix l X commit.1 wait).kvAcquires 0 = 0 := by
  obtain ⟨base,hFrags⟩ := initialKeyIssueFields hp hX hCommit stage
  refine ⟨base,?_⟩
  intro frag
  obtain ⟨wait,op,hMma,hOrder,hOp,hReady,hAcquire,hFirst,hB,hCollector⟩ := hFrags frag
  have hStage : qkStage (initialQkBlock stage) = stage :=
    Fin.ext (Nat.mod_eq_of_lt stage.isLt)
  have hExact : op = qkOperands l commit.1 (initialQkBlock stage) frag 0 := by
    rw [qkOperands,hStage]
    cases op
    congr 1
    all_goals first
      | exact hOp.descriptor | exact hOp.address | exact hOp.ctaLow
      | exact hOp.ctaHigh | exact hOp.shared
  rw [hExact] at hMma
  exact ⟨wait,by simpa only [qkIssueEvent,hStage] using hMma,hOrder,hReady,hAcquire,hFirst⟩

/-- Both initial QK banks before the final O1 commit have the full specified
operands and acquire the ordinal-zero K packet. -/
theorem initialKeyExactIssuesBeforeSecondOutputCommit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {commit : EvId} {spec : TcCommit.Spec}
    (hCommit : SecondOutputCommit X commit spec) (stage : Fin 2) :
    ∃ base : Nat, ∀ frag : Fin 8, ∃ wait d accum mask,
      let issue : EvId := (commit.1,base+frag.val)
      X.MmaIssue issue d (qkOperands l commit.1 (initialQkBlock stage) frag 0) accum mask ∧
      TraceBefore X issue commit ∧ Mma.ReadyPoll l X commit.1 wait 0 0 true .cta ∧
      TraceBefore X (commit.1,wait) issue ∧ (Mma.atPrefix l X commit.1 wait).kvAcquires 0 = 0 := by
  obtain ⟨base,hFrags⟩ := initialCanonicalQkIssuesBeforeSecondOutputCommit hp hX hCommit stage
  refine ⟨base,?_⟩
  intro frag
  obtain ⟨wait,hMma,hOrder,hReady,hAcquire,hFirst⟩ := hFrags frag
  exact ⟨wait,_,_,_,⟨_,hMma⟩,hOrder,hReady,hAcquire,hFirst⟩

/-- Physical byte in the first key packet as addressed by an initial QK fragment. -/
def initialKeyByte (l : Launch) (cta : Nat) (fragment : Fin 8) (row k byte : Nat) : Loc :=
  ⟨.shared, cta, kvCopyAddress l.sharedBase 0 (qkLoaderLane fragment row k) (row / 8)
    (decide (4 ≤ fragment.val)) + qkLoaderByte fragment k byte⟩

/-- An actual initial QK fragment addresses the chosen key byte before O1 is committed. -/
theorem initialKeyByteReadBeforeSecondOutputCommit {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {commit : EvId} {spec : TcCommit.Spec}
    (hCommit : SecondOutputCommit X commit spec) (stage : Fin 2) (frag : Fin 8) {row k byte : Nat}
    (hRow : row < 128) (hK : k < 16) (hByte : byte < 2) :
    ∃ wait mma d op accum mask, X.MmaIssue mma d op accum mask ∧
      TraceBefore X mma commit ∧ Mma.ReadyPoll l X commit.1 wait 0 0 true .cta ∧
      TraceBefore X (commit.1,wait) mma ∧ (Mma.atPrefix l X commit.1 wait).kvAcquires 0 = 0 ∧
      op.byteLoc .b (qkByteIndex row k byte) =
        some (initialKeyByte l (commit.1/l.block) frag row k byte) := by
  obtain ⟨_, hFrags⟩ := initialKeyExactIssuesBeforeSecondOutputCommit hp hX hCommit stage
  obtain ⟨wait,d,accum,mask,hMma,hOrder,hReady,hAcquire,hFirst⟩ := hFrags frag
  refine ⟨wait,_,d,_,accum,mask,hMma,hOrder,hReady,hAcquire,hFirst,?_⟩
  rw [qkKCopyByteLoc l commit.1 (initialQkBlock stage) frag 0 hp.shared.1 hRow hK hByte]
  rfl

/-- The actual K shared descriptor is the word decoded at a QK instruction's B register. -/
theorem qkKeyDescriptorOfRegister {m : Mem0} (hp : Pre p l m) (block : Fin 4) (step : Fin 8)
    (use : Nat) {g d : Nat} {t u : TState} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hReg : t.regs (qkBReg block+step.val) =
      some (b64 (sharedDescriptorWord (kvStart l use+qkFragment step) 16)))
    (hStep : EStep kernel Assumptions.all l g t
      ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩ (some u)) :
    op.b = sharedDescriptor (kvStart l use+qkFragment step) 16 := by
  let b := kvStart l use+qkFragment step
  have hBound : b < 2^18 ∧ b % 16 = 0 := by
    have hBase := hp.shared.2.1
    have hAlign := hp.shared.1
    have hUse := Nat.mod_lt use (show 0 < 3 by decide)
    have hFrag : qkFragment step < 16496 ∧ qkFragment step % 16 = 0 := by
      fin_cases step <;> decide
    dsimp only [b,kvStart,kvSlot]
    omega
  have hWord := sharedDescriptorWord_lt hBound.1 hBound.2 (.inl rfl)
  have hRead := readBits_b64 (L := l) (g := g) hReg hWord
  have hDecode := sharedDescriptor_decode hBound.1 hBound.2 (.inl rfl)
  have hPc := (estep_source_pc hStep).symm
  obtain ⟨ins,hCode,_,hFires⟩ := estep_event_source hStep
  rw [hPc,qkCode block step] at hCode
  obtain rfl := Option.some.inj hCode
  rw [hPc] at hFires
  exact (keyTemplateFires (keyTemplateDecode hRead (toNat_ofNat_lt hWord) hDecode)
    hFires).1

/-- An actual issue of either initial QK bank reads the physical slot-zero key. -/
theorem QkInstruction.initialKeyOperand {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {issue : EvId} {step : Fin 8}
    {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X issue (initialQkBlock stage) step d op accum mask) :
    op.b = sharedDescriptor (kvStart l 0+qkFragment step) 16 := by
  obtain ⟨g,index⟩ := issue
  let block := initialQkBlock stage
  let e : Event := ⟨qkPc block+step.val,.tc (.mma d op accum mask)⟩
  have hGet : X.get (g,index) = some e := hIssue.decoded
  have hPc : 2153 < e.pc ∧ e.pc < 2763 ∧ e.pc ∉ registerHintSites := by
    change 2153 < qkPc block+step.val ∧ qkPc block+step.val < 2763 ∧
      qkPc block+step.val ∉ registerHintSites
    fin_cases stage <;> fin_cases step <;> decide
  have hRole := roleBodyPcOfEvent hp hX hGet (by omega) hPc.2.2
  have hWarp : warpIndex l g = 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with hExit | hBody
    · omega
    · split_ifs at hBody <;> omega
  obtain ⟨first,inst,lead,_,hElect⟩ :=
    firstMmaElectionBeforeEvent hp hX hGet hWarp ⟨hPc.1,hPc.2.1⟩
  obtain ⟨send,ok,hSend,_⟩ := initialKeyReplyBeforeFirstElection hp hX hElect
  obtain ⟨t,vs,ht,hw,he⟩ := keyReplyContinuation hp hX hSend hGet (by omega)
  obtain ⟨s,rem,post,hs,hReg,hWalk,hFound⟩ := keyFrameAtIssue hp stage step ht hw he rfl
  obtain ⟨u,hStep⟩ := qkInitialStepAtCheckpoint stage step hs hWalk hFound
  exact qkKeyDescriptorOfRegister hp block step 0 hReg hStep

end
end PTX.Kernels.TmlFa4Fwd.Thread
