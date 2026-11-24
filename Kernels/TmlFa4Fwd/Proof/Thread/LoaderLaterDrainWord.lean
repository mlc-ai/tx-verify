-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import all Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Kernels.TmlFa4Fwd.Flow.Code.Part027
import Kernels.TmlFa4Fwd.Flow.Code.Part028

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader
  (loaderPipelineCutOp ringShapeOfAt loaderLinear traceAfterObservedEvent loaderOutCore
    loaderPipelineStepRegs loaderRingWrites loaderPipelineStepShape loaderSubstepAtNewPc
    prefixProjectionsCutOrEvent)

private theorem drainSigned {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (BitVec.ofNat 64 n) = (n : Int) := by
  simp only [toSigned, toNat_ofNat_lt (show n < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega), ite_eq_left hn]

variable {p : Params} {l : Launch} {m : Mem0}

private theorem laterDrainGroup (hp : Pre p l m) {g first carry : Nat} (hf : first ≤ p.batch) :
    Seg kernel [] l g 4 1794 [(7190,b32 first),(7145,b32 p.batch),(1173,b32 carry)] 1798
      [(1174,b32 (first+31)),(241,.pred (decide (p.batch ≤ first+31))),
        (7190,b32 (min (first+31) p.batch)),(7191,b32 carry)] := by
  intro t ht
  have hLaunch := hp.shape.2.2
  have hSize : p.batch < 2 ^ 22 := by omega
  have hNext : first + 31 < 2 ^ 31 := by omega
  have hBatch : p.batch < 2 ^ 31 := by omega
  have hFirst32 : first < 2 ^ 32 := by omega
  have hNext32 : first + 31 < 2 ^ 32 := by omega
  have hBatch32 : p.batch < 2 ^ 32 := by omega
  have hLit : truncBits 32 (BitVec.ofInt 64 31) = BitVec.ofNat 64 31 := rfl
  seg_fp ht using
    simp only [b32,hLit,← BitVec.ofNat_add,truncBits_ofNat hFirst32 (by decide),
      truncBits_ofNat hNext32 (by decide),truncBits_ofNat hBatch32 (by decide),
      compare,Option.getD_some,
      drainSigned hNext,drainSigned hBatch,Int.ofNat_le,ge_iff_le]
    all_goals
      by_cases h : first + 31 < p.batch
      · simp [Nat.min_eq_left (Nat.le_of_lt h)]
        omega
      · simp [Nat.min_eq_right (Nat.le_of_not_lt h)]
        omega

private theorem laterDrainLaneGate (hp : Pre p l m) {g first : Nat} (hFirst : first < p.batch) :
    Seg kernel [] l g 3 1799 [(1174,b32 first),(1073,b32 (laneOf l g)),(7145,b32 p.batch)] 1802
      [(1175,b32 (first+laneOf l g)),(242,.pred (decide (p.batch < first+laneOf l g))),
        (7186,b32 0)] := by
  intro t ht
  have hLaunch := hp.shape.2.2
  have hLane : laneOf l g < 32 := Nat.mod_lt _ (by decide)
  have hIndex : first+laneOf l g < 2 ^ 31 := by omega
  have hBatch : p.batch < 2 ^ 31 := by omega
  have hFirst32 : first < 2 ^ 32 := by omega
  have hIdx32 : first+laneOf l g < 2 ^ 32 := by omega
  have hLane32 : laneOf l g < 2 ^ 32 := by omega
  have hBatch32 : p.batch < 2 ^ 32 := by omega
  have hZero : truncBits 32 (BitVec.ofInt 64 0) = 0#64 := rfl
  seg_fp ht using
    simp only [b32,← BitVec.ofNat_add,truncBits_ofNat hFirst32 (by decide),
      truncBits_ofNat hIdx32 (by decide),truncBits_ofNat hLane32 (by decide),
      truncBits_ofNat hBatch32 (by decide),compare,Option.getD_some,
      drainSigned hIndex,drainSigned hBatch,Int.ofNat_lt,gt_iff_lt,hZero]

private theorem laterDrainAddress (hp : Pre p l m) {g index : Nat} (hi : index ≤ p.batch) :
    Seg kernel [] l g 2 1803 [(1175,b32 index),(7506,b64 p.cuQBase)] 1805
      [(7860,b64 (p.cuQBase+4*index))] := by
  intro t ht
  have hBatch := hp.shape.2.1
  have hRegion := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2 ^ 64 at hRegion
  have h31 : index < 2 ^ 31 := by omega
  have hAddr : p.cuQBase+4*index < 2 ^ 64 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hOff : 4*index < 2 ^ 64 := by omega
  have hBase : p.cuQBase < 2 ^ 64 := by omega
  have hI4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hPr : (index : Int) * 4 = ((4*index : Nat) : Int) := by
    push_cast
    omega
  seg_fp ht using simp only [b64,kind_s_beq_s,↓reduceIte,hI4,drainSigned h31,
    truncBits_ofNat h32 (by decide),truncBits_ofNat hOff (by decide),
    truncBits_ofNat hBase (by decide),
    hPr,BitVec.ofInt_natCast,← BitVec.ofNat_add,truncBits_ofNat hAddr (by decide)]

private theorem observesAfterCut {l : Launch} {X : Execution}
    {g pos j low cut bypass : Nat} {a : Acc} {bs : List (Option Byte)}
    {s : TState} {o : Option TState} {F : List (Nat × Value)}
    (hMin : 174 ≤ low) (hMax : cut ≤ 1901)
    (hCode : ((kernel.code.drop low).take (cut-low)).all
      (fun ins => loaderPipelineCutOp low cut bypass (F.map Prod.fst) ins.op) = true)
    (hFloor : ∀ {x y : TState} {es : List Event},
      TraceReach kernel Assumptions.all l g x es y → bypass < x.pc → bypass < y.pc)
    (hBounds : low ≤ s.pc ∧ s.pc ≤ cut) (hTarget : cut ≤ 1805 ∧ 1805 ≤ bypass)
    (hs : At s s.pc F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o)
    (hPos : pos ≤ j) (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) :
    ∃ mid start, start ≤ j ∧ At mid cut F ∧
      Run kernel Assumptions.all l g mid ((X.tr g).drop start) o := by
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some ⟨1805,.rd a bs⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨t,_,hPath,hEvent⟩ := hr.before_event hIndexed
  have ht : t.pc = 1805 := (estep_source_pc hEvent).symm
  obtain ⟨mid,pre,_,hSplit,hPc,hSub,hAcc,hRegs,hPrefix,_⟩ :=
    loaderCutOfObservedPath hPath hMin hMax hCode hFloor hBounds (ringShapeOfAt hs)
      (fun _ => hs.2.1) hs.2.2.2.2 (ht.symm ▸ hTarget)
  obtain ⟨hBefore,hTail⟩ := resumeAtCut hr hPos he hSplit hPrefix
  have hFault : mid.fault = none := by
    cases hf : mid.fault with
    | none => rfl
    | some f =>
      have hIndex : ((X.tr g).drop (pos+pre.length))[j-(pos+pre.length)]? =
          some ⟨1805,.rd a bs⟩ := by
        rw [List.getElem?_drop,Nat.add_sub_of_le hBefore]
        exact he
      cases hTail.eventOfFault hf hIndex
  exact ⟨mid,_,hBefore,⟨hPc,hSub,hAcc,hFault,hRegs⟩,hTail⟩

private noncomputable def laterDrainRoots (p : Params) (l : Launch) (g : Nat) :
    List (Nat × Value) :=
  (7145,b32 p.batch)::drainRootFrame p l g

private theorem laterDrainEndFloor {l : Launch} {g : Nat} {x y : TState}
    {es : List Event}
    (h : TraceReach kernel Assumptions.all l g x es y)
    (hx : 1847 < x.pc) : 1847 < y.pc := by
  have hAudit : (kernel.code.drop 1848).all (fun i => staysPastEvent 1848 i.op) = true := by
    decide +kernel
  have hSeg : Assumptions.swExp2Sites.all (fun pc => match PTX.Assumption.cuteExp2.matchAt
        kernel pc with
      | some seg => decide (1848 ≤ seg.stop)
      | none => false) = true := by decide +kernel
  induction h with
  | refl => exact hx
  | tau he _ ih => exact ih (eventTailStepOfAudit hAudit hSeg hx (.inl ⟨rfl,he⟩))
  | event he _ ih => exact ih (eventTailStepOfAudit hAudit hSeg hx (.inr ⟨_,rfl,he⟩))

private theorem laterDrainStarts {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {g j : Nat}
    {a : Acc} {bs : List (Option Byte)} (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) :
    ∃ s pos ending, pos ≤ j ∧
      At s 1794 ((7190,b32 0)::(1173,b32 (g/l.block+1))::laterDrainRoots p l g) ∧
      Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending := by
  obtain ⟨pos,hPos,t,ending,ht,hRun⟩ := actualDrainCut hp hX hCuQ (.inr rfl) he
  obtain ⟨s,hFirst,hs⟩ := loaderFirstDrainGate hp ht
  have hBounds : 1748 ≤ s.pc ∧ s.pc ≤ 1791 := by
    rw [hs.1]
    split <;> decide
  let root := laterDrainRoots p l g
  have hRootCode : ((kernel.code.drop 1748).take (1791-1748)).all
      (fun ins => loaderPipelineCutOp 1748 1791 1847 (root.map Prod.fst) ins.op) = true := by
    change ((kernel.code.drop 1748).take (1791-1748)).all
      (fun ins => loaderPipelineCutOp 1748 1791 1847 [7145,1073,7506,1072] ins.op) = true
    decide +kernel
  obtain ⟨u,first,hFirstPos,hu,huRun⟩ := observesAfterCut (by decide) (by decide) hRootCode
    laterDrainEndFloor hBounds (by decide) ⟨rfl,hs.2⟩
    (hRun.after_local_nonempty hFirst (traceAfterObservedEvent he hPos)) hPos he
  let frame := (7190,b32 0)::(1173,b32 (g/l.block+1))::root
  have hLimits : g/l.block + 1 < 2 ^ 31 := by
    have hg := event_thread_lt hX he
    have hCta : g/l.block < l.grid := NamedBar.cta_lt hg
    have hGrid := hp.grid.2.2
    omega
  have hSet : Seg kernel [] l g 2 1791 root 1793 frame := by
    intro v hv
    dsimp [root,laterDrainRoots,drainRootFrame,frame] at hv ⊢
    have hCta : g/l.block < 2 ^ 32 := by omega
    have hSum : g/l.block+1 < 2 ^ 32 := by omega
    have hOne : truncBits 32 (BitVec.ofInt 64 1) = BitVec.ofNat 64 1 := rfl
    have hZero : truncBits 32 (BitVec.ofInt 64 0) = 0#64 := rfl
    seg_fp hv using simp only [b32,hOne,hZero,← BitVec.ofNat_add,
      truncBits_ofNat hCta (by decide),truncBits_ofNat hSum (by decide)]
  obtain ⟨v,hLocal,hV⟩ := hSet u hu
  have hLocalA := (loaderLinear (regs := []) (by decide) (by decide) hu.1
    (by simp) (by decide +kernel) hLocal).1
  have hSkip : ((kernel.code.drop 1793).take (1794-1793)).all
      (fun ins => loaderPipelineCutOp 1793 1794 1861 (frame.map Prod.fst) ins.op) = true := by
    change ((kernel.code.drop 1793).take (1794-1793)).all
      (fun ins => loaderPipelineCutOp 1793 1794 1861 [7190,1173,7145,1073,7506,1072]
        ins.op) = true
    decide +kernel
  obtain ⟨w,pos',hPos',hW,hWRun⟩ := observesAfterCut (by decide) (by decide) hSkip
    (fun h hPc => lt_of_lt_of_le (by decide : 1861 < 1862) (drainTailFloor h hPc))
    (by rw [hV.1]; decide) (by decide) ⟨rfl,hV.2⟩
    (huRun.after_local_nonempty (run_rtg hLocalA) (traceAfterObservedEvent he hFirstPos))
    hFirstPos he
  exact ⟨w,pos',ending,hPos',hW,hWRun⟩

private theorem laterDrainExitMissesRead {l : Launch} {X : Execution}
    {g pos j : Nat} {s : TState} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hs : 1848 ≤ s.pc) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o)
    (hj : pos ≤ j) (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) : False := by
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some ⟨1805,.rd a bs⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hj]
    exact he
  obtain ⟨t,_,hPath,hStep⟩ := hr.before_event hIndexed
  have hPc : t.pc = 1805 := (estep_source_pc hStep).symm
  have hLower := laterDrainEndFloor hPath hs
  omega

private theorem laterDrainBackEdge {l : Launch} {X : Execution}
    {g pos j : Nat} {s : TState} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    {F : List (Nat × Value)}
    (hKeep : ∀ r ∈ F.map Prod.fst,
      r ∉ loaderRingWrites (kernel.code[1847]?.getD (⟨none,.exit⟩ : Instr)).op)
    (hs : At s 1847 F) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o)
    (hPos : pos ≤ j) (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) :
    ∃ t, At t 1794 F ∧ Run kernel Assumptions.all l g t ((X.tr g).drop pos) o := by
  have hIndexed : ((X.tr g).drop pos)[j-pos]? = some ⟨1805,.rd a bs⟩ := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨t,_,hPath,hEvent⟩ := hr.before_event hIndexed
  have hEventPc : t.pc = 1805 := (estep_source_pc hEvent).symm
  have hTau : ∃ u, Tau kernel Assumptions.all l g s u := by
    generalize ((X.tr g).drop pos).take (j-pos) = pre at hPath
    cases hPath with
    | refl => have := hs.1; omega
    | tau h _ => exact ⟨_,h⟩
    | event hEvent _ =>
      obtain ⟨ins,hc,hIsLocal,_⟩ := estep_event_source hEvent
      rw [hs.1,Flow.code_1847] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hIsLocal
  obtain ⟨u,hu⟩ := hTau
  have hLower : 174 ≤ s.pc := by rw [hs.1]; decide
  have hUpper : s.pc < 1901 := by rw [hs.1]; decide
  have huCore : Tau kernel [] l g s u := by
    unfold Tau at hu ⊢
    rwa [← loaderOutCore hLower (by omega)]
  have hCode := hs.1.symm ▸ Flow.code_1847
  have hPc : u.pc = 1794 ∨ u.pc = 1848 := by
    rcases tau_core_frame hCode huCore with rfl | hFrame
    · exact .inr (by simp [skip, hs.1])
    · exact .inl (hFrame.pc.resolve_right (by simp [BrxTarget]))
  have hTail := hr.after_local_nonempty (.single hu) (traceAfterObservedEvent he hPos)
  have huPc := hPc.resolve_right fun h => laterDrainExitMissesRead h.ge hTail hPos he
  have hw : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,hu⟩
  have hSub := loaderSubstepAtNewPc hLower hUpper (ringShapeOfAt hs) hw (by
    rw [hs.1,huPc]
    decide)
  have hShape := loaderPipelineStepShape hLower hUpper (ringShapeOfAt hs) hw
  have hRegs := holdsSchedulerFrame hs.2.2.2.2
    (fun r hr => loaderPipelineStepRegs hLower hUpper (fun ins hc => by
      have hi := Option.some.inj (hCode.symm.trans hc)
      subst ins
      simpa only [Flow.code_1847,Option.getD_some] using hKeep r hr) hw)
    (fun _ h => List.mem_map_of_mem h)
  have hFault : u.fault = none := by
    cases hf : u.fault with
    | none => rfl
    | some f => cases hTail.eventOfFault hf hIndexed
  exact ⟨u,⟨huPc,hSub,hShape.2 hSub,hFault,hRegs⟩,hTail⟩

private noncomputable def laterDrainFrame (p : Params) (l : Launch) (g first : Nat) :
    List (Nat × Value) :=
  (7190,b32 first)::(1173,b32 (g/l.block+1))::laterDrainRoots p l g

private theorem laterGroupAtBranch (hp : Pre p l m) {g first : Nat} (hf : first ≤ p.batch)
    {s : TState} (hs : At s 1794 (laterDrainFrame p l g first)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch ≤ first+31 then 1845 else 1799)
        ((1174,b32 (first+31))::(7191,b32 (g/l.block+1))::
          laterDrainFrame p l g (min (first+31) p.batch)) := by
  let carry := (1173,b32 (g/l.block+1))::laterDrainRoots p l g
  have hInputs : At s 1794 [(7190,b32 first),(7145,b32 p.batch),(1173,b32 (g/l.block+1))] :=
    hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.2.1,hs.2.2.2.2.2.1,trivial⟩
  obtain ⟨v,hGroup,hV⟩ := laterDrainGroup hp hf s hInputs
  have hKeep : ((kernel.code.drop 1794).take 4).all
      (fun ins => (carry.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    change ((kernel.code.drop 1794).take 4).all
      (fun ins => ([1173,7145,1073,7506,1072] : List Nat).all
        (fun r => !(writesRegs ins.op).contains r)) = true
    decide +kernel
  obtain ⟨hvRun,hFrame⟩ := loaderLinear (by decide) (by decide) hs.1 hKeep
    (by decide +kernel) hGroup
  have hCarry := holdsSchedulerFrame hs.2.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  let out := (1174,b32 (first+31))::(7191,b32 (g/l.block+1))::
    laterDrainFrame p l g (min (first+31) p.batch)
  have hBefore : At v 1798 ((241,.pred (decide (p.batch ≤ first+31)))::out) :=
    hV.mono ⟨hV.2.2.2.2.2.1,hV.2.2.2.2.1,hV.2.2.2.2.2.2.2.1,hV.2.2.2.2.2.2.1,hCarry⟩
  obtain ⟨u,hBranch,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1798 _ hBefore hBefore.2.2.2.2.1 (by simp)
  have hTau := (loaderLinear (regs := []) (by decide) (by decide) hBefore.1
    (by simp) (by decide) hBranch).1
  exact ⟨u,(run_rtg hvRun).trans (run_rtg hTau),
    by simpa only [decide_eq_true_eq] using hU.mono hU.2.2.2.2.2⟩

private theorem laterGroupExhausted (hp : Pre p l m) {g first : Nat} (hg : g < l.threads)
    {s : TState}
    (hs : At s 1845
      ((1174,b32 (first+31))::(7191,b32 (g/l.block+1))::laterDrainFrame p l g p.batch)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧ t.pc = 1848 := by
  let cta := g/l.block
  have hCta : cta < l.grid := NamedBar.cta_lt hg
  have hGrid := hp.grid.2.2
  have hAt : At s 1845 [(7191,b32 (cta+1)),(1072,b32 cta)] :=
    hs.mono ⟨hs.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.2.1,trivial⟩
  have hStop : Seg kernel [] l g 2 1845 [(7191,b32 (cta+1)),(1072,b32 cta)] 1847
      [(254,.pred false)] := by
    intro t ht
    have hLess : cta < 2 ^ 32 := by omega
    have hSum : cta+1 < 2 ^ 32 := by omega
    have hCta31 : cta < 2 ^ 31 := by omega
    have hSum31 : cta+1 < 2 ^ 31 := by omega
    seg_fp ht using simp only [truncBits_ofNat hLess (by decide),
      truncBits_ofNat hSum (by decide),compare,Option.getD_some,
      drainSigned hCta31,drainSigned hSum31,Int.ofNat_le,Nat.add_one_le_iff,
      Nat.lt_irrefl,decide_false]
  obtain ⟨t,hLocal,hT⟩ := hStop s hAt
  obtain ⟨u,hBranch,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1847 false hT hT.2.2.2.2.1 (by simp)
  have hv := (loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by simp) (by decide +kernel) hLocal).1
  have hu := (loaderLinear (regs := []) (by decide) (by decide) hT.1
    (by simp) (by decide) hBranch).1
  exact ⟨u,(run_rtg hv).trans (run_rtg hu),hU.1⟩

private theorem laterGroupAtRead (hp : Pre p l m) {g first : Nat} (hf : first < p.batch)
    {s : TState} (hs : At s 1799 ((1174,b32 first)::laterDrainFrame p l g first)) :
    let index := first+laneOf l g
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u (if p.batch < index then 1806 else 1803)
        ((1175,b32 index)::laterDrainFrame p l g first) := by
  let F := laterDrainFrame p l g first
  have hAt : At s 1799 [(1174,b32 first),(1073,b32 (laneOf l g)),(7145,b32 p.batch)] :=
    hs.mono ⟨hs.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨v,hGate,hV⟩ := laterDrainLaneGate hp hf s hAt
  have hKeep : ((kernel.code.drop 1799).take 3).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    change ((kernel.code.drop 1799).take 3).all
      (fun ins => ([7190,1173,7145,1073,7506,1072] : List Nat).all
        (fun r => !(writesRegs ins.op).contains r)) = true
    decide +kernel
  obtain ⟨hLocal,hPreserved⟩ := loaderLinear (by decide) (by decide) hAt.1 hKeep
    (by decide +kernel) hGate
  have hF := holdsSchedulerFrame hs.2.2.2.2.2 hPreserved (fun _ hm => List.mem_map_of_mem hm)
  have hGateAt : At v 1802 ((242,.pred (decide (p.batch < first+laneOf l g)))::
      (1175,b32 (first+laneOf l g))::F) := hV.mono ⟨hV.2.2.2.2.2.1,hV.2.2.2.2.1,hF⟩
  obtain ⟨u,hBranch,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1802 _ hGateAt hGateAt.2.2.2.2.1 (by simp)
  have hBranchA := (loaderLinear (regs := []) (by decide) (by decide) hGateAt.1
    (by simp) (by decide) hBranch).1
  exact ⟨u,(run_rtg hLocal).trans (run_rtg hBranchA),
    by simpa only [decide_eq_true_eq] using hU.mono hU.2.2.2.2.2⟩

private theorem laterGroupReadOrPass {X : Execution} (hp : Pre p l m) {g j pos first : Nat}
    (hf : first < p.batch) {s : TState} {o : Option TState} {a : Acc} {bs : List (Option Byte)}
    (hs : At s 1799 ((1174,b32 first)::laterDrainFrame p l g first))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o) (hj : pos ≤ j)
    (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) :
    (∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4}) ∨
      ∃ t i, i ≤ j ∧ At t 1806 (laterDrainFrame p l g first) ∧
        Run kernel Assumptions.all l g t ((X.tr g).drop i) o := by
  let index := first+laneOf l g
  let F := laterDrainFrame p l g first
  obtain ⟨u,hLocal,hu⟩ := laterGroupAtRead hp hf hs
  have hMore := traceAfterObservedEvent he hj
  have hU := hr.after_local_nonempty hLocal hMore
  by_cases hIndex : index ≤ p.batch
  · change first+laneOf l g ≤ p.batch at hIndex
    have huPc : u.pc = 1803 := by simpa only [ite_eq_right (Nat.not_lt_of_ge hIndex)] using hu.1
    have hAt : At u 1803 [(1175,b32 index),(7506,b64 p.cuQBase)] :=
      ⟨huPc,hu.2.1,hu.2.2.1,hu.2.2.2.1,
        hu.2.2.2.2.1,hu.2.2.2.2.2.2.2.2.2.1,trivial⟩
    obtain ⟨v,hMove,hv⟩ := laterDrainAddress (g := g) hp hIndex u hAt
    have hKeep : ((kernel.code.drop 1803).take 2).all
        (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
      change ((kernel.code.drop 1803).take 2).all
        (fun ins => ([7190,1173,7145,1073,7506,1072] : List Nat).all
          (fun r => !(writesRegs ins.op).contains r)) = true
      decide +kernel
    obtain ⟨hvRun,hPreserve⟩ := loaderLinear (by decide) (by decide) hAt.1 hKeep
      (by decide +kernel) hMove
    have hvF := holdsSchedulerFrame hu.2.2.2.2.2 hPreserve
      (fun _ hm => List.mem_map_of_mem hm)
    let acc : Acc := {loc := globalLoc (p.cuQBase+4*index),size := 4}
    have hRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
    change p.cuQBase+4*(p.batch+1) ≤ 2 ^ 64 at hRange
    have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
    have hOut : out kernel Assumptions.all l g v = .ev (.read acc (afterLoad v [7186])) := by
      rw [loaderOutCore (by rw [hv.1]; decide) (by rw [hv.1]; decide)]
      rw [out_event hv.2.2.2.1 (by rw [hv.1]; exact Flow.code_1805) rfl rfl]
      change Out.ev (loadTmpl [] l g v .global false 32 [7186] 7860 0) = _
      exact congrArg Out.ev (loadTmpl_global hv.2.1 hv.2.2.2.2.1 (by omega)
        (by decide) (by omega))
    let hn : Next kernel Assumptions.all l g u v (.read acc (afterLoad v [7186])) :=
      ⟨run_rtg hvRun,hOut⟩
    obtain ⟨e,t,hGet,hFire,hTail⟩ := hn.continuing_at_nonempty
      (by rintro _ ⟨_,_,_,hBad⟩; cases hBad) hU hMore
    obtain ⟨bytes,_,rfl,hRet⟩ := hFire
    obtain rfl := Option.some.inj hRet
    by_cases hPos : pos = j
    · subst j
      have hKind := congrArg Event.kind (Option.some.inj (hGet.symm.trans he))
      exact .inl ⟨index,hIndex,(Kind.rd.inj hKind).1.symm⟩
    · have hAfter : pos+1 ≤ j := by omega
      cases hValue : rebuild 3 bytes with
      | error err =>
        have hFault : (afterLoad v [7186] bytes).fault = some err := by rw [afterLoad,hValue]
        have hIndexed : ((X.tr g).drop (pos+1))[j-(pos+1)]? = some ⟨1805,.rd a bs⟩ := by
          rw [List.getElem?_drop,Nat.add_sub_of_le hAfter]
          exact he
        cases hTail.eventOfFault hFault hIndexed
      | ok value =>
        have hValueAt : At (afterLoad v [7186] bytes) 1806 F := by
          rw [afterLoad_ok hv.2.1 hv.2.2.1 hValue]
          have hAtV : At v 1805 F := hv.mono hvF
          have hSet : At (next (setReg v 7186 value)) 1806 ((7186,value)::F) :=
            hAtV.set (by
              intro pair hm
              have hRegs : pair.1 ∈ [7190,1173,7145,1073,7506,1072] :=
                List.mem_map_of_mem hm
              exact fun he => (by decide : 7186 ∉ [7190,1173,7145,1073,7506,1072])
                (he ▸ hRegs))
          simpa only [next,setReg,hv.2.1,hv.2.2.1] using
            (hSet.mono hSet.2.2.2.2.2 : At (next (setReg v 7186 value)) 1806 F)
        exact .inr ⟨_,_,hAfter,hValueAt,hTail⟩
  · change ¬ first+laneOf l g ≤ p.batch at hIndex
    have huPc : u.pc = 1806 := by
      simpa only [ite_eq_left (Nat.lt_of_not_ge hIndex)] using hu.1
    exact .inr ⟨u,pos,hj,⟨huPc,hu.2.1,hu.2.2.1,hu.2.2.2.1,hu.2.2.2.2.2⟩,hU⟩

private theorem recordedLaterDrainWord {X : Execution} (hp : Pre p l m) {g : Nat}
    (hg : g < l.threads) {j : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g,j) = some ⟨1805,.rd a bs⟩) :
    ∀ fuel first pos, p.batch-first = fuel → first ≤ p.batch →
      ∀ s ending, pos ≤ j → At s 1794 (laterDrainFrame p l g first) →
        Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending →
        ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first pos hFuel hBound s ending hPos hs hr
    obtain ⟨u,hGroup,hU⟩ := laterGroupAtBranch hp hBound hs
    have hRun := hr.after_local_nonempty hGroup (traceAfterObservedEvent he hPos)
    by_cases hClip : p.batch ≤ first+31
    · have hAt : At u 1845 ((1174,b32 (first+31))::
          (7191,b32 (g/l.block+1))::laterDrainFrame p l g p.batch) := by
        simpa only [ite_eq_left hClip,Nat.min_eq_right hClip] using hU
      obtain ⟨v,hExit,hv⟩ := laterGroupExhausted hp hg hAt
      exact (laterDrainExitMissesRead hv.ge
        (hRun.after_local_nonempty hExit (traceAfterObservedEvent he hPos)) hPos he).elim
    have hMore : first+31 < p.batch := Nat.lt_of_not_ge hClip
    let next := first+31
    let F := laterDrainFrame p l g next
    have hFrom : At u 1799 ((1174,b32 next)::(7191,b32 (g/l.block+1))::F) := by
      simpa only [ite_eq_right hClip,Nat.min_eq_left hMore.le,next,F] using hU
    have hAt : At u 1799 ((1174,b32 next)::F) :=
      hFrom.mono ⟨hFrom.2.2.2.2.1,hFrom.2.2.2.2.2.2⟩
    rcases laterGroupReadOrPass hp hMore hAt hRun hPos he with
      hRead | ⟨v,i,hIndex,hV,hVRun⟩
    · exact hRead
    have hCode (branch : Nat) : ((kernel.code.drop 1806).take (1847-1806)).all
        (fun ins => loaderPipelineCutOp 1806 1847 branch (F.map Prod.fst) ins.op) = true := by
      change ((kernel.code.drop 1806).take (1847-1806)).all
        (fun ins => loaderPipelineCutOp 1806 1847 branch [7190,1173,7145,1073,7506,1072]
          ins.op) = true
      set_option maxRecDepth 100000 in kernel_rfl
    have hSafe : ∀ fault, (⟨1805,.rd a bs⟩ : Event).kind ≠ .ub fault := by
      intro f h
      cases h
    rcases prefixProjectionsCutOrEvent (by decide : 174 ≤ 1806 ∧ 1806 ≤ 1847 ∧ 1847 ≤ 1901)
        hCode (fun (_ : Unit) _ => 0) (fun _ _ => false)
        (fun _ => rfl) (by intros; simp) hV hVRun he hIndex hSafe with
      ⟨hBand,_⟩ | ⟨stop,hStop,t,last,hT,hTRun,_⟩
    · have hImpossible : 1806 ≤ 1805 := hBand
      omega
    have hKeep : ∀ r ∈ F.map Prod.fst,
        r ∉ loaderRingWrites (kernel.code[1847]?.getD (⟨none,.exit⟩ : Instr)).op := by
      change ∀ r ∈ [7190,1173,7145,1073,7506,1072],
        r ∉ loaderRingWrites (kernel.code[1847]?.getD (⟨none,.exit⟩ : Instr)).op
      decide +kernel
    obtain ⟨t',hNext,hNextRun⟩ := laterDrainBackEdge hKeep hT hTRun hStop he
    exact ih (p.batch-next) (by dsimp [next]; omega) next stop rfl hMore.le
      t' last hStop hNext hNextRun

/-- An optional lookup in a later group of the loader drain scan. -/
@[no_expose] def LaterDrainCuQRead (X : Execution) (i : EvId) (a : Acc)
    (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨1805,.rd a bytes⟩

/-- All recorded loader drain groups read bounded launch words, even if their trace stops
at the lookup. -/
theorem LaterDrainCuQRead.word {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : DrainCuQProtected p X) {i : EvId}
    {a : Acc} {bytes : List (Option Byte)} (he : LaterDrainCuQRead X i a bytes) :
    ∃ index ≤ p.batch, a = {loc := globalLoc (p.cuQBase+4*index),size := 4} := by
  obtain ⟨g,j⟩ := i
  have hg := event_thread_lt hX (show X.get (g,j) = some ⟨1805,.rd a bytes⟩ from he)
  obtain ⟨s,pos,ending,hPos,hs,hr⟩ := laterDrainStarts hp hX hCuQ he
  exact recordedLaterDrainWord hp hg he p.batch 0 pos (Nat.sub_zero _) (Nat.zero_le _)
    s ending hPos hs hr

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
