-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainSecondShuffle
import Kernels.TmlFa4Fwd.Proof.EpilogueExit
import Kernels.TmlFa4Fwd.Flow.Code.Part119
import Kernels.TmlFa4Fwd.Flow.Code.Part120

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

def scanPc (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 7700 else 7642)+3*stage.val
def scanDst (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 5843 else 5822)+3*stage.val
def scanSrc (later : Bool) (stage : Fin 6) : Nat :=
  if stage.val = 0 then 7262 else if stage.val = 5 then 7263
  else (if later then 5842 else 5821)+3*stage.val
def scanGuard (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 675 else 661)-stage.val

def scanKeep (later : Bool) (lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  ((List.finRange 5).reverse.map fun i => (scanGuard later i,.pred (drainScanGuard i lane))) ++ F

/-- A softmax terminal rescan fold keeps the live operand and all five lane guards. -/
def terminalScanFrame (p : Params) (l : Launch) (g first : Nat) (later : Bool) (stage : Fin 6)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  (scanSrc later stage,b32 (prefixWindow (groupLaneTiles p first) (2^stage.val) (laneOf l g))) ::
    scanKeep later (laneOf l g) F

private theorem scanCode (later : Bool) (stage : Fin 5) :
    kernel.code[scanPc later stage]? = some ⟨none,.warp
      {kind := .shfl .up,ty := some (.int .b 32),dsts := [some (scanDst later stage)],
        srcs := [.reg (scanSrc later stage.castSucc),.imm ((2^stage.val : Nat) : Int),.imm 0],
        mask := some (.imm (-1))}⟩ := by
  cases later <;> fin_cases stage
  · exact Flow.code_7642
  · exact Flow.code_7645
  · exact Flow.code_7648
  · exact Flow.code_7651
  · exact Flow.code_7654
  · exact Flow.code_7700
  · exact Flow.code_7703
  · exact Flow.code_7706
  · exact Flow.code_7709
  · exact Flow.code_7712

private theorem scanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (later : Bool) (stage : Fin 5) {t : TState} {word : Nat}
    (hPc : t.pc = scanPc later stage) (hFault : t.fault = none)
    (hWord : t.regs (scanSrc later stage.castSucc) = some (b32 word)) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 word) (2^stage.val) 0
      (fun v _ => next (setReg t (scanDst later stage) v))) := by
  have hWidth : 2^stage.val < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCore := RowDrainRole.softmax.drainCore (l := l) (g := g) (s := t)
    (by rw [hPc]; cases later <;> fin_cases stage <;> decide)
    (by rw [hPc]; cases later <;> fin_cases stage <;> decide)
  rw [hCore,out_event hFault (hPc.symm ▸ scanCode later stage) rfl rfl]
  change Out.ev (shflTmpl l g t .up (scanDst later stage) none (.reg (scanSrc later stage.castSucc))
    (.imm ((2^stage.val : Nat) : Int)) (.imm 0) (.imm (-1))) = _
  have hBits : readBits l g t 32 (.imm ((2^stage.val : Nat) : Int)) =
      .ok (BitVec.ofNat 64 (2^stage.val)) := by
    simp only [readBits,BitVec.ofInt_natCast,truncBits_ofNat (show 2^stage.val < 2^32 by omega)
      (by decide),pure,Except.pure]
  have hMask : readBits l g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl
  have hZero : readBits l g t 32 (.imm 0) = .ok 0 := rfl
  simp only [shflTmpl,readValue,readReg,hWord,hBlock,hBits,hMask,hZero,pure,Except.pure,
    toNat_ofNat_lt (show 2^stage.val < 2^64 by omega)]
  rfl

set_option maxHeartbeats 1000000 in
private theorem combineScan (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat}
    (hsum : left+recv < 2^32) :
    Seg kernel [] l g 2 (scanPc later stage+1)
      [(scanGuard later stage,.pred (drainScanGuard stage lane)),
        (scanSrc later stage.castSucc,b32 left),(scanDst later stage,b32 recv)]
      (scanPc later stage+3)
      [(scanSrc later stage.succ,b32 (left + if 2^stage.val ≤ lane then recv else 0))] := by
  by_cases h : 2^stage.val ≤ lane
  · have hPred : drainScanGuard stage lane = decide (stage.val ≠ 0) := by
      by_cases hz : stage.val = 0
      · rw [hz,Nat.pow_zero] at h
        simp [drainScanGuard,hz,show lane ≠ 0 by omega]
      · simp [drainScanGuard,hz,h]
    cases later <;> fin_cases stage <;> intro t ht <;> simp only [hPred] at ht <;>
      seg_fp ht using norm_bits [ite_eq_left h]
  · have hPred : drainScanGuard stage lane = decide (stage.val = 0) := by
      by_cases hz : stage.val = 0
      · rw [hz,Nat.pow_zero] at h
        simp [drainScanGuard,hz,show lane = 0 by omega]
      · simp [drainScanGuard,hz,h]
    cases later <;> fin_cases stage <;> intro t ht <;> simp only [hPred] at ht <;>
      seg_fp ht using norm_bits [ite_eq_right h]

private theorem foldScan {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (later : Bool) (stage : Fin 5) {g first : Nat} (hFirst : first ≤ p.batch)
    {F : List (Nat × Value)}
    (hSafe : ∀ x ∈ F, x.1 ∉ [scanDst later stage+1,scanSrc later stage.succ])
    (hl : laneOf l g < 32) {t : TState}
    (ht : At t (scanPc later stage+1)
      ((scanDst later stage,b32 (prefixWindow (groupLaneTiles p first) (2^stage.val)
        (shflSource .up (laneOf l g) (2^stage.val) 0).1))::
        terminalScanFrame p l g first later stage.castSucc F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (scanPc later stage+3) (terminalScanFrame p l g first later stage.succ F) := by
  let lane := laneOf l g
  let xs := groupLaneTiles p first
  let width := 2^stage.val
  let src := (shflSource .up lane width 0).1
  let R := (scanKeep later lane F).map Prod.fst
  have hSrc : src < 32 := Step.shflSource_lt .up hl width 0
  have hSum : prefixWindow xs width lane + prefixWindow xs width src < 2^32 := by
    have hLeft : prefixWindow xs width lane < 2^31 :=
      hp.groupWindow_signed hFirst hl width
    have hRight : prefixWindow xs width src < 2^31 :=
      hp.groupWindow_signed hFirst hSrc width
    omega
  have hGuard : (scanGuard later stage,.pred (drainScanGuard stage lane)) ∈
      scanKeep later lane F := by
    exact List.mem_append_left _ (List.mem_map_of_mem (by simp))
  have hInput : At t (scanPc later stage+1)
      [(scanGuard later stage,.pred (drainScanGuard stage lane)),
        (scanSrc later stage.castSucc,b32 (prefixWindow xs width lane)),
        (scanDst later stage,b32 (prefixWindow xs width src))] :=
    ht.mono ⟨holds_mem ht.2.2.2.2 (.tail _ (.tail _ hGuard)),ht.2.2.2.2.2.1,
      ht.2.2.2.2.1,trivial⟩
  obtain ⟨u,hRun,hu⟩ := (combineScan later stage l g hSum).apply hInput
  have hWidth : width < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hMerge : prefixWindow xs width lane + (if width ≤ lane then prefixWindow xs width src else 0)
      = prefixWindow xs (2^stage.succ.val) lane := by
    rw [show 2^stage.succ.val = 2*width by simp [width,Nat.pow_succ,Nat.mul_comm],
      prefixWindow_double]
    dsimp only [src]
    rw [shflSource_up hWidth]
    by_cases h : width ≤ lane <;> simp [h]
  have hCode :
      ∃ a b : Instr, kernel.code[scanPc later stage+1]? = some a ∧
        kernel.code[scanPc later stage+2]? = some b ∧
        writesRegs a.op = [scanDst later stage+1] ∧
        writesRegs b.op = [scanSrc later stage.succ] ∧
        schedulerFallsThrough a.op = true := by
    cases later <;> fin_cases stage
    · exact ⟨_,_,Flow.code_7643,Flow.code_7644,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7646,Flow.code_7647,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7649,Flow.code_7650,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7652,Flow.code_7653,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7655,Flow.code_7656,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7701,Flow.code_7702,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7704,Flow.code_7705,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7707,Flow.code_7708,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7710,Flow.code_7711,rfl,rfl,rfl⟩
    · exact ⟨_,_,Flow.code_7713,Flow.code_7714,rfl,rfl,rfl⟩
  obtain ⟨a,b,ha,hb,hA,hB,hFall⟩ := hCode
  have hSlice : (kernel.code.drop (scanPc later stage+1)).take 2 = [a,b] := by
    have hL := List.getElem?_eq_some_iff.mp ha
    rw [List.drop_eq_getElem_cons hL.1,hL.2,List.take_succ_cons,List.take_one,List.head?_drop]
    rw [hb]
    rfl
  have hRegs : ((kernel.code.drop (scanPc later stage+1)).take 2).all
      (fun ins => R.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    rw [hSlice]
    simp only [List.all_cons,List.all_nil,Bool.and_true,hA,hB,Bool.and_eq_true,List.all_eq_true]
    have hKeep (r : Nat) (hr : r ∈ R) :
        r ∉ [scanDst later stage+1,scanSrc later stage.succ] := by
      obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
        change scanGuard later i ∉ [scanDst later stage+1,scanSrc later stage.succ]
        cases later <;> fin_cases stage <;> fin_cases i <;> decide
      · exact hSafe item hm
    constructor
    · intro r hr
      simpa using fun h => hKeep r hr (List.mem_cons.mpr (.inl h))
    · intro r hr
      simpa using fun h => hKeep r hr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr h)))
  have hStraight : ((kernel.code.drop (scanPc later stage+1)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    simp only [List.take_one,List.head?_drop,ha,Option.toList_some,List.all_cons,List.all_nil,
      Bool.and_true,hFall]
  have hPath := RowDrainRole.softmax.drainLocals (lo := scanPc later stage+1) (n := 2)
    (by cases later <;> fin_cases stage <;> decide)
    (by cases later <;> fin_cases stage <;> decide) ht.1 hStraight hRun
  have hFrame (r : Nat) (hr : r ∈ R) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := scanPc later stage+1) (len := 2)
      hRegs hStraight hRun ht.1.ge (by rw [ht.1]) hr
  have hKeep := holdsSchedulerFrame ht.2.2.2.2.2.2 hFrame (fun _ h =>
    List.mem_map_of_mem h)
  exact ⟨u,hPath,hu.mono ⟨by rw [← hMerge]; exact hu.2.2.2.2.1,hKeep⟩⟩

/-- The same fold walks either of the terminal scheduler's two decoded scan windows. -/
private theorem consumeScan {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (later : Bool) (stage : Fin 5)
    (hSafe : ∀ lane < 32, ∀ x ∈ F lane,
      x.1 ∉ [scanDst later stage,scanDst later stage+1,scanSrc later stage.succ])
    (cur : SchedulerWarpReached l X g (scanPc later stage)
      (fun lane => terminalScanFrame p l (warpLane l g lane) first later stage.castSucc
        (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (scanPc later stage+3)
      (fun lane => terminalScanFrame p l (warpLane l g lane) first later stage.succ
        (F lane)) (shuffles+1) votes ends) := by
  let width := 2^stage.val
  let input (lane : Nat) := b32 (prefixWindow (groupLaneTiles p first) width
    (laneOf l (warpLane l g lane)))
  obtain ⟨mid⟩ := cur.consumeShuffle hp hMax hg .up input (fun _ => width) (fun _ => 0) (by
    intro lane hl pair hm
    rcases List.mem_cons.mp hm with rfl | ht
    · change scanSrc later stage.castSucc ≠ scanDst later stage
      cases later <;> fin_cases stage <;> decide
    · rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
        change scanGuard later i ≠ scanDst later stage
        cases later <;> fin_cases stage <;> fin_cases i <;> decide
      · exact fun h => hSafe lane hl pair ht (h ▸ List.mem_cons_self))
    (fun lane hl => scanTemplate hp _ later stage (cur.checkpoint lane hl).1
      (cur.checkpoint lane hl).2.2.2.1 (cur.checkpoint lane hl).2.2.2.2.1)
  apply mid.advanceLocal
  intro lane hl
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
  have hSrc : laneOf l (warpLane l g (shflSource .up lane width 0).1) =
      (shflSource .up lane width 0).1 :=
    (Step.sameWarp_lane hBlock hg (Step.shflSource_lt .up hl width 0)).2
  apply foldScan hp later stage hFirst (F := F lane)
    (fun x hx hm => hSafe lane hl x hx (List.mem_cons_of_mem _ hm)) (Nat.mod_lt _ (by decide))
  have hh := mid.checkpoint lane hl
  simp only [input,hSrc] at hh
  rw [hLane]
  exact hh

/-- The decoded first or later terminal scan folds five consecutive warp prefixes. -/
theorem warpTerminalUpScanOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (later : Bool) {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (hSafe : ∀ lane < 32, ∀ x ∈ F lane, ∀ stage,
      x.1 ∉ [scanDst later stage,scanDst later stage+1,scanSrc later stage.succ])
    (cur : SchedulerWarpReached l X g (scanPc later 0)
      (fun lane => terminalScanFrame p l (warpLane l g lane) first later 0
        (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (scanPc later 4+3)
      (fun lane => let t := warpLane l g lane
        (7263,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::F lane)
      (shuffles+5) votes ends) := by
  have go s lane hl x hx := hSafe lane hl x hx s
  obtain ⟨s1⟩ := consumeScan hp hMax hg hFirst later 0 (go 0) cur
  obtain ⟨s2⟩ := consumeScan hp hMax hg hFirst later 1 (go 1) s1
  obtain ⟨s3⟩ := consumeScan hp hMax hg hFirst later 2 (go 2) s2
  obtain ⟨s4⟩ := consumeScan hp hMax hg hFirst later 3 (go 3) s3
  obtain ⟨s5⟩ := consumeScan hp hMax hg hFirst later 4 (go 4) s4
  apply s5.advanceLocal
  intro lane hl
  have h := s5.checkpoint lane hl
  exact ⟨_,.refl,h.mono ⟨h.2.2.2.2.1,((holds_append ..).mp h.2.2.2.2.2).2⟩⟩

/-- Replays all five actual terminal up-shuffles and reaches the lane-31 broadcast
with the complete first-group prefix for every lane. -/
theorem terminalDrainFirstUpScanOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7642
      (fun lane => terminalSecondScanFrame p l (warpLane l g lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 7657
      (fun lane => let t := warpLane l g lane
        [(7263,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l t))),(7141,b32 p.heads)] ++
          RowDrainRole.softmax.roots p l t) (shuffles+5) votes ends) := by
  let F := fun lane => let t := warpLane l g lane
    (7141,b32 p.heads)::RowDrainRole.softmax.roots p l t
  have hStart : Nonempty (SchedulerWarpReached l X g 7642
      (fun lane => terminalScanFrame p l (warpLane l g lane) 0 false 0 (F lane))
      shuffles votes ends) := by
    apply cur.advanceLocal
    intro lane hl
    have h := cur.checkpoint lane hl
    refine ⟨_,.refl,h.mono ?_⟩
    have hWord : (cur.state lane).regs 7262 =
        some (b32 (prefixWindow (groupLaneTiles p 0) 1 (laneOf l (warpLane l g lane)))) := by
      simpa only [prefixWindow_one] using h.2.2.2.2.1
    refine ⟨hWord,(holds_append ..).mpr ⟨?_,?_⟩⟩
    · simpa [scanKeep,scanGuard,drainScanGuard,List.finRange_succ,Nat.succ_le_iff] using
        (show Holds (cur.state lane).regs
          [(657,.pred (decide (15 < laneOf l (warpLane l g lane)))),
           (658,.pred (decide (7 < laneOf l (warpLane l g lane)))),
           (659,.pred (decide (3 < laneOf l (warpLane l g lane)))),
           (660,.pred (decide (1 < laneOf l (warpLane l g lane)))),
           (661,.pred (decide (laneOf l (warpLane l g lane) = 0)))] from
          ⟨h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.1,
            h.2.2.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.1,trivial⟩)
    · exact ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2.2.2.2⟩
  obtain ⟨s0⟩ := hStart
  apply warpTerminalUpScanOfMaximal hp hMax hg (Nat.zero_le p.batch) false _ s0
  intro lane _ x hx stage
  simp only [F,RowDrainRole.roots,RowDrainRole.frame,RowDrainRole.batchReg,RowDrainRole.laneReg,
    RowDrainRole.ctaReg,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> fin_cases stage <;> decide

end PTX.Kernels.TmlFa4Fwd.Softmax
