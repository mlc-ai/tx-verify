-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTerminalFirstScan
import Kernels.TmlFa4Fwd.Proof.EpilogueExit
import Kernels.TmlFa4Fwd.Flow.Code.Part142
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

def scanPc (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 9167 else 9110)+3*stage.val
def scanDst (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 7110 else 7089)+3*stage.val
def scanSrc (later : Bool) (stage : Fin 6) : Nat :=
  if stage.val = 0 then 7282 else if stage.val = 5 then 7283
  else (if later then 7109 else 7088)+3*stage.val
def scanGuard (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 766 else 752)-stage.val

def scanKeep (later : Bool) (lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  ((List.finRange 5).reverse.map fun i => (scanGuard later i,.pred (drainScanGuard i lane))) ++ F

/-- A correction terminal rescan fold keeps the live operand and all five lane guards. -/
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
  · exact Flow.code_9110
  · exact Flow.code_9113
  · exact Flow.code_9116
  · exact Flow.code_9119
  · exact Flow.code_9122
  · exact Flow.code_9167
  · exact Flow.code_9170
  · exact Flow.code_9173
  · exact Flow.code_9176
  · exact Flow.code_9179


private theorem scanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (later : Bool) (stage : Fin 5) {t : TState} {word : Nat}
    (hPc : t.pc = scanPc later stage) (hFault : t.fault = none)
    (hWord : t.regs (scanSrc later stage.castSucc) = some (b32 word)) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 word) (2^stage.val) 0
      (fun v _ => next (setReg t (scanDst later stage) v))) := by
  have hWidth : 2^stage.val < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCore := RowDrainRole.correction.drainCore (l := l) (g := g) (s := t)
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

private theorem combineScanWithPrefix (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat}
    (h : 2^stage.val ≤ lane) (hsum : left+recv < 2^32) :
    Seg kernel [] l g 2 (scanPc later stage+1)
      [(scanGuard later stage,.pred (drainScanGuard stage lane)),
        (scanSrc later stage.castSucc,b32 left),(scanDst later stage,b32 recv)]
      (scanPc later stage+3)
      [(scanSrc later stage.succ,b32 (left + if 2^stage.val ≤ lane then recv else 0))] := by
  have hPred : drainScanGuard stage lane = decide (stage.val ≠ 0) := by
    by_cases hz : stage.val = 0
    · rw [hz,Nat.pow_zero] at h
      simp [drainScanGuard,hz,show lane ≠ 0 by omega]
    · simp [drainScanGuard,hz,h]
  cases later <;> fin_cases stage <;> intro t ht <;> simp only [hPred] at ht <;>
    seg_fp ht using norm_bits [ite_eq_left h]

private theorem combineScanWithoutPrefix (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat}
    (h : ¬2^stage.val ≤ lane) (hsum : left+recv < 2^32) :
    Seg kernel [] l g 2 (scanPc later stage+1)
      [(scanGuard later stage,.pred (drainScanGuard stage lane)),
        (scanSrc later stage.castSucc,b32 left),(scanDst later stage,b32 recv)]
      (scanPc later stage+3)
      [(scanSrc later stage.succ,b32 (left + if 2^stage.val ≤ lane then recv else 0))] := by
  have hPred : drainScanGuard stage lane = decide (stage.val = 0) := by
    by_cases hz : stage.val = 0
    · rw [hz,Nat.pow_zero] at h
      simp [drainScanGuard,hz,show lane = 0 by omega]
    · simp [drainScanGuard,hz,h]
  cases later <;> fin_cases stage <;> intro t ht <;> simp only [hPred] at ht <;>
    seg_fp ht using norm_bits [ite_eq_right h]

private theorem combineScan (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat}
    (hsum : left+recv < 2^32) :
    Seg kernel [] l g 2 (scanPc later stage+1)
      [(scanGuard later stage,.pred (drainScanGuard stage lane)),
        (scanSrc later stage.castSucc,b32 left),(scanDst later stage,b32 recv)]
      (scanPc later stage+3)
      [(scanSrc later stage.succ,b32 (left + if 2^stage.val ≤ lane then recv else 0))] := by
  by_cases h : 2^stage.val ≤ lane
  · exact combineScanWithPrefix later stage l g h hsum
  · exact combineScanWithoutPrefix later stage l g h hsum

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
  let writes := [scanDst later stage+1,scanSrc later stage.succ]
  let code := (kernel.code.drop (scanPc later stage+1)).take 2
  have hWriteAudit : code.all (fun i => (writesRegs i.op).all (· ∈ writes)) = true := by
    cases later <;> fin_cases stage <;> decide +kernel
  have hSafeKeep (r : Nat) (hr : r ∈ R) : r ∉ writes := by
    obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
      change scanGuard later i ∉ writes
      cases later <;> fin_cases stage <;> fin_cases i <;> decide
    · exact hSafe item hm
  have hRegs : code.all
      (fun ins => R.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    apply List.all_eq_true.mpr
    intro i hi
    apply List.all_eq_true.mpr
    intro r hr
    cases hw : (writesRegs i.op).contains r
    · rfl
    · exact (hSafeKeep r hr (of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp hWriteAudit i hi) r
          (by simpa using hw)))).elim
  have hStraight : ((kernel.code.drop (scanPc later stage+1)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    cases later <;> fin_cases stage <;> decide +kernel
  have hPath := RowDrainRole.correction.drainLocals (lo := scanPc later stage+1) (n := 2)
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
        (7283,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::F lane)
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

/-- Each terminal window prepares the same five guards from the physical lane. -/
private theorem terminalScanPrepare (later : Bool) (l : Launch) (g lane : Nat)
    (hl : lane < 32) :
    Seg kernel [] l g 5 (scanPc later 0-5) [(1616,b32 lane)]
      (scanPc later 0) (scanKeep later lane []) := by
  have hLane : lane < 2^32 := by omega
  have hLane64 : lane < 2^64 := by omega
  have hz : (↑(truncBits 32 (BitVec.ofInt 64 0)).toNat : Int) = 0 := rfl
  have h1 : (↑(truncBits 32 (BitVec.ofInt 64 1)).toNat : Int) = 1 := rfl
  have h3 : (↑(truncBits 32 (BitVec.ofInt 64 3)).toNat : Int) = 3 := rfl
  have h7 : (↑(truncBits 32 (BitVec.ofInt 64 7)).toNat : Int) = 7 := rfl
  have h15 : (↑(truncBits 32 (BitVec.ofInt 64 15)).toNat : Int) = 15 := rfl
  have hG0 : drainScanGuard 0 lane = decide (lane = 0) := rfl
  have hG1 : drainScanGuard 1 lane = decide (2 ≤ lane) := rfl
  have hG2 : drainScanGuard 2 lane = decide (4 ≤ lane) := rfl
  have hG3 : drainScanGuard 3 lane = decide (8 ≤ lane) := rfl
  have hG4 : drainScanGuard 4 lane = decide (16 ≤ lane) := rfl
  have hShape : ∀ b, scanKeep b lane [] =
      [(scanGuard b 4,.pred (drainScanGuard 4 lane)),
       (scanGuard b 3,.pred (drainScanGuard 3 lane)),
       (scanGuard b 2,.pred (drainScanGuard 2 lane)),
       (scanGuard b 1,.pred (drainScanGuard 1 lane)),
       (scanGuard b 0,.pred (drainScanGuard 0 lane))] := by intro b; cases b <;> rfl
  rw [hShape]
  cases later <;> intro t ht <;> seg_fp ht using
    (simp only [hG0,hG1,hG2,hG3,hG4,compare,Option.getD_some,
      truncBits_ofNat hLane (by decide),toNat_ofNat_lt hLane64,Value.pred.injEq,
      decide_eq_decide,hz,h1,h3,h7,h15]
     all_goals omega)

theorem terminalFirstUpScanOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g n votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 9105
      (fun lane => terminalFirstCountFrame p l (warpLane l g lane)) n votes ends) :
    Nonempty (SchedulerWarpReached l X g 9125
      (fun lane => let thread := warpLane l g lane
        (7283,b32 (prefixWindow (groupLaneTiles p 0) 32 (laneOf l thread))) ::
          terminalFirstCountFrame p l thread) (n+5) votes ends) := by
  let F := fun lane => terminalFirstCountFrame p l (warpLane l g lane)
  have hInput : Nonempty (SchedulerWarpReached l X g 9110
      (fun lane => terminalScanFrame p l (warpLane l g lane) 0 false 0 (F lane)) n votes ends) := by
    apply cur.advanceLocal
    intro lane hl
    let thread := warpLane l g lane
    have ht := cur.checkpoint lane hl
    have hPrep := terminalScanPrepare false l thread (laneOf l thread) (Nat.mod_lt _ (by decide))
    obtain ⟨u,hRun,hAt⟩ := hPrep.apply (ht.mono
      ⟨ht.2.2.2.2.2.2.2.1,trivial⟩)
    have hSaved : Holds u.regs (F lane) := holdsSchedulerFrame ht.2.2.2.2
      (fun r hr => schedulerLocalFrame (lo := 9105) (len := 5)
        (by
          change ((kernel.code.drop 9105).take 5).all
            (fun i => [7143,7282,7153,1616,7506,1618].all
              (fun r => !(writesRegs i.op).contains r)) = true
          decide +kernel)
        (by decide +kernel) hRun ht.1.ge (by rw [ht.1]) hr)
      (fun _ hm => List.mem_map_of_mem hm)
    have hKeep := (holds_append ..).mpr ⟨hAt.2.2.2.2,hSaved⟩
    have hWord : u.regs 7282 = some
        (b32 (prefixWindow (groupLaneTiles p 0) 1 (laneOf l thread))) := by
      rw [prefixWindow_one]
      exact hSaved.2.1
    exact ⟨u,RowDrainRole.correction.drainLocals (by decide) (by decide) ht.1
      (by decide +kernel) hRun,hAt.mono ⟨hWord,hKeep⟩⟩
  obtain ⟨start⟩ := hInput
  apply warpTerminalUpScanOfMaximal hp hMax hg (Nat.zero_le p.batch) false _ start
  intro lane _ x hm stage
  simp only [F,terminalFirstCountFrame,RowDrainRole.roots,RowDrainRole.frame,
    RowDrainRole.batchReg,RowDrainRole.laneReg,RowDrainRole.ctaReg,
    List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;> fin_cases stage <;> decide

end PTX.Kernels.TmlFa4Fwd.Correction
