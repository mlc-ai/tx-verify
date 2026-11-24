-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainTiles
import Kernels.TmlFa4Fwd.Proof.EpilogueExit
import Kernels.TmlFa4Fwd.Flow.Code.Part041
import Kernels.TmlFa4Fwd.Flow.Code.Part042

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

def drainScanPc (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 2730 else 2673)+3*stage.val
def drainScanDst (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 2661 else 2640)+3*stage.val
def drainScanSrc (later : Bool) (stage : Fin 6) : Nat :=
  if stage.val = 0 then 7212 else if stage.val = 5 then 7213
  else (if later then 2660 else 2639)+3*stage.val
def drainGuardReg (later : Bool) (stage : Fin 5) : Nat :=
  (if later then 432 else 418)-stage.val

def drainScanKeep (later : Bool) (lane : Nat) (F : List (Nat × Value)) : List (Nat × Value) :=
  ((List.finRange 5).reverse.map fun i =>
    (drainGuardReg later i,.pred (drainScanGuard i lane))) ++ F

/-- A terminal MMA scan fold keeps the live operand and all five lane guards. -/
def activeDrainScanFrame (p : Params) (l : Launch) (g first : Nat) (later : Bool) (stage : Fin 6)
    (F : List (Nat × Value)) : List (Nat × Value) :=
  (drainScanSrc later stage,
    b32 (prefixWindow (groupLaneTiles p first) (2^stage.val) (laneOf l g))) ::
    drainScanKeep later (laneOf l g) F

private theorem drainScanCode : ∀ (later : Bool) (stage : Fin 5),
    kernel.code[drainScanPc later stage]? = some ⟨none,.warp
      {kind := .shfl .up,ty := some (.int .b 32),dsts := [some (drainScanDst later stage)],
        srcs := [.reg (drainScanSrc later stage.castSucc),.imm ((2^stage.val : Nat) : Int),.imm 0],
        mask := some (.imm (-1))}⟩ := by
  intro later stage
  cases later <;> fin_cases stage <;> kernel_rfl

private theorem drainScanTemplate {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (later : Bool) (stage : Fin 5) {t : TState} {word : Nat}
    (hPc : t.pc = drainScanPc later stage) (hFault : t.fault = none)
    (hWord : t.regs (drainScanSrc later stage.castSucc) = some (b32 word)) :
    out kernel Assumptions.all l g t = .ev (.shfl .up (b32 word) (2^stage.val) 0
      (fun v _ => next (setReg t (drainScanDst later stage) v))) := by
  have hWidth : 2^stage.val < 32 := Nat.pow_lt_pow_right (by decide) stage.isLt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hCore := out_eq_core (l := l) (g := g) (t := t)
    (by rw [hPc]; cases later <;> fin_cases stage <;> decide)
    (by rw [hPc]; cases later <;> fin_cases stage <;> decide)
  rw [hCore,out_event hFault (hPc.symm ▸ drainScanCode later stage) rfl rfl]
  change Out.ev (shflTmpl l g t .up (drainScanDst later stage) none
    (.reg (drainScanSrc later stage.castSucc))
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

private theorem combineScan (later : Bool) (stage : Fin 5) (l : Launch) (g : Nat)
    {lane left recv : Nat}
    (hsum : left+recv < 2^32) :
    Seg kernel [] l g 2 (drainScanPc later stage+1)
      [(drainGuardReg later stage,.pred (drainScanGuard stage lane)),
        (drainScanSrc later stage.castSucc,b32 left),(drainScanDst later stage,b32 recv)]
      (drainScanPc later stage+3)
      [(drainScanSrc later stage.succ,b32 (left + if 2^stage.val ≤ lane then recv else 0))] := by
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
    (hSafe : ∀ x ∈ F, x.1 ∉ [drainScanDst later stage+1,drainScanSrc later stage.succ])
    (hl : laneOf l g < 32) {t : TState}
    (ht : At t (drainScanPc later stage+1)
      ((drainScanDst later stage,b32 (prefixWindow (groupLaneTiles p first) (2^stage.val)
        (shflSource .up (laneOf l g) (2^stage.val) 0).1))::
        activeDrainScanFrame p l g first later stage.castSucc F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      At u (drainScanPc later stage+3) (activeDrainScanFrame p l g first later stage.succ F) := by
  let lane := laneOf l g
  let xs := groupLaneTiles p first
  let width := 2^stage.val
  let src := (shflSource .up lane width 0).1
  let R := (drainScanKeep later lane F).map Prod.fst
  have hSrc : src < 32 := Step.shflSource_lt .up hl width 0
  have hSum : prefixWindow xs width lane + prefixWindow xs width src < 2^32 := by
    have hLeft : prefixWindow xs width lane < 2^31 :=
      hp.groupWindow_signed hFirst hl width
    have hRight : prefixWindow xs width src < 2^31 :=
      hp.groupWindow_signed hFirst hSrc width
    omega
  have hGuard : (drainGuardReg later stage,.pred (drainScanGuard stage lane)) ∈
      drainScanKeep later lane F := by
    exact List.mem_append_left _ (List.mem_map_of_mem (by simp))
  have hInput : At t (drainScanPc later stage+1)
      [(drainGuardReg later stage,.pred (drainScanGuard stage lane)),
        (drainScanSrc later stage.castSucc,b32 (prefixWindow xs width lane)),
        (drainScanDst later stage,b32 (prefixWindow xs width src))] :=
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
  have hLayout : ((kernel.code.drop (drainScanPc later stage+1)).take 2).map
      (fun i => writesRegs i.op) =
        [[drainScanDst later stage+1],[drainScanSrc later stage.succ]] := by
    cases later <;> fin_cases stage <;> decide +kernel
  have hRegs : ((kernel.code.drop (drainScanPc later stage+1)).take 2).all
      (fun ins => R.all (fun r => !(writesRegs ins.op).contains r)) = true := by
    change ((kernel.code.drop (drainScanPc later stage+1)).take 2).all
      ((fun dsts : List Nat => R.all (fun r => !dsts.contains r)) ∘
        fun ins : Instr => writesRegs ins.op) = true
    rw [← List.all_map,hLayout]
    simp only [List.all_cons,List.all_nil,Bool.and_true,Bool.and_eq_true,List.all_eq_true]
    have hKeep (r : Nat) (hr : r ∈ R) :
        r ∉ [drainScanDst later stage+1,drainScanSrc later stage.succ] := by
      obtain ⟨item,hm,rfl⟩ := List.mem_map.mp hr
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
        change drainGuardReg later i ∉ [drainScanDst later stage+1,drainScanSrc later stage.succ]
        cases later <;> fin_cases stage <;> fin_cases i <;> decide
      · exact hSafe item hm
    constructor
    · intro r hr
      simpa using fun h => hKeep r hr (List.mem_cons.mpr (.inl h))
    · intro r hr
      simpa using fun h => hKeep r hr (List.mem_cons.mpr (.inr (List.mem_singleton.mpr h)))
  have hStraight : ((kernel.code.drop (drainScanPc later stage+1)).take 1).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    cases later <;> fin_cases stage <;> decide +kernel
  have hPath := run_rtg (localRun (pc := drainScanPc later stage+1) (n := 2)
    (by cases later <;> fin_cases stage <;> decide)
    (by cases later <;> fin_cases stage <;> decide) ht.1 hStraight hRun)
  have hFrame (r : Nat) (hr : r ∈ R) : u.regs r = t.regs r :=
    schedulerLocalFrame (lo := drainScanPc later stage+1) (len := 2)
      hRegs hStraight hRun ht.1.ge (by rw [ht.1]) hr
  have hKeep := holdsSchedulerFrame ht.2.2.2.2.2.2 hFrame (fun _ h =>
    List.mem_map_of_mem h)
  exact ⟨u,hPath,hu.mono ⟨by rw [← hMerge]; exact hu.2.2.2.2.1,hKeep⟩⟩

/-- The same fold walks either of the terminal scheduler's two decoded scan windows. -/
private theorem consumeDrainScan {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (later : Bool) (stage : Fin 5)
    (hSafe : ∀ lane < 32, ∀ x ∈ F lane,
      x.1 ∉ [drainScanDst later stage,drainScanDst later stage+1,drainScanSrc later stage.succ])
    (cur : SchedulerWarpReached l X g (drainScanPc later stage)
      (fun lane => activeDrainScanFrame p l (warpLane l g lane) first later stage.castSucc
        (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc later stage+3)
      (fun lane => activeDrainScanFrame p l (warpLane l g lane) first later stage.succ
        (F lane)) (shuffles+1) votes ends) := by
  let width := 2^stage.val
  let input (lane : Nat) := b32 (prefixWindow (groupLaneTiles p first) width
    (laneOf l (warpLane l g lane)))
  obtain ⟨mid⟩ := cur.consumeShuffle hp hMax hg .up input (fun _ => width) (fun _ => 0) (by
    intro lane hl pair hm
    rcases List.mem_cons.mp hm with rfl | ht
    · change drainScanSrc later stage.castSucc ≠ drainScanDst later stage
      cases later <;> fin_cases stage <;> decide
    · rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
        change drainGuardReg later i ≠ drainScanDst later stage
        cases later <;> fin_cases stage <;> fin_cases i <;> decide
      · exact fun h => hSafe lane hl pair ht (h ▸ List.mem_cons_self))
    (fun lane hl => drainScanTemplate hp _ later stage (cur.checkpoint lane hl).1
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
theorem activeDrainUpScanOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g first shuffles votes : Nat} (hg : g < l.threads) (hFirst : first ≤ p.batch)
    (later : Bool) {ends : Nat → Option TState} {F : Nat → List (Nat × Value)}
    (hSafe : ∀ lane < 32, ∀ x ∈ F lane, ∀ stage,
      x.1 ∉ [drainScanDst later stage,drainScanDst later stage+1,drainScanSrc later stage.succ])
    (cur : SchedulerWarpReached l X g (drainScanPc later 0)
      (fun lane => activeDrainScanFrame p l (warpLane l g lane) first later 0
        (F lane)) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g (drainScanPc later 4+3)
      (fun lane => let t := warpLane l g lane
        (7213,b32 (prefixWindow (groupLaneTiles p first) 32 (laneOf l t)))::F lane)
      (shuffles+5) votes ends) := by
  have go s lane hl x hx := hSafe lane hl x hx s
  obtain ⟨s1⟩ := consumeDrainScan hp hMax hg hFirst later 0 (go 0) cur
  obtain ⟨s2⟩ := consumeDrainScan hp hMax hg hFirst later 1 (go 1) s1
  obtain ⟨s3⟩ := consumeDrainScan hp hMax hg hFirst later 2 (go 2) s2
  obtain ⟨s4⟩ := consumeDrainScan hp hMax hg hFirst later 3 (go 3) s3
  obtain ⟨s5⟩ := consumeDrainScan hp hMax hg hFirst later 4 (go 4) s4
  apply s5.advanceLocal
  intro lane hl
  have h := s5.checkpoint lane hl
  exact ⟨_,.refl,h.mono ⟨h.2.2.2.2.1,((holds_append ..).mp h.2.2.2.2.2).2⟩⟩

end PTX.Kernels.TmlFa4Fwd.Mma
