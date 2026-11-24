-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublish
public import Kernels.TmlFa4Fwd.Proof.SoftmaxReductionLayout
import Kernels.TmlFa4Fwd.Proof.SoftmaxProbability
public import Lemmas.Flow.TraceReach

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

def tailElectLane : Round → Nat
  | .first => 3944
  | .biased => 5115
  | .unbiased => 5798

def tailElectPred : Round → Nat
  | .first => 623
  | .biased => 638
  | .unbiased => 647

private theorem tailWarpBarrierCode (round : Round) :
    kernel.code[probabilityWaitPc round true + 1]? =
      some ⟨none, .warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩⟩ := by
  cases round
  · exact Flow.code_4858
  · exact Flow.code_6543
  · exact Flow.code_7448

private theorem tailElectCode (round : Round) :
    kernel.code[probabilityWaitPc round true + 2]? = some ⟨none,
      .warp ⟨.elect, none, [some (tailElectLane round), some (tailElectPred round)], [],
        some (.imm (-1))⟩⟩ := by
  cases round
  · exact Flow.code_4859
  · exact Flow.code_6544
  · exact Flow.code_7449

private theorem fullMember (l : Launch) (g : Nat) : electMember (2 ^ 32 - 1) (laneOf l g) := by
  have h (lane : Fin 32) : electMember (2 ^ 32 - 1) lane.val := by
    fin_cases lane <;> decide
  exact h ⟨_, Nat.mod_lt _ (by decide)⟩

private theorem fullMaskBits : (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1 := by
  decide

private theorem singletonOfTailGet {X : Execution} {g j : Nat} {e : Event}
    (he : X.get (g,j) = some e) : ((X.tr g).drop j).take 1 = [e] := by
  rw [List.take_one,List.head?_drop]
  change (X.get (g,j)).toList = [e]
  rw [he]
  rfl

variable {p : Params} {l : Launch} {m : Mem0}

/-- Every round's P tail is drained by the store wait, then a full warp rendezvous elects
the lane whose Boolean predicate controls the P-tail notification. -/
theorem tailElectionPath {X : Execution} (hp : Pre p l m) (round : Round) {g j : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t (probabilityWaitPc round true) F)
    (hLaneFresh : ∀ r ∈ F, r.1 ≠ tailElectLane round)
    (hPredFresh : ∀ r ∈ F, r.1 ≠ tailElectPred round)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityWaitPc round true
    ∃ u barInst electInst leader,
      X.get (g, j) = some ⟨pc, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨pc + 1, .warpBar (2 ^ 32 - 1) barInst⟩ ∧
      X.get (g, j + 2) = some ⟨pc + 2, .elect (2 ^ 32 - 1) electInst leader⟩ ∧
      At u (pc + 3) ((tailElectPred round, .pred (laneOf l g == leader)) ::
        (tailElectLane round, b32 leader) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 3)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 3) u := by
  dsimp only
  obtain ⟨hWait, hTail⟩ := probabilityWaitTrace hp round true ht.1 ht.2.2.2.1 hRun
  have hBar : out kernel Assumptions.all l g (next t) =
      .ev (.warpBar (2 ^ 32 - 1) (next (next t))) := by
    rw [out_event ht.next.2.2.2.1 (by rw [ht.next.1]; exact tailWarpBarrierCode round) rfl rfl]
    change Out.ev (warpBarTmpl l g (next t) (.imm (-1))) = _
    simp only [warpBarTmpl, readBits, pure, Except.pure, fullMaskBits, fullMember, ↓reduceIte]
  have hNext : Next kernel Assumptions.all l g (next t) (next t)
      (.warpBar (2 ^ 32 - 1) (next (next t))) := ⟨.refl, hBar⟩
  obtain ⟨e, v, he, ⟨barInst, rfl, hV⟩, hRest⟩ := hNext.continuing_at (by
    rintro _ ⟨_, _, hBad⟩
    cases hBad) hTail
  obtain rfl := Option.some.inj hV
  let s := next (next t)
  let k := fun leader =>
    next (setReg (setReg s (tailElectLane round) (b32 leader)) (tailElectPred round)
      (.pred (laneOf l g == leader)))
  have hs := ht.next.next
  have hElect : out kernel Assumptions.all l g s = .ev (.elect (2 ^ 32 - 1) k) := by
    rw [out_event hs.2.2.2.1 (by rw [hs.1]; exact tailElectCode round) rfl rfl]
    change Out.ev (electTmpl l g s (some (tailElectLane round)) (tailElectPred round)
      (.imm (-1))) = _
    simp only [electTmpl, readBits, pure, Except.pure, fullMaskBits, fullMember, ↓reduceIte]
    rfl
  have hn : Next kernel Assumptions.all l g s s (.elect (2 ^ 32 - 1) k) := ⟨.refl, hElect⟩
  obtain ⟨e, u, hE, ⟨electInst, leader, rfl, hU⟩, hAfter⟩ := hn.continuing_at (by
    rintro _ ⟨_, _, _, hBad⟩
    cases hBad) hRest
  obtain rfl := Option.some.inj hU
  have hDistinct : tailElectLane round ≠ tailElectPred round := by cases round <;> decide
  have hU : At (k leader) (probabilityWaitPc round true + 3)
      ((tailElectPred round, .pred (laneOf l g == leader)) ::
        (tailElectLane round, b32 leader) :: F) := by
    obtain ⟨hpc, hsub, hacc, hf, hF⟩ := hs
    refine ⟨?_, hsub, hacc, hf, Function.update_self .., ?_⟩
    · change s.pc + 1 = probabilityWaitPc round true + 3
      have hh : s.pc = probabilityWaitPc round true + 1 + 1 := hpc
      omega
    · have hFresh : ∀ pair ∈ (tailElectLane round, b32 leader) :: F,
          pair.1 ≠ tailElectPred round := by
        intro pair hPair
        rcases List.mem_cons.mp hPair with rfl | hm
        · exact hDistinct
        · exact hPredFresh _ hm
      exact holds_update ⟨Function.update_self .., holds_update hF hLaneFresh⟩ hFresh
  have hPc : s.pc = probabilityWaitPc round true + 2 := by
    have h := hs.1
    change s.pc = _ at h
    omega
  refine ⟨_, barInst, electInst, leader, hWait, by simpa only [ht.next.1] using he,
    by simpa only [hPc, Nat.add_assoc] using hE, hU,
    by simpa only [Nat.add_assoc] using hAfter,?_⟩
  have wStep : EStep kernel Assumptions.all l g t ⟨t.pc,.tc .waitSt⟩ (some (next t)) :=
    ⟨_,probabilityWaitTemplate hp round true ht.1 ht.2.2.2.1,rfl,rfl⟩
  have bStep : EStep kernel Assumptions.all l g (next t)
      ⟨(next t).pc,.warpBar (2^32-1) barInst⟩ (some s) := ⟨_,hBar,barInst,rfl,rfl⟩
  have eStep : EStep kernel Assumptions.all l g s
      ⟨s.pc,.elect (2^32-1) electInst leader⟩ (some (k leader)) :=
    ⟨_,hElect,electInst,leader,rfl,rfl⟩
  rw [show (3 : Nat) = 1+1+1 from rfl,List.take_add,List.take_add,List.drop_drop,
    List.drop_drop, singletonOfTailGet hWait, singletonOfTailGet he, singletonOfTailGet hE]
  exact .event (ht.1 ▸ wStep) (.event bStep (.event eStep (.refl _)))

def tailPublication : Round → Fin 8
  | .first => 2
  | .biased => 5
  | .unbiased => 7

private def tailSkipPred : Round → Nat
  | .first => 624
  | .biased => 639
  | .unbiased => 648

def tailFrame (l : Launch) (warp : Fin 8) : List (Nat × Value) :=
  [(1062, b32 warp.val), (2535, b32 l.sharedBase)]

/-- FP32 probability words that survive the P-tail control instructions. -/
def exponentLive : List Nat := (List.range 128).map (1231 + ·)

theorem mem_exponentLive {r : Nat} : r ∈ exponentLive ↔ 1231 ≤ r ∧ r < 1359 := by
  simp only [exponentLive, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro hr
    exact ⟨r - 1231, by omega, by omega⟩

/-- Registers read by the first continuation after the softmax denominator is initialized. -/
def firstTransitionRegs : List Nat := [1225, 1226, 1228, 1229, 7256]

/-- The FP32 reduction operands following each decoded P tail. -/
def tailLive : Round → List Nat
  | .first => firstTransitionRegs ++ exponentLive
  | .biased => Repeated.biased.sumLive
  | .unbiased => Repeated.unbiased.sumLive

/-- Use the continuation operands available along this branch. -/
def tailContinuationRegs : Round → List Nat
  | .first => []
  | .biased => Repeated.biased.continuationRegs
  | .unbiased => Repeated.unbiased.continuationRegs

/-- Include the continuation register facts when replay proceeds to the next loop head. -/
def tailLiveWith (round : Round) (keepContinuation : Bool) : List Nat :=
  if keepContinuation then tailLive round ++ tailContinuationRegs round else tailLive round

/-- The optional frame carries the FP32 probability registers into the row sum. -/
def tailCarryWith (l : Launch) (warp : Fin 8) (round : Round)
    (frame : Option (Nat → Value)) (keepContinuation : Bool) : List (Nat × Value) :=
  (1062, b32 warp.val) :: (2535, b32 l.sharedBase) ::
    (match frame with | none => [] | some v => factsFrom (tailLiveWith round keepContinuation) v)

theorem tailCarryWith_member {l : Launch} {warp : Fin 8} {round : Round}
    {frame : Option (Nat → Value)} {keep : Bool} {x : Nat × Value}
    (h : x ∈ tailCarryWith l warp round frame keep) :
    x.1 = 1062 ∨ x.1 = 2535 ∨ x.1 ∈ tailLiveWith round keep := by
  simp only [tailCarryWith, List.mem_cons] at h
  rcases h with rfl | rfl | h
  · exact .inl rfl
  · exact .inr (.inl rfl)
  cases frame with
  | none => cases h
  | some v =>
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact .inr (.inr hr)

/-- The default frame retains the original numerical operands. -/
def tailCarry (l : Launch) (warp : Fin 8) (round : Round)
    (frame : Option (Nat → Value)) : List (Nat × Value) :=
  (1062, b32 warp.val) :: (2535, b32 l.sharedBase) ::
    (match frame with | none => [] | some v => factsFrom (tailLive round) v)

set_option maxRecDepth 100000 in
private theorem tailLiveSafe (round : Round) (keep : Bool) :
    (tailLiveWith round keep).all (fun r =>
      r != tailElectLane round && r != tailElectPred round &&
        r != (signalSite (tailPublication round)).state) = true := by
  cases round <;> cases keep <;> kernel_rfl

private theorem tailLiveDistinct (round : Round) (keep : Bool) {r : Nat}
    (hr : r ∈ tailLiveWith round keep) :
    r ≠ tailElectLane round ∧ r ≠ tailElectPred round ∧
      r ≠ (signalSite (tailPublication round)).state := by
  have h := List.all_eq_true.mp (tailLiveSafe round keep) r hr
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

private theorem tailBranchCode (round : Round) :
    kernel.code[probabilityWaitPc round true + 4]? = some
      ⟨some (tailSkipPred round, false),
        .bra ((signalSite (tailPublication round)).pc + 1) false⟩ :=
  match round with
  | .first => Flow.code_4861
  | .biased => Flow.code_6546
  | .unbiased => Flow.code_7451

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private theorem tailNegate (l : Launch) (g : Nat) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool)
    (chosen : Bool) :
    Seg kernel Assumptions.all l g 1 (probabilityWaitPc round true + 3)
      ((tailElectPred round, .pred chosen) :: tailCarryWith l warp round frame keep)
      (probabilityWaitPc round true + 4)
      ((tailSkipPred round, .pred (!chosen)) :: tailCarryWith l warp round frame keep) := by
  cases round <;> cases frame <;> cases keep <;> intro t ht <;>
    simp only [probabilityWaitPc, tailElectPred, tailSkipPred, tailCarryWith,
      tailLiveWith, tailContinuationRegs, Repeated.continuationRegs,
      Bool.false_eq_true,
      ↓reduceIte] at ht ⊢ <;>
    seg_fp ht using seg_close

private theorem tailBranch {l : Launch} {g : Nat} (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool)
    (chosen : Bool) :
    Seg kernel Assumptions.all l g 1 (probabilityWaitPc round true + 4)
      ((tailSkipPred round, .pred (!chosen)) :: tailCarryWith l warp round frame keep)
      (if chosen then probabilityWaitPc round true + 5
        else (signalSite (tailPublication round)).pc + 1)
      (tailCarryWith l warp round frame keep) := by
  intro t ht
  obtain ⟨u, hu, hU⟩ := run_bra (A := []) (K := kernel) (L := l) (g := g)
    (tailBranchCode round) (!chosen) (ht.mono ht.2.2.2.2.2) ht.2.2.2.2.1 (by simp)
  have hTau : tauStep kernel Assumptions.all l g t = tauStep kernel [] l g t := by
    apply Assumptions.tauStep_all_eq_nil (by rw [ht.1]; cases round <;> decide)
      (by rw [ht.1]; exact tailBranchCode round) rfl
  have hu' : run kernel Assumptions.all l g 1 t = some u :=
    by simpa only [run, hTau] using hu
  exact ⟨u, hu', by cases chosen <;> exact hU⟩

private def tailOffsetReg : Round → Nat
  | .first => 3945
  | .biased => 5116
  | .unbiased => 5799

private def TailStage (l : Launch) (g : Nat) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) : Prop :=
  Seg kernel Assumptions.all l g 3 (probabilityWaitPc round true + 5)
    (tailCarryWith l warp round frame keep)
    (probabilityWaitPc round true + 8)
    ((tailOffsetReg round, b32 (8 * (stageOf warp).val)) :: tailCarryWith l warp round frame keep)

private theorem tailStageFirst (l : Launch) (g : Nat) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) : TailStage l g .first warp frame keep := by
  unfold TailStage
  cases frame <;> cases keep <;> fin_cases warp <;> intro t ht <;>
    simp only [tailCarryWith, tailLiveWith, tailContinuationRegs,
      Bool.false_eq_true,
      ↓reduceIte, probabilityWaitPc, tailOffsetReg] at ht ⊢ <;>
    seg_fp ht using decide

private theorem tailStageBiased (l : Launch) (g : Nat) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) : TailStage l g .biased warp frame keep := by
  unfold TailStage
  cases frame <;> cases keep <;> fin_cases warp <;> intro t ht <;>
    simp only [tailCarryWith, tailLiveWith, tailContinuationRegs, Repeated.continuationRegs,
      Bool.false_eq_true,
      ↓reduceIte, probabilityWaitPc, tailOffsetReg] at ht ⊢ <;>
    seg_fp ht using decide

private theorem tailStageUnbiased (l : Launch) (g : Nat) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) : TailStage l g .unbiased warp frame keep := by
  unfold TailStage
  cases frame <;> cases keep <;> fin_cases warp <;> intro t ht <;>
    simp only [tailCarryWith, tailLiveWith, tailContinuationRegs, Repeated.continuationRegs,
      Bool.false_eq_true,
      ↓reduceIte, probabilityWaitPc, tailOffsetReg] at ht ⊢ <;>
    seg_fp ht using decide

private theorem tailStage (l : Launch) (g : Nat) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) : TailStage l g round warp frame keep :=
  match round with
  | .first => tailStageFirst l g warp frame keep
  | .biased => tailStageBiased l g warp frame keep
  | .unbiased => tailStageUnbiased l g warp frame keep

private theorem tailAddress (hp : Pre p l m) (g : Nat) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) (offset : Nat) (hO : offset ≤ 8) :
    let s := signalSite (tailPublication round)
    Seg kernel Assumptions.all l g 2 (probabilityWaitPc round true + 8)
      ((tailOffsetReg round, b32 offset) :: tailCarryWith l warp round frame keep) s.pc
      ((s.base, b32 (l.sharedBase + offset)) :: (s.count, b32 1) ::
        tailCarryWith l warp round frame keep) := by
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hOff : offset < 2 ^ 32 := by omega
  have hSum : l.sharedBase + offset < 2 ^ 32 := by omega
  have hAddress :
      Value.bits 32
          (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
            truncBits 32 (BitVec.ofNat 64 offset))) =
        b32 (l.sharedBase + offset) := by
    rw [truncBits_ofNat hBase (by decide), truncBits_ofNat hOff (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hSum (by decide)]
    rfl
  dsimp only
  cases round <;> cases frame <;> cases keep <;> intro t ht <;>
    simp only [tailCarryWith, tailLiveWith, tailContinuationRegs, Repeated.continuationRegs,
      Bool.false_eq_true,
      ↓reduceIte, probabilityWaitPc, tailOffsetReg, signalSite, tailPublication] at ht ⊢ <;>
    seg_fp ht using first | exact hAddress | decide

private theorem tailPrepare (hp : Pre p l m) (g : Nat) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) :
    let s := signalSite (tailPublication round)
    Seg kernel Assumptions.all l g 5 (probabilityWaitPc round true + 5)
      (tailCarryWith l warp round frame keep) s.pc
      ((s.base, b32 (l.sharedBase + 8 * (stageOf warp).val)) ::
        (s.count, b32 1) :: tailCarryWith l warp round frame keep) := by
  have hStage := (stageOf warp).isLt
  exact Seg.comp (tailStage l g round warp frame keep)
    (tailAddress hp g round warp frame keep _ (by omega))

/-- The first elected P-tail lane reaches the unit release using its startup frame. -/
theorem firstTailSelectedRelease (hp : Pre p l m) (warp : Fin 8) {g : Nat} {t : TState}
    (ht : At t 4860 ((623,.pred true) :: tailFrame l warp)) :
    ∃ u v, Next kernel Assumptions.all l g t u
      (.arrive (signalLoc l g (stageOf warp) 2) 0 v 1 true .cta) := by
  have hStart : At t (probabilityWaitPc .first true + 3)
      ((tailElectPred .first,.pred true) :: tailCarryWith l warp .first none false) := ht
  obtain ⟨u,hLocal,hU⟩ := ((tailNegate l g .first warp none false true).comp
    (tailBranch .first warp none false true)).rtg hStart
  obtain ⟨v,hPrep,hV⟩ := (tailPrepare hp g .first warp none false).rtg hU
  exact ⟨v,_,⟨hLocal.trans hPrep,signalTemplate hp (stageOf warp) 2 hV.1
    hV.2.2.2.1 hV.2.2.2.2.1 hV.2.2.2.2.2.1⟩⟩

/-- The elected lane releases the tail slot. Its peers bypass the release and reach
the same join without advancing their event cursors. -/
private theorem tailNotificationPath {X : Execution} (hp : Pre p l m) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) {g j : Nat} {t : TState} (chosen : Bool)
    (ht : At t (probabilityWaitPc round true + 3)
      ((tailElectPred round, .pred chosen) :: tailCarryWith l warp round frame keep))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let i := tailPublication round
    ∃ u, (chosen = true → X.get (g, j) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (tailCarryWith l warp round frame keep) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (if chosen then j + 1 else j)) none ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop j).take (if chosen then 1 else 0)) u := by
  dsimp only
  obtain ⟨u, hLocal, hU⟩ := ((tailNegate l g round warp frame keep chosen).comp
    (tailBranch round warp frame keep chosen)).rtg ht
  have hRest := hRun.after_local hLocal
  cases chosen
  · exact ⟨u,(fun h => Bool.false_ne_true h |>.elim),hU,hRest,.of_local hLocal⟩
  · obtain ⟨v, hPrep, hV⟩ := (tailPrepare hp g round warp frame keep).rtg hU
    let i := tailPublication round
    obtain ⟨hSignal, hAfter⟩ := signalTrace hp (stageOf warp) i hV.1 hV.2.2.2.1
      hV.2.2.2.2.1 hV.2.2.2.2.2.1 (hRest.after_local hPrep)
    let w := next (mbarStateDest v (some (signalSite i).state))
    refine ⟨w, fun _ => hSignal, ⟨by exact congrArg (· + 1) hV.1,
      hV.2.1, hV.2.2.1, hV.2.2.2.1, ?_⟩, hAfter,?_⟩
    · exact holds_update hV.2.2.2.2.2.2 fun pair hPair => by
        rcases tailCarryWith_member hPair with h | h | h
        · rw [h]
          cases round <;> decide
        · rw [h]
          cases round <;> decide
        · exact (tailLiveDistinct round keep h).2.2

    · have hOut := signalTemplate hp (stageOf warp) i (g := g) hV.1 hV.2.2.2.1
        hV.2.2.2.2.1 hV.2.2.2.2.2.1
      have hStep : EStep kernel Assumptions.all l g v
          ⟨(signalSite i).pc,.arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩ (some w) := by
        refine ⟨_,hOut,?_,rfl⟩
        rw [hV.1]
      change TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 1) w
      rw [singletonOfTailGet hSignal]
      exact (TraceReach.of_local (hLocal.trans hPrep)).append (.event hStep (.refl _))

/-- The complete local P-tail protocol from the final store wait through the join. -/
theorem tailPublicationPath {X : Execution} (hp : Pre p l m) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) {g j : Nat} {t : TState}
    (ht : At t (probabilityWaitPc round true) (tailCarryWith l warp round frame keep))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityWaitPc round true
    let i := tailPublication round
    ∃ u barInst electInst leader,
      X.get (g, j) = some ⟨pc, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨pc + 1, .warpBar (2 ^ 32 - 1) barInst⟩ ∧
      X.get (g, j + 2) = some ⟨pc + 2, .elect (2 ^ 32 - 1) electInst leader⟩ ∧
      (laneOf l g = leader → X.get (g, j + 3) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (tailCarryWith l warp round frame keep) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if laneOf l g = leader then j + 3 + 1 else j + 3)) none ∧
      TraceReach kernel Assumptions.all l g t
        (((X.tr g).drop j).take (if laneOf l g = leader then 4 else 3)) u := by
  have hLane : ∀ pair ∈ tailCarryWith l warp round frame keep, pair.1 ≠ tailElectLane round := by
    intro pair hp
    rcases tailCarryWith_member hp with h | h | h
    · rw [h]
      cases round <;> decide
    · rw [h]
      cases round <;> decide
    · exact (tailLiveDistinct round keep h).1
  have hPred : ∀ pair ∈ tailCarryWith l warp round frame keep, pair.1 ≠ tailElectPred round := by
    intro pair hp
    rcases tailCarryWith_member hp with h | h | h
    · rw [h]
      cases round <;> decide
    · rw [h]
      cases round <;> decide
    · exact (tailLiveDistinct round keep h).2.1
  obtain ⟨s, barInst, electInst, leader, hWait, hBar, hElect, hS, hTail,hPath⟩ :=
    tailElectionPath hp round ht hLane hPred hr
  have hStart : At s (probabilityWaitPc round true + 3)
      ((tailElectPred round, .pred (laneOf l g == leader)) ::
        tailCarryWith l warp round frame keep) :=
    hS.mono ⟨hS.2.2.2.2.1, hS.2.2.2.2.2.2⟩
  obtain ⟨u, hSignal, hU, hRest,hNext⟩ :=
    tailNotificationPath hp round warp frame keep (laneOf l g == leader) hStart hTail
  refine ⟨u,barInst,electInst,leader,hWait,hBar,hElect,fun h => hSignal (beq_iff_eq.mpr h),
    hU,by simpa only [beq_iff_eq] using hRest,?_⟩
  have hCount : (if laneOf l g = leader then 4 else 3 : Nat) =
      3+(if laneOf l g == leader then 1 else 0) := by simp only [beq_iff_eq]; split <;> rfl
  rw [hCount,List.take_add,List.drop_drop]
  exact hPath.append hNext

theorem tailPublicationCarryWith {X : Execution} (hp : Pre p l m) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) (keep : Bool) {g j : Nat} {t : TState}
    (ht : At t (probabilityWaitPc round true) (tailCarryWith l warp round frame keep))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityWaitPc round true
    let i := tailPublication round
    ∃ u barInst electInst leader,
      X.get (g, j) = some ⟨pc, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨pc + 1, .warpBar (2 ^ 32 - 1) barInst⟩ ∧
      X.get (g, j + 2) = some ⟨pc + 2, .elect (2 ^ 32 - 1) electInst leader⟩ ∧
      (laneOf l g = leader → X.get (g, j + 3) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (tailCarryWith l warp round frame keep) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if laneOf l g = leader then j + 3 + 1 else j + 3)) none := by
  obtain ⟨u,bar,elect,leader,hWait,hBar,hElect,hSignal,hu,hTail,_⟩ :=
    tailPublicationPath hp round warp frame keep ht hr
  exact ⟨u,bar,elect,leader,hWait,hBar,hElect,hSignal,hu,hTail⟩

theorem tailPublicationCarry {X : Execution} (hp : Pre p l m) (round : Round) (warp : Fin 8)
    (frame : Option (Nat → Value)) {g j : Nat} {t : TState}
    (ht : At t (probabilityWaitPc round true) (tailCarry l warp round frame))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityWaitPc round true
    let i := tailPublication round
    ∃ u barInst electInst leader,
      X.get (g, j) = some ⟨pc, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨pc + 1, .warpBar (2 ^ 32 - 1) barInst⟩ ∧
      X.get (g, j + 2) = some ⟨pc + 2, .elect (2 ^ 32 - 1) electInst leader⟩ ∧
      (laneOf l g = leader → X.get (g, j + 3) = some
        ⟨(signalSite i).pc, .arrive (signalLoc l g (stageOf warp) i) 0 1 true .cta⟩) ∧
      At u ((signalSite i).pc + 1) (tailCarry l warp round frame) ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (if laneOf l g = leader then j + 3 + 1 else j + 3)) none :=
  tailPublicationCarryWith hp round warp frame false ht hr

end
end PTX.Kernels.TmlFa4Fwd.Softmax
