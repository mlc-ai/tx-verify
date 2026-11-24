-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxUnbiasedProbabilityAddress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreStart
import Kernels.TmlFa4Fwd.Flow.Code.Part104
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

private theorem plainSharedOffset (l : Launch) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 2
      6672 [(644,.pred (stage.val = 1)),(2535,b32 l.sharedBase)]
      6674 [(5186,b32 (8*stage.val)),(2535,b32 l.sharedBase)] := by
  fin_cases stage <;> intro t ht <;> seg_fp ht using decide

variable {p : Params} {l : Launch} {m : Mem0}

private theorem plainSharedAddresses (hp : Pre p l m) (g : Nat) (stage : Fin 2) :
    Seg kernel Assumptions.all l g 2
      6674 [(5186,b32 (8*stage.val)),(2535,b32 l.sharedBase)]
      6676 [(5126,b32 (waitLoc l g stage (qkWaitSite .unbiased)).addr),
        (5187,b32 (l.sharedBase+8*stage.val))] := by
  have hL := hp.shared.2.1
  have hStage := stage.isLt
  have hb : l.sharedBase < 2^32 := by omega
  have hs : 8*stage.val < 2^32 := by omega
  have hBase : l.sharedBase+8*stage.val < 2^32 := by omega
  have hWait : l.sharedBase+8*stage.val+80 < 2^32 := by omega
  have hWord₁ :
      Value.bits 32
        (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
          truncBits 32 (BitVec.ofNat 64 (8*stage.val)))) =
        b32 (l.sharedBase+8*stage.val) := by
    rw [truncBits_ofNat hb (by decide),truncBits_ofNat hs (by decide),← BitVec.ofNat_add,
      truncBits_ofNat hBase (by decide)]
    rfl
  have hWord₂ :
      Value.bits 32
        (truncBits 32
          (truncBits 32
            (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
              truncBits 32 (BitVec.ofNat 64 (8*stage.val)))) +
            truncBits 32 (BitVec.ofInt 64 80))) =
        b32 (waitLoc l g stage (qkWaitSite .unbiased)).addr := by
    rw [show BitVec.ofInt 64 80 = BitVec.ofNat 64 80 by decide,
      truncBits_ofNat hb (by decide),truncBits_ofNat hs (by decide),← BitVec.ofNat_add,
      truncBits_ofNat hBase (by decide),truncBits_ofNat hBase (by decide),
      truncBits_ofNat (n := 80) (by decide) (by decide),← BitVec.ofNat_add,
      truncBits_ofNat hWait (by decide)]
    change b32 (l.sharedBase+8*stage.val+80) = b32 (l.sharedBase+(80+8*stage.val))
    rw [show l.sharedBase+8*stage.val+80 = l.sharedBase+(80+8*stage.val) by omega]
  intro t ht
  seg_fp ht using first | exact hWord₁ | exact hWord₂

def plainReadySetup (l : Launch) (g : Nat) (warp : Fin 8) :=
  unbiasedAddressRows l g warp ++ (unbiasedProbabilityFacts l g (stageOf warp) ++
    roundScoreFacts l g (stageOf warp) .unbiased)

def plainReadyFacts (l : Launch) (g : Nat) (warp : Fin 8)
    (phase : Nat) (rest : List (Nat × Value)) :=
  [(5126,b32 (waitLoc l g (stageOf warp) (qkWaitSite .unbiased)).addr),
    (5187,b32 (l.sharedBase+8*(stageOf warp).val)),(7253,b32 phase)] ++
    (plainReadySetup l g warp ++ rest)

private theorem plainReadySetupKeeps {l : Launch} {g : Nat} {t u : TState}
    (ht : t.pc = 6672) (hRun : run kernel Assumptions.all l g 4 t = some u) :
    ∀ r ∉ [1055,5186,5187,5126], u.regs r = t.regs r := by
  apply fixedFrame (first := 6672) (stop := 6676) _ _ (by rw [ht]) (by rw [ht]) hRun
  · intro pc hl hh
    interval_cases pc
    · exact ⟨_,Flow.code_6672,rfl,rfl,fun _ => nofun,by simp [writesRegs]; tauto⟩
    · exact ⟨_,Flow.code_6673,rfl,rfl,fun _ => nofun,by simp [writesRegs]; tauto⟩
    · exact ⟨_,Flow.code_6674,rfl,rfl,fun _ => nofun,by simp [writesRegs]; tauto⟩
    · exact ⟨_,Flow.code_6675,rfl,rfl,fun _ => nofun,by simp [writesRegs]⟩
  · intro pc hl hh hm
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

private theorem plainSetupSafe (l : Launch) (g : Nat) (warp : Fin 8) :
    (plainReadySetup l g warp).all (fun x => !([1055,5186,5187,5126] : List Nat).contains x.1) =
      true := by rfl

private theorem frameFacts {t u : TState}
    {facts : List (Nat × Value)} (ht : Holds t.regs facts)
    (hKeep : ∀ n ∉ [1055,5186,5187,5126], u.regs n = t.regs n)
    (hSafe : ∀ x ∈ facts, x.1 ∉ [1055,5186,5187,5126]) :
    Holds u.regs facts := by
  apply Epilogue.holdsSchedulerFrame (regs := facts.map Prod.fst) ht
  · intro r hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact hKeep x.1 (hSafe x hx)
  · exact fun _ hx => List.mem_map_of_mem hx

/-- The plain setup computes its score, probability and signal addresses
before the score-ready poll, independently of the loop's numerical state. -/
theorem plainReadyGeometrySegment (hp : Pre p l m) (g : Nat) (warp : Fin 8) :
    Seg kernel Assumptions.all l g 15 6661 [(1062,b32 warp.val),(2535,b32 l.sharedBase)]
      6676 ((5187,b32 (l.sharedBase+8*(stageOf warp).val)) ::
        (unbiasedAddressRows l g warp).drop 1 ++ unbiasedProbabilityFacts l g (stageOf warp)) := by
  intro t ht
  obtain ⟨s,hSetupRun,hS⟩ := (unbiasedTensorAddressSegmentWithRows hp g warp).apply
    (ht.mono ⟨ht.2.2.2.2.1,trivial⟩)
  have hSetup := unbiasedSetupFrame (by rw [ht.1]) (by rw [ht.1]; decide) hSetupRun
  have hBase := (hSetup 2535 (by decide)).trans ht.2.2.2.2.2.1
  have hFlags : Holds s.regs (plainReadySetup l g warp) := hS.2.2.2.2
  obtain ⟨u,huRun,hu⟩ := ((plainSharedOffset l g (stageOf warp)).comp
      (plainSharedAddresses hp g (stageOf warp))).apply (hS.mono ⟨hFlags.1,hBase,trivial⟩)
  have hFrame := plainReadySetupKeeps hS.1 huRun
  have hFlagU := frameFacts hFlags hFrame (fun x hx => by
    have h := List.all_eq_true.mp (plainSetupSafe l g warp) x hx
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h)
  have hRows := (holds_append ..).mp hFlagU
  have hProb := (holds_append ..).mp hRows.2
  exact ⟨u,run_comp hSetupRun huRun,hu.mono
    ⟨hu.2.2.2.2.2.1,(holds_append ..).mpr ⟨hRows.1.2,hProb.1⟩⟩⟩

/-- The actual plain loop head prepares the four score and probability addresses
and its score-ready poll, while retaining the preceding iteration's state. -/
theorem plainScoreReadyLocal (hp : Pre p l m) (warp : Fin 8) {g phase : Nat} {t : TState}
    (facts : List (Nat × Value)) (hStable : ∀ x ∈ facts, x.1 ∉ unbiasedSetupWrites)
    (ht : At t 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 phase)::facts)) :
    ∃ u, At u 6676 (plainReadyFacts l g warp phase facts) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨s,hSetupRun,hS⟩ := (unbiasedTensorAddressSegmentWithRows hp g warp).apply
    (ht.mono ⟨ht.2.2.2.2.1,trivial⟩)
  have hSetup := unbiasedSetupFrame (by rw [ht.1]) (by rw [ht.1]; decide) hSetupRun
  have hBase := (hSetup 2535 (by decide)).trans ht.2.2.2.2.2.1
  have hPar := (hSetup 7253 (by decide)).trans ht.2.2.2.2.2.2.1
  have hFlags : Holds s.regs (plainReadySetup l g warp) := hS.2.2.2.2
  have hStage : s.regs 644 = some (.pred ((stageOf warp).val = 1)) := hFlags.1
  obtain ⟨u,huRun,hu⟩ := ((plainSharedOffset l g (stageOf warp)).comp
      (plainSharedAddresses hp g (stageOf warp))).apply (hS.mono ⟨hStage,hBase,trivial⟩)
  have hFrame := plainReadySetupKeeps hS.1 huRun
  have hFlagU := frameFacts hFlags hFrame (fun x hx => by
    have h := List.all_eq_true.mp (plainSetupSafe l g warp) x hx
    simpa only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] using h)
  have hOther : Holds u.regs facts := by
    have hKeepAll := unbiasedSetupFrame (by rw [ht.1]) (by rw [ht.1]) (run_comp hSetupRun huRun)
    apply Epilogue.holdsSchedulerFrame (regs := facts.map Prod.fst) ht.2.2.2.2.2.2.2
    · intro r hr
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
      exact hKeepAll _ (hStable x hx)
    · exact fun _ hx => List.mem_map_of_mem hx
  have hTailFacts : Holds u.regs (plainReadySetup l g warp ++ facts) :=
    (holds_append ..).mpr ⟨hFlagU,hOther⟩
  have hUFacts : Holds u.regs (plainReadyFacts l g warp phase facts) :=
    ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.1,(hFrame 7253 (by decide)).trans hPar,hTailFacts⟩
  exact ⟨u,hu.mono hUFacts,(run_rtg hSetupRun).trans (run_rtg huRun)⟩

private theorem plainReadyScratch {l : Launch} {g phase : Nat} {warp : Fin 8}
    {facts : List (Nat × Value)} (hFresh : ∀ x ∈ facts, x.1 ≠ 9821)
    (x : Nat × Value) (hx : x ∈ plainReadyFacts l g warp phase facts) :
    x.1 ≠ (waitSite (qkWaitSite .unbiased)).result := by
  have hSite : (waitSite (qkWaitSite .unbiased)).result = 9821 := rfl
  rw [hSite]
  simp only [plainReadyFacts,List.cons_append,List.nil_append,List.mem_cons,List.mem_append] at hx
  rcases hx with rfl | rfl | rfl | h | h
  · change 5126 ≠ 9821
    decide
  · change 5187 ≠ 9821
    decide
  · change 7253 ≠ 9821
    decide
  · have hAudit : (plainReadySetup l g warp).all (fun x => x.1 != 9821) = true := by rfl
    simpa only [bne_iff_ne] using List.all_eq_true.mp hAudit x h
  · exact hFresh x h

/-- The ordinary repeated loop consumes the real ready polls before its four score loads. -/
theorem plainScorePathFromHead {X : Execution} (hp : Pre p l m) (warp : Fin 8) {g j phase : Nat}
    (hPhase : phase < 2) {t : TState} (facts : List (Nat × Value))
    (hStable : ∀ x ∈ facts, x.1 ∉ unbiasedSetupWrites) (hFresh : ∀ x ∈ facts, x.1 ≠ 9821)
    (ht : At t 6661 ((1062,b32 warp.val)::(2535,b32 l.sharedBase)::(7253,b32 phase)::facts))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ u failed,
      let stage := stageOf warp
      let wait := qkWaitSite .unbiased
      let target := waitLoc l g stage wait
      (X.tr g).drop j = List.replicate failed ⟨(waitSite wait).pc,
        .wait target phase false true .cta⟩ ++
        ⟨(waitSite wait).pc,.wait target phase true true .cta⟩ ::
          (X.tr g).drop (j+failed+1) ∧
      At u (scorePc .unbiased 0) (plainReadyFacts l g warp phase facts) ∧
      (∀ q : Fin 4, u.regs (scoreReg .unbiased q) =
        some (b32 (scoreAddress l g stage q))) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+failed+1)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (failed+1)) u := by
  obtain ⟨s,hs,hLocal⟩ := plainScoreReadyLocal hp warp facts hStable ht
  let stage := stageOf warp
  let wait := qkWaitSite .unbiased
  have hBase : ((waitSite wait).base,b32 (waitLoc l g stage wait).addr) ∈
      plainReadyFacts l g warp phase facts := .head _
  have hPar : ((waitSite wait).phase,b32 phase) ∈ plainReadyFacts l g warp phase facts :=
    .tail _ (.tail _ (.head _))
  obtain ⟨failed,u,hPolls,hu,hTail,hPath⟩ := waitTraceAtWithPath hp stage wait g phase hPhase
    hBase hPar
    (plainReadyScratch hFresh) hs (hRun.after_local hLocal)
  have hHeld : Holds u.regs (plainReadyFacts l g warp phase facts)  := hu.2.2.2.2
  have hAt : At u (scorePc .unbiased 0) (plainReadyFacts l g warp phase facts) :=
    hu.mono hHeld
  have hSetupFacts : Holds u.regs (plainReadySetup l g warp) :=
    ((holds_append u.regs (plainReadySetup l g warp) facts).mp hHeld.2.2.2).1
  have hAddrFacts : Holds u.regs (unbiasedProbabilityFacts l g stage ++
      roundScoreFacts l g stage .unbiased) :=
    ((holds_append u.regs (unbiasedAddressRows l g warp) _).mp hSetupFacts).2
  have hAddrs : Holds u.regs (roundScoreFacts l g stage .unbiased) :=
    ((holds_append u.regs (unbiasedProbabilityFacts l g stage) _).mp hAddrFacts).2
  exact ⟨u,failed,hPolls,hAt,fun q => holds_mem hAddrs (List.mem_ofFn.mpr ⟨q,rfl⟩),hTail,
    (TraceReach.of_local hLocal).append hPath⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
