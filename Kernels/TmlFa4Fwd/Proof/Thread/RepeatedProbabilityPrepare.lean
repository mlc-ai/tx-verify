-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityIssue
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedNumeric
public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublish
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
import all Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedNumeric
import Lemmas.Step.WarpLanes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Correction

/-- At the first repeated P store, the lane's actual cursor contains all sixteen packed words. -/
structure RepeatedProbabilityPrepared (l : Launch) (X : Execution) (g : Nat)
    (mode : Repeated) (stage : Fin 2) (weights : Nat → ℝ) where
  cursor : OpeningTripCursor l X g (probabilityPc mode.round 0) []
  sources : List Nat
  length : sources.length = 16
  code : kernel.code[probabilityPc mode.round 0]? =
    some ⟨none,.tcSt (probabilityReg mode.round 0) (sources.map Opnd.reg) .s32x32b⟩
  words : ∀ i (hi : i < sources.length), cursor.ready.regs sources[i] =
    some (probabilityWord weights i)
  address : cursor.ready.regs (probabilityReg mode.round 0) =
    some (b32 (probabilityAddress l g stage 0))
  exponents : RepeatedWeights mode cursor.ready weights

private def atFirstRepeatedProbability {l : Launch} {X : Execution} {g : Nat}
    {mode : Repeated} {stage : Fin 2} {weights : Nat → ℝ} {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g mode.affineStart F) {t : TState}
    (path : Relation.ReflTransGen (Tau kernel Assumptions.all l g) c.ready t)
    (ht : At t (probabilityPc mode.round 0) []) (sources : List Nat) (hLen : sources.length = 16)
    (hCode : kernel.code[probabilityPc mode.round 0]? =
      some ⟨none,.tcSt (probabilityReg mode.round 0) (sources.map Opnd.reg) .s32x32b⟩)
    (hWords : ∀ i (hi : i < sources.length), t.regs sources[i] = some (probabilityWord weights i))
    (hAddress : t.regs (probabilityReg mode.round 0) =
      some (b32 (probabilityAddress l g stage 0)))
    (hExponents : RepeatedWeights mode t weights) :
    RepeatedProbabilityPrepared l X g mode stage weights :=
  ⟨⟨c.pos,c.before,t,c.ending,c.positive,c.bounded,c.released,ht,c.recorded,c.remaining,
    c.localSteps.trans path⟩,sources,hLen,hCode,hWords,hAddress,hExponents⟩

/-- The exponent arithmetic preserves the ABI, mass, phase, and continuation registers. -/
def repeatedProbabilityRetained (mode : Repeated) : List Nat :=
  (match mode with
    | .biased => biasedExpFrame
    | .unbiased => unbiasedExpFrame) ++ roundContinuationRegs

private structure PackedRoundContinuation (l : Launch) (X : Execution) (g : Nat)
    (mode : Repeated) (stage : Fin 2) (weights : Nat → ℝ) (q : Fin 4) where
  cursor : OpeningTripCursor l X g (probabilityPc mode.round q) []
  arguments : ExponentArguments
  registerTable : ExponentRegs
  mixed : Bool
  eval : ExponentEval arguments weights
  holds : ExponentHolds arguments weights registerTable cursor.ready
  table : (match mode with
    | .biased => biasedStoreInputs mixed q
    | .unbiased => unbiasedStoreInputs q) = some registerTable
  addresses : ∀ quarter, arguments.original (probabilityReg mode.round quarter) =
    b32 (probabilityAddress l g stage quarter)
  publication : Holds cursor.ready.regs (firstPublicationFacts l stage mode.round)
  origin : TState
  originalFrame : ∀ n ∈ (match mode with
    | .biased => biasedExpFrame
    | .unbiased => unbiasedExpFrame), some (arguments.original n) = origin.regs n
  continuationFrame : ∀ n ∈ roundContinuationRegs, arguments.saved n = origin.regs n

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
include hp

/-- On either repeated path, the arithmetic between the reached shift and the first
probability issue is local. The cursor stays at the current trace position. -/
private theorem prepareWithContinuation {mode : Repeated} {g : Nat} {stage : Fin 2}
    {F : List (Nat × Value)} {scores : Nat → Option ℝ} {reference : ℝ}
    (c : OpeningTripCursor l X g mode.affineStart F)
    (frame : RepeatedProbabilityShiftFrame p l mode g stage c.ready scores reference) :
    let weights := fun i =>
      repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-reference) (scores i))
    ∃ v : RepeatedProbabilityPrepared l X g mode stage weights,
      ∃ pack : PackedRoundContinuation l X g mode stage weights 0,
      v.cursor = pack.cursor ∧ v.cursor.pos = c.pos ∧ v.cursor.ending = c.ending ∧
      pack.origin = c.ready := by
  let raw i := affineScore (abiFloat p.scaleLog2Bits) (-reference) (scores i)
  let weights i := repeatedExpWeight (raw i)
  obtain ⟨s,hs,hRaw,hKeep,hPath⟩ := repeatedShiftedWordsLocal hp mode
    scores reference frame.words frame.inputs frame.atShift frame.reads frame.source frame.columns
    frame.scale frame.offset
  have hContinuation n (hn : n ∈ roundContinuationRegs) : s.regs n = c.ready.regs n :=
    hKeep n (continuationShiftFresh mode hn)
  cases mode with
  | biased =>
    let args : ExponentArguments := ⟨raw,biasedOriginal l g stage frame.words,s.regs⟩
    have hEval : ExponentEval args weights :=
      ⟨fun _ => repeatedHardwareExp _,fun _ => repeatedSoftwareExp _⟩
    have hAddr (q : Fin 4) : args.original (probabilityReg .biased q) =
        b32 (probabilityAddress l g stage q) := by fin_cases q <;> rfl
    have hKeep' r (hr : r ∈ 634 :: biasedExpFrame) : s.regs r = c.ready.regs r := by
      have hh := List.all_eq_true.mp biasedFrameShift r hr
      simp only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at hh
      exact hKeep r hh
    have hFrame r (hr : r ∈ biasedExpFrame) : s.regs r = some (args.original r) :=
      (hKeep' r (List.mem_cons_of_mem _ hr)).trans ((frame.frame r hr).trans
        (congrArg some (biasedOriginalFrame l g stage frame.words hr).symm))
    have hStart := hs.mono (G := [(634,.pred frame.mixed)])
      ⟨(hKeep' 634 (.head _)).trans (frame.mixChoice rfl),trivial⟩
    obtain ⟨u,regs,hRegs,hu,hValues,hLocal⟩ := biasedExpStartStoreLocal hp stage frame.mixed
      hEval hStart hRaw hFrame (fun _ _ => rfl) (frame.biasedStage rfl) hAddr
    obtain ⟨hLen,hWords,hAddress⟩ :=
      biasedStoreWords stage frame.mixed 0 hValues hRegs (hAddr 0)
    have hPack := observedBiasedRegs frame.mixed 0 hRegs hValues
    let first := atFirstRepeatedProbability c (hPath.trans hLocal) hu (biasedSources 0) hLen
      (biasedStoreCode 0) (by simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hWords)
      hAddress hPack.1
    have hPublication : Holds u.regs (firstPublicationFacts l stage .biased) :=
      ⟨(hPack.2 _ (by decide)).trans (congrArg some (frame.biasedStage rfl)),
        (hPack.2 _ (by decide)).trans (congrArg some (frame.biasedBase rfl)),trivial⟩
    have hOriginal n (hn : n ∈ biasedExpFrame) :
        some (args.original n) = c.ready.regs n :=
      (congrArg some (biasedOriginalFrame l g stage frame.words hn)).trans (frame.frame n hn).symm
    exact ⟨first,⟨first.cursor,args,regs,frame.mixed,hEval,hValues,hRegs,hAddr,hPublication,
      c.ready,hOriginal,hContinuation⟩,rfl,rfl,rfl,rfl⟩
  | unbiased =>
    let args : ExponentArguments := ⟨raw,frame.words,s.regs⟩
    have hEval : ExponentEval args weights :=
      ⟨fun _ => repeatedHardwareExp _,fun _ => repeatedSoftwareExp _⟩
    have hFrame r (hr : r ∈ unbiasedExpFrame) : s.regs r = some (args.original r) := by
      have hh := List.all_eq_true.mp unbiasedFrameShift r hr
      simp only [Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at hh
      exact (hKeep r hh).trans (frame.frame r hr)
    obtain ⟨u,regs,hRegs,hu,hValues,hLocal⟩ := unbiasedExpStartLocal
      (l := l) (g := g) hEval hs hRaw hFrame (fun _ _ => rfl)
    obtain ⟨hLen,hWords,hAddress⟩ :=
      unbiasedStoreWords stage 0 hValues hRegs (frame.plainAddresses rfl 0)
    have hPack := observedUnbiasedRegs 0 hRegs hValues
    let first := atFirstRepeatedProbability c (hPath.trans hLocal) hu (unbiasedSources 0) hLen
      (unbiasedStoreCode 0) (by simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using hWords)
      hAddress hPack.1
    have hPublication : Holds u.regs (firstPublicationFacts l stage .unbiased) :=
      ⟨(hPack.2 _ (by decide)).trans (congrArg some (frame.plainSignal rfl)),trivial⟩
    exact ⟨first,⟨first.cursor,args,regs,false,hEval,hValues,hRegs,frame.plainAddresses rfl,
      hPublication,c.ready,fun n hn => (frame.frame n hn).symm,hContinuation⟩,rfl,rfl,rfl,rfl⟩

/-- An actual reached first repeated P store publishes the computed BF16 words.
The biased path records its delayed wait before the store. -/
theorem RepeatedProbabilityPrepared.issueOfMaximal (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) {mode : Repeated} {stage : Fin 2} {weights : Nat → ℝ}
    (v : RepeatedProbabilityPrepared l X g mode stage weights)
    (hPeers : mode = .biased → v.cursor.pos+1 = (X.tr g).length →
      ∀ peer ∈ warpLanes l g, ∃ k, X.TcK (peer,k)
        (((X.tr g).take v.cursor.pos).countP isTcColl)) :
    let pos := v.cursor.pos + mode.probabilityStoreOffset 0
    (mode = .biased →
      X.get (g,v.cursor.pos) = some ⟨probabilityPc mode.round 0,.tc .waitLd⟩) ∧
    X.get (g,pos) = some (repeatedStoreEvent l g stage mode.round 0 weights) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next v.cursor.ready)) ∧
    Run kernel Assumptions.all l g (next v.cursor.ready) ((X.tr g).drop (pos+1)) v.cursor.ending :=
  have hw : ∀ i (hi : i < v.sources.length), v.cursor.ready.regs v.sources[i] =
      some (probabilityWord weights (16*(0 : Fin 4).val+i)) := by
    simpa only [Fin.val_zero,Nat.mul_zero,Nat.zero_add] using v.words
  have hd : delayedProbability mode.round 0 = true ↔ mode = .biased := by cases mode <;> decide
  have he := repeatedProbabilityIssueOfMaximal hp hMax hg mode.round stage 0 v.cursor
    v.sources weights v.length v.code hw v.address (fun h => hPeers (hd.mp h))
  have hPos : (if delayedProbability mode.round 0 then v.cursor.pos+1 else v.cursor.pos) =
      v.cursor.pos+mode.probabilityStoreOffset 0 := by cases mode <;> rfl
  by rw [hPos] at he; simpa only [hd] using he

end PTX.Kernels.TmlFa4Fwd.Softmax
