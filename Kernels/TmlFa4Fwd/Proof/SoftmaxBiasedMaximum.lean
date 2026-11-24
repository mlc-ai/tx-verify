-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasedScores
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedMax
import Kernels.TmlFa4Fwd.Flow.Code.Part086

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

private theorem biasMaximumInputMap :
    (List.range 64).all (fun n =>
      match (shiftItems 1)[n]?, (biasBodyItems true)[n]? with
      | some a, some i =>
        (a.a == i.result) && (i.qk == 7367+n) &&
          (a.x == 1363+2*n) && (a.y == 1363+2*n+1) &&
          (a.a != 7251) && ((repeatedMaxPacks true).idxOf? a.a == some n)
      | _, _ => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem biasShiftInput {t : TState} (scores : Nat → Option ℝ)
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1)))))
    {n : Nat} {a : FmaItem} (hn : n < 64) (ha : (shiftItems 1)[n]? = some a) :
    a.a ≠ 7251 ∧ (repeatedMaxPacks true).idxOf? a.a = some n ∧
    a.x = 1363+2*n ∧ a.y = 1363+2*n+1 ∧
    t.regs a.a = some (.pair (scoreValue (scores (2*n))) (scoreValue (scores (2*n+1)))) := by
  have hr := List.all_eq_true.mp biasMaximumInputMap n (List.mem_range.mpr hn)
  rw [ha] at hr
  cases hi : (biasBodyItems true)[n]? with
  | none => simp [hi] at hr
  | some i =>
    simp only [hi,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at hr
    obtain ⟨⟨⟨⟨⟨hReg,hCol⟩,hX⟩,hY⟩,hOld⟩,hRank⟩ := hr
    have hMem : i ∈ biasBodyItems true := List.mem_of_getElem? hi
    refine ⟨hOld,hRank,hX,hY,?_⟩
    rw [hReg]
    simpa only [hCol,Nat.add_sub_cancel_left] using hLogits i hMem

/-- The affine output pairs are the operands of the corresponding biased shift. -/
theorem biasedLogitsForShift {t : TState} (scores : Nat → Option ℝ)
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1))))) :
    ∀ i ∈ shiftItems 1, i.pk = none ∧
      t.regs i.a = some (.pair (scoreValue (scores (i.x-1363)))
        (scoreValue (scores (i.y-1363)))) := by
  intro i hi
  obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hi
  have hN := (List.getElem?_eq_some_iff.mp hn).1
  rw [shiftLength] at hN
  obtain ⟨_,_,hX,hY,hPair⟩ := biasShiftInput scores hLogits hN hn
  have hNoPacks : ((shiftItems 1).all (fun i => i.pk.isNone)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hPack : i.pk = none := Option.isNone_iff_eq_none.mp
    (List.all_eq_true.mp hNoPacks i hi)
  exact ⟨hPack,by simpa only [hX,hY,Nat.add_assoc,Nat.add_sub_cancel_left] using hPair⟩

private theorem maxScore_none (a : Option ℝ) : maxScore a none = a := by cases a <;> rfl

def biasCombinedScores (scores : Nat → Option ℝ) (old : Option ℝ) (n : Nat) :
    Option ℝ :=
  if n = 0 then old else scores (n-1)

/-- The decoded biased reduction reads the current score pairs and prior reference. -/
theorem biasedMaximumWords {s : TState} (scores : Nat → Option ℝ) (old : Option ℝ)
    (hLogits : ∀ i ∈ biasBodyItems true,
      s.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1)))))
    (hOld : s.regs 7251 = some (scoreValue old)) :
    ∀ r ∈ repeatedMaxDom true,
      s.regs r =
        some (scalarValue (biasCombinedScores scores old) (repeatedMaxInputs true) r) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [
      repeatedMaxInputs,repeatedMaxOld,ite_true,beq_self_eq_true,scalarValue,
      Option.map_some,Option.getD_some,MaxDatum.value,scoreMax,List.foldr_cons,List.foldr_nil,
      maxScore_none,biasCombinedScores,ite_true] using hOld
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
    obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp ha
    have hN := (List.getElem?_eq_some_iff.mp hn).1
    rw [shiftLength] at hN
    obtain ⟨hNe,hRank,_,_,hWord⟩ := biasShiftInput scores hLogits hN hn
    have hL : (2*n+1-1) = 2*n := by omega
    have hH : (2*n+2-1) = 2*n+1 := by omega
    simpa only [repeatedMaxInputs,repeatedMaxOld,
      ite_true,beq_iff_eq,ite_eq_right hNe,hRank,scalarValue,Option.map_some,Option.getD_some,
      MaxDatum.value,scoreMax,List.foldr_cons,List.foldr_nil,maxScore_none,
      biasCombinedScores,ite_eq_right (show 2*n+1 ≠ 0 by omega),
      ite_eq_right (show 2*n+2 ≠ 0 by omega),hL,hH] using hWord

variable {l : Launch} {g : Nat} {t : TState}

/-- The repeated Bias logits and the previous maximum become the actual
reduction inputs after the local comparison. -/
theorem biasedMaximumInputs (scores : Nat → Option ℝ) (old : Option ℝ) (nextBlock floor : Nat)
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1))))) (hOld : t.regs 7251 = some (scoreValue old))
    (hBlock : t.regs 7249 = some (b32 nextBlock)) (hFloor : t.regs 1361 = some (b32 floor)) :
    ∃ s, At s (repeatedMaxStart true) [] ∧ run kernel Assumptions.all l g 1 t = some s ∧
      (∀ r ∈ repeatedMaxDom true,
        s.regs r =
          some (scalarValue (biasCombinedScores scores old) (repeatedMaxInputs true) r)) ∧
      (∀ r, r ≠ 634 → s.regs r = t.regs r) ∧
      s.regs 634 = some (.pred (compare .lt .u 32
        (truncBits 32 (BitVec.ofNat 64 nextBlock)) (truncBits 32 (BitVec.ofNat 64 floor)))) := by
  let mixed := compare .lt .u 32
    (truncBits 32 (BitVec.ofNat 64 nextBlock)) (truncBits 32 (BitVec.ofNat 64 floor))
  let s := next (setReg t 634 (.pred mixed))
  have hAt : At t 5535 [] := ht
  have hRunLocal : run kernel Assumptions.all l g 1 t = some s := by
    apply run_local Flow.code_5535 rfl hAt
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hAt.1 ▸ (by decide : 5535 ∉ Assumptions.swExp2Sites)) rfl,
      execLocalA_nil,execLocal_int rfl]
    change (do
      let a ← readBits l g t 32 (.reg 7249)
      let b ← readBits l g t 32 (.reg 1361)
      pure (next (setReg t 634 (.pred (compare .lt .u 32 a b))))) = .ok s
    rw [readBits_b32' hBlock,readBits_b32' hFloor]
    rfl
  have hs : At s (repeatedMaxStart true) [] := by
    exact ⟨congrArg (·+1) ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,trivial⟩
  have hInputs := biasedMaximumWords (s := s) scores old (fun i hi => by
    have hNot : i.result ≠ 634 := by
      have hKeys : (biasBodyItems true).all (fun x => x.result != 634) = true := by decide +kernel
      exact bne_iff_ne.mp (List.all_eq_true.mp hKeys _ hi)
    simpa only [s,next,setReg,Function.update_of_ne hNot] using hLogits i hi)
    (by simpa only [s,next,setReg,Function.update_of_ne (by decide : 7251 ≠ 634)] using hOld)
  refine ⟨s,hs,hRunLocal,hInputs,fun r hn => ?_,?_⟩
  · exact Function.update_of_ne hn ..
  · simp [s,next,setReg,mixed]

/-- The biased maximum reduction consumes the 128 affine logits and the preceding maximum.
The preceding setp supplies the predicate that chooses the exponent path. -/
theorem biasedMaximumLocal (scores : Nat → Option ℝ) (old : Option ℝ) (nextBlock floor : Nat)
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1))))) (hOld : t.regs 7251 = some (scoreValue old))
    (hBlock : t.regs 7249 = some (b32 nextBlock)) (hFloor : t.regs 1361 = some (b32 floor)) :
    ∃ u candidate, At u (referenceSite .biased).pc [(4560,scoreValue candidate)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v) ∧
      (∀ r, r ≠ 634 → r ∉ rWrites (repeatedMaxItems true) → u.regs r = t.regs r) ∧
      u.regs 634 = some (.pred (compare .lt .u 32
        (truncBits 32 (BitVec.ofNat 64 nextBlock)) (truncBits 32 (BitVec.ofNat 64 floor)))) := by
  let combined := biasCombinedScores scores old
  obtain ⟨s,hs,hRunLocal,hInputs,hKeep,hMixed⟩ :=
    biasedMaximumInputs (l := l) (g := g) scores old nextBlock floor ht hLogits hOld hBlock hFloor
  obtain ⟨u,candidate,hu,hTail,hMaximum,hFrame⟩ :=
    repeatedMaxLocal true combined hs hInputs
  refine ⟨u,candidate,hu,(run_rtg hRunLocal).trans hTail,?_,?_,?_⟩
  · intro v
    rw [hMaximum]
    constructor
    · intro h
      exact ⟨h 0 (by decide),fun i hi => by
        have hh := h (i+1) (by omega)
        simpa only [combined,biasCombinedScores,
          ite_eq_right (show i+1 ≠ 0 by omega),Nat.add_sub_cancel] using hh⟩
    · intro h i hi
      by_cases hz : i = 0
      · simpa [combined,biasCombinedScores,hz] using h.1
      · simpa only [combined,biasCombinedScores,ite_eq_right hz] using h.2 (i-1) (by omega)
  · exact fun r hr hw => (hFrame r hw).trans (hKeep r hr)
  · exact (hFrame 634 (by decide +kernel)).trans hMixed

/-- The biased logits determine the actual running reference and rescale word,
using the lane's launch scale and previous running maximum. -/
theorem biasedReferenceLocal (scores : Nat → Option ℝ) (old : Option ℝ) (nextBlock floor : Nat)
    (scale : ℝ) (hs : 0 < scale) (word : Value)
    (hWord : readEReal .f32 word = some (.ok (scale : EReal)))
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      t.regs i.result = some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1))))) (hOld : t.regs 7251 = some (scoreValue old))
    (hBlock : t.regs 7249 = some (b32 nextBlock)) (hFloor : t.regs 1361 = some (b32 floor))
    (hScale : t.regs 7132 = some word) :
    ∃ u candidate, At u 5675 [(7256,scoreValue (chosenReference scale old candidate)),
      (4565,finiteRefValue (chosenReference scale old candidate)),
      (1362,alphaWord scale old candidate)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v) ∧
      (∀ r, r ≠ 634 → r ∉ rWrites (repeatedMaxItems true) →
        r ∉ [4561,635] → r ∉ oWrites (alphaSite true).items → u.regs r = t.regs r) ∧
      u.regs 634 = some (.pred (compare .lt .u 32
        (truncBits 32 (BitVec.ofNat 64 nextBlock)) (truncBits 32 (BitVec.ofNat 64 floor)))) := by
  obtain ⟨s,candidate,hsAt,hsTail,hBound,hFrame,hMixed⟩ :=
    biasedMaximumLocal (l := l) (g := g) scores old nextBlock floor ht hLogits hOld
      hBlock hFloor
  obtain ⟨v,hvAt,hvTail,hvFrame⟩ :=
    finiteReferenceLocal (l := l) (g := g) .biased candidate (hsAt.mono trivial) hsAt.2.2.2.2.1
  have hRead : ∀ r ∈ (alphaSite true).inputs,
      v.regs r = some ((alphaSite true).valuesOfWord word old candidate r) := by
    intro r hr
    change r ∈ [7251,4560,4561,7132] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hvFrame _ (by decide)).trans ((hFrame _ (by decide) (by decide +kernel)).trans hOld)
    · exact hvAt.2.2.2.2.2.1
    · exact hvAt.2.2.2.2.1
    · exact (hvFrame _ (by decide)).trans ((hFrame _ (by decide) (by decide +kernel)).trans hScale)
  obtain ⟨u,huRun,huAt,huFrame⟩ :=
    alphaSegmentWithScaleWord (l := l) (g := g) true hs old candidate hWord (hvAt.mono trivial)
      hRead
  refine ⟨u,candidate,huAt,(hsTail.trans hvTail).trans (run_rtg huRun),hBound,?_,?_⟩
  · intro r hR hMax hFinite hAlpha
    exact (huFrame r hAlpha).trans ((hvFrame r hFinite).trans (hFrame r hR hMax))
  · exact (huFrame _ (by decide)).trans ((hvFrame _ (by decide)).trans hMixed)

end PTX.Kernels.TmlFa4Fwd.Softmax
