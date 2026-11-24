-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainVisitExtent
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAlpha

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

private def plainPairByIndex (i : Nat) : Nat :=
  repeatedScorePairReg .unbiased ⟨i/16%4,Nat.mod_lt _ (by decide)⟩ (i%16)

private theorem plainMaximumPairMap :
    (List.range 64).all (fun n => (shiftItems 2)[n]?.any fun i =>
      i.pk.isNone && (i.a == plainPairByIndex n) &&
      (i.x == 5520+2*n) && (i.y == 5520+2*n+1) &&
      (i.a != 7255) && ((repeatedMaxPacks false).idxOf? i.a == some n)) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem plainMaximumPair {t : TState} (scores : Nat → Option ℝ)
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1)))))) :
    ∀ (i : FmaItem) (n : Nat), n < 64 → (shiftItems 2)[n]? = some i →
      i.pk = none ∧ i.a ≠ 7255 ∧ (repeatedMaxPacks false).idxOf? i.a = some n ∧
      i.x = 5520+2*n ∧ i.y = 5520+2*n+1 ∧
      t.regs i.a = some (.pair (scoreValue (scores (2*n))) (scoreValue (scores (2*n+1)))) := by
  intro i n hn hi
  have h := List.all_eq_true.mp plainMaximumPairMap n (List.mem_range.mpr hn)
  simp only [hi,Option.any_some,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨hNo,hReg⟩,hX⟩,hY⟩,hOld⟩,hRank⟩ := h
  have hPack := Option.isNone_iff_eq_none.mp hNo
  let q : Fin 4 := ⟨n/16%4,Nat.mod_lt _ (by decide)⟩
  let k : Fin 16 := ⟨n%16,Nat.mod_lt _ (by decide)⟩
  have hLo : 32*q.val+2*k.val = 2*n := by
    dsimp [q,k]
    rw [Nat.mod_eq_of_lt (by omega : n/16 < 4)]
    omega
  have hHi : 32*q.val+(2*k.val+1) = 2*n+1 := by omega
  refine ⟨hPack,hOld,hRank,hX,hY,?_⟩
  rw [hReg]
  change t.regs (repeatedScorePairReg .unbiased q k.val) = _
  simpa only [hLo,hHi] using hPacked q k

/-- The plain score-load pairs are preserved as the operands for the score shift. -/
theorem plainLogitsForShift {t : TState} (scores : Nat → Option ℝ)
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1)))))) :
    ∀ i ∈ shiftItems 2, i.pk = none ∧
      t.regs i.a = some (.pair (scoreValue (scores (i.x-5520)))
        (scoreValue (scores (i.y-5520)))) := by
  intro i hi
  obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hi
  have hN := (List.getElem?_eq_some_iff.mp hn).1
  rw [shiftLength] at hN
  obtain ⟨hPack,_,_,hX,hY,hPair⟩ := plainMaximumPair scores hPacked i n hN hn
  exact ⟨hPack,by simpa only [hX,hY,Nat.add_assoc,Nat.add_sub_cancel_left] using hPair⟩

def plainCombinedScores (s : Nat → Option ℝ) (old : Option ℝ) (n : Nat) : Option ℝ :=
  if n = 0 then old else s (n-1)

private theorem maxScore_none (a : Option ℝ) : maxScore a none = a := by cases a <;> rfl

/-- The previous maximum and observed plain score pairs are the decoded reduction inputs. -/
theorem plainMaximumInputs {t : TState} (scores : Nat → Option ℝ) (old : Option ℝ)
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1))))))
    (hOld : t.regs 7255 = some (scoreValue old)) :
    ∀ r ∈ repeatedMaxDom false,
      t.regs r =
        some (scalarValue (plainCombinedScores scores old) (repeatedMaxInputs false) r) := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simpa only [repeatedMaxInputs,repeatedMaxOld,Bool.false_eq_true,ite_false,ite_true,
      beq_self_eq_true,
      scalarValue,Option.map_some,Option.getD_some,MaxDatum.value,scoreMax,List.foldr_cons,
      List.foldr_nil,maxScore_none,plainCombinedScores] using hOld
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hr
    obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp ha
    have hN := (List.getElem?_eq_some_iff.mp hn).1
    rw [shiftLength] at hN
    obtain ⟨_,hNe,hRank,_,_,hWord⟩ := plainMaximumPair scores hPacked a n hN hn
    have hL : (2*n+1-1) = 2*n := by omega
    have hH : (2*n+2-1) = 2*n+1 := by omega
    simpa only [repeatedMaxInputs,repeatedMaxOld,Bool.false_eq_true,ite_false,beq_iff_eq,
      ite_eq_right hNe,
      hRank,scalarValue,Option.map_some,Option.getD_some,MaxDatum.value,scoreMax,
      List.foldr_cons,List.foldr_nil,maxScore_none,plainCombinedScores,
      ite_eq_right (show 2*n+1 ≠ 0 by omega),ite_eq_right (show 2*n+2 ≠ 0 by omega),hL,hH]
      using hWord

variable {l : Launch} {g : Nat}

/-- The actual plain-loop reduction computes the maximum of its 128 packed
scores and the preceding running reference. -/
theorem plainMaximumLocal {t : TState} (scores : Nat → Option ℝ) (old : Option ℝ)
    (ht : At t (repeatedMaxStart false) [])
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1))))))
    (hOld : t.regs 7255 = some (scoreValue old)) :
    ∃ u candidate, At u (referenceSite .unbiased).pc [(5509,scoreValue candidate)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v) ∧
      ∀ r ∉ rWrites (repeatedMaxItems false), u.regs r = t.regs r := by
  let combined := plainCombinedScores scores old
  have hInputs := plainMaximumInputs scores old hPacked hOld
  obtain ⟨u,candidate,hu,hTail,hMaximum,hFrame⟩ :=
    repeatedMaxLocal false combined ht hInputs
  refine ⟨u,candidate,hu,hTail,?_,hFrame⟩
  intro v
  rw [hMaximum]
  constructor
  · intro h
    exact ⟨h 0 (by decide),fun i hi => by
      have hh := h (i+1) (by omega)
      simpa only [combined,plainCombinedScores,
        ite_eq_right (show i+1 ≠ 0 by omega),Nat.add_sub_cancel] using hh⟩
  · intro h i hi
    by_cases hz : i = 0
    · simpa [combined,plainCombinedScores,hz] using h.1
    · simpa only [combined,plainCombinedScores,ite_eq_right hz] using h.2 (i-1) (by omega)

/-- The plain logits determine the new running reference and the actual
rescale word using the retained launch scale. -/
theorem plainReferenceLocal {t : TState} (scores : Nat → Option ℝ) (old : Option ℝ) (scale : ℝ)
    (hs : 0 < scale) (word : Value) (hWord : readEReal .f32 word = some (.ok (scale : EReal)))
    (ht : At t (repeatedMaxStart false) [])
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (scores (32*q.val+2*k.val)))
          (scoreValue (scores (32*q.val+(2*k.val+1))))))
    (hOld : t.regs 7255 = some (scoreValue old)) (hScale : t.regs 7133 = some word) :
    ∃ u candidate, At u 6886 [(7256,scoreValue (chosenReference scale old candidate)),
      (5514,finiteRefValue (chosenReference scale old candidate)),
      (1492,alphaWord scale old candidate)] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (scores i) ≤ v) ∧
      ∀ r, r ∉ rWrites (repeatedMaxItems false) →
        r ∉ [5510,645] → r ∉ oWrites (alphaSite false).items → u.regs r = t.regs r := by
  obtain ⟨s,candidate,hsAt,hsTail,hBound,hFrame⟩ :=
    plainMaximumLocal (l := l) (g := g) scores old ht hPacked hOld
  obtain ⟨v,hvAt,hvTail,hvFrame⟩ :=
    finiteReferenceLocal (l := l) (g := g) .unbiased candidate (hsAt.mono trivial) hsAt.2.2.2.2.1
  have hRead : ∀ r ∈ (alphaSite false).inputs,
      v.regs r = some ((alphaSite false).valuesOfWord word old candidate r) := by
    intro r hr
    change r ∈ [7255,5509,5510,7133] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (hvFrame _ (by decide)).trans ((hFrame _ (by decide +kernel)).trans hOld)
    · exact hvAt.2.2.2.2.2.1
    · exact hvAt.2.2.2.2.1
    · exact (hvFrame _ (by decide)).trans ((hFrame _ (by decide +kernel)).trans hScale)
  obtain ⟨u,huRun,huAt,huFrame⟩ :=
    alphaSegmentWithScaleWord (l := l) (g := g) false hs old candidate hWord (hvAt.mono trivial)
      hRead
  exact ⟨u,candidate,huAt,(hsTail.trans hvTail).trans (run_rtg huRun),hBound,fun r hMax hFinite
    hAlpha =>
    (huFrame r hAlpha).trans ((hvFrame r hFinite).trans (hFrame r hMax))⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
