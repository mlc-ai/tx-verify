-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionAlignedTensor
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Epilogue Prologue

/-- An exited correction peer has covered every observed collective if the actual warp
agrees at common ordinals. The terminal wait supplies an actual peer event. -/
theorem correctionTensorPeerCoversOfAgreement {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h i j k : Nat} (hWarp : SameWarp l g h)
    (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hk : X.TcK (g,i) k)
    (hAgree : ∀ {a b ordinal : Nat} {left right : Event},
      X.get (g,a) = some left → X.get (h,b) = some right →
      X.TcK (g,a) ordinal → X.TcK (h,b) ordinal →
      left.pc = right.pc ∧
        AlignedClass.tc.operands left.kind = AlignedClass.tc.operands right.kind) :
    ¬ X.ExitedShort isTcColl (h,j) k := by
  rintro ⟨⟨pc,hExit⟩,hShort⟩
  have hWork := correctionTensorCollectiveRequiresWork hp hX hLo hHi hk
  rw [hWarp.1.2.2] at hWork
  have hRole : warpIndex l g = warpIndex l h := hWarp.2
  obtain ⟨q,hQ,hWait⟩ := correctionFinalTensorWaitBeforeExit hp hX
    (hRole ▸ hLo) (hRole ▸ hHi) hWork hExit
  let ordinal := ((X.tr h).take q).countP isTcColl
  have hWaitOrd : X.TcK (h,q) ordinal := ⟨⟨_,hWait,rfl⟩,rfl⟩
  have hWant : Returned X (h,q) := by
    unfold Returned
    rw [hWait]
    change q+1 < (X.tr h).length
    have hLen : j < (X.tr h).length := len_of_get hExit
    omega
  have hPeer := mem_warpLanes_of_sameWarp hWarp
  obtain ⟨_,_,r,hRef,hr⟩ := hX.dependency.ready (h,q) hWant _
    (tcNeed_mem hWait rfl hPeer)
  obtain ⟨e,he,hColl⟩ := hr.1
  obtain ⟨hPc,hOp⟩ := hAgree he hWait hr hWaitOrd
  have hKind : e.kind = .tc .waitLd := by
    obtain ⟨p, kind⟩ := e
    obtain ⟨a,rfl⟩ := isTcColl_kind hColl
    cases a <;> first | rfl | simp [AlignedClass.operands, tcStatic] at hOp
  have hTerminal : X.get (g,r) = some ⟨9043,.tc .waitLd⟩ := by
    obtain ⟨pos,kind⟩ := e
    change pos = 9043 at hPc
    change kind = .tc .waitLd at hKind
    subst pos kind
    exact he
  have hBefore := (List.take_sublist (q+1) (X.tr h)).countP_le (p := isTcColl)
  have hCount := countP_take_succ (p := isTcColl) hWait rfl
  change (X.tr h).countP isTcColl ≤ k at hShort
  change ((X.tr h).take (q+1)).countP isTcColl = ordinal + 1 at hCount
  have hOrd : ordinal < k := by omega
  have hPos : r < i := by
    by_contra! hEarly
    have hMono := countP_take_mono isTcColl (X.tr g) hEarly
    have hK := hk.2
    have hR := hr.2
    change ((X.tr g).take i).countP isTcColl = k at hK
    change ((X.tr g).take r).countP isTcColl = ordinal at hR
    omega
  exact correctionNoTensorCollectiveAfterFinalWait hp hX hLo hHi hPos hTerminal hk

/-- The position and operation agreed on by correction lanes at a shared ordinal. -/
@[no_expose] def CorrectionTensorSlotAlignment (l : Launch) (X : Execution) : Prop :=
  ∀ {g h i j k : Nat} {e f : Event}, 8 ≤ warpIndex l g → warpIndex l g < 12 → SameWarp l g h →
    X.get (g,i) = some e → X.get (h,j) = some f → X.TcK (g,i) k → X.TcK (h,j) k →
    e.pc = f.pc ∧ correctionTensorOperation e.kind = correctionTensorOperation f.kind

/-- Build correction slot alignment from actual same-ordinal event observations. -/
theorem CorrectionTensorSlotAlignment.of_agreement {l : Launch} {X : Execution}
    (hAgree : ∀ {g h i j k : Nat} {e f : Event},
      8 ≤ warpIndex l g → warpIndex l g < 12 → SameWarp l g h →
      X.get (g,i) = some e → X.get (h,j) = some f → X.TcK (g,i) k → X.TcK (h,j) k →
      e.pc = f.pc ∧ correctionTensorOperation e.kind = correctionTensorOperation f.kind) :
    CorrectionTensorSlotAlignment l X := hAgree

/-- The collective alignment and exit obligations restricted to softmax lanes. -/
structure SoftmaxTensorAlignment (l : Launch) (X : Execution) : Prop where
  sameOrdinal : ∀ {g h i j k : Nat} {e f : Event}, warpIndex l g < 8 → SameWarp l g h →
    X.get (g,i) = some e → X.get (h,j) = some f → X.TcK (g,i) k → X.TcK (h,j) k →
    e.pc = f.pc ∧ AlignedClass.tc.operands e.kind = AlignedClass.tc.operands f.kind
  exitCoverage : ∀ {g h i j k : Nat}, warpIndex l g < 8 → SameWarp l g h → X.TcK (g,i) k →
    ¬ X.ExitedShort isTcColl (h,j) k

/-- Correction checks static operands and short exits once its real ordinal slots agree. -/
theorem arithmeticTensorAlignmentOfCorrectionSlots {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hSoftmax : SoftmaxTensorAlignment l X)
    (hCorrection : CorrectionTensorSlotAlignment l X) :
    ArithmeticTensorAlignment l X := by
  have hAgree {g h i j k : Nat} {e f : Event} (hLo : 8 ≤ warpIndex l g)
      (hHi : warpIndex l g < 12) (hWarp : SameWarp l g h)
      (he : X.get (g,i) = some e) (hf : X.get (h,j) = some f)
      (hi : X.TcK (g,i) k) (hj : X.TcK (h,j) k) :
      e.pc = f.pc ∧ AlignedClass.tc.operands e.kind = AlignedClass.tc.operands f.kind := by
    obtain ⟨hPc,hOp⟩ := hCorrection hLo hHi hWarp he hf hi hj
    obtain ⟨other,hOther,hColl⟩ := hi.1
    obtain rfl := Option.some.inj (he.symm.trans hOther)
    exact ⟨hPc, correctionTensorOperandsAgree hp hX hWarp hLo hHi he hf hColl hPc hOp⟩
  constructor
  · intro g h i j k e f hHi hWarp he hf hi hj
    by_cases hLo : warpIndex l g < 8
    · exact hSoftmax.sameOrdinal hLo hWarp he hf hi hj
    · exact hAgree (Nat.le_of_not_gt hLo) hHi hWarp he hf hi hj
  · intro g h i j k hHi hWarp hk
    by_cases hLo : warpIndex l g < 8
    · exact hSoftmax.exitCoverage hLo hWarp hk
    · have hCorr := Nat.le_of_not_gt hLo
      exact correctionTensorPeerCoversOfAgreement hp hX hWarp hCorr hHi hk
        (hAgree hCorr hHi hWarp)

end PTX.Kernels.TmlFa4Fwd.Thread
