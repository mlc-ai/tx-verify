-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedQueryOperand
import Kernels.TmlFa4Fwd.Proof.Protocol.BiasWriteReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOperandBanks
import Kernels.TmlFa4Fwd.Proof.InputActualSources
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryUniqueness
import Lemmas.Tensor.TensorTransfer
import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy Protocol
open PTX.Kernels.TmlFa4Fwd.Mma (qStart)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem queryBoxRange (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {s : TensorCopy.Spec} {stage plane : Fin 2} {x y k : Nat} {loc : Loc}
    (h : Thread.Loader.QuerySubbox p l X i stage plane s)
    (hl : TensorCopy.writeLoc s x y k = some loc) :
    qStart l stage + 16384 * plane.val ≤ loc.addr ∧
      loc.addr < qStart l stage + 16384 * (plane.val + 1) := by
  obtain ⟨hLo,hHi⟩ := actualTensorInputByteWithinBox hp hX h.1 hl
  rw [h.2.2.1] at hLo hHi
  change qStart l stage + 16384 * plane.val ≤ loc.addr at hLo
  change loc.addr < qStart l stage + 16384 * plane.val + 16384 at hHi
  exact ⟨hLo, by simpa only [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc] using hHi⟩

private theorem biasBoxRange (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {s : TensorCopy.Spec} {stage half : Fin 2} {x y k : Nat} {loc : Loc}
    (h : Thread.Loader.BiasSubbox p l X i stage half s)
    (hl : TensorCopy.writeLoc s x y k = some loc) :
    l.sharedBase + 166912 + 32768 * stage.val + 16384 * half.val ≤ loc.addr ∧
      loc.addr < l.sharedBase + 166912 + 32768 * stage.val + 16384 * (half.val + 1) := by
  obtain ⟨hLo,hHi⟩ := actualTensorInputByteWithinBox hp hX h.1 hl
  rw [h.2.2.1] at hLo hHi
  change l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) ≤ loc.addr at hLo
  change loc.addr < l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) + 16384 at hHi
  omega

private theorem sharedSubboxCoordinates {base address : Nat} {stage plane stage' plane' : Fin 2}
    (ha : base + 32768 * stage.val + 16384 * plane.val ≤ address)
    (hb : address < base + 32768 * stage.val + 16384 * (plane.val + 1))
    (hc : base + 32768 * stage'.val + 16384 * plane'.val ≤ address)
    (hd : address < base + 32768 * stage'.val + 16384 * (plane'.val + 1)) :
    stage = stage' ∧ plane = plane' := by
  have := plane.isLt
  have := plane'.isLt
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private theorem inputWriteCta {X : Execution} {i : EvId} {address x y k : Nat}
    {s : TensorCopy.Spec} {loc : Loc} {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hi : X.TensorIssue i address s) (h : TensorCopy.writeLoc s x y k = some loc) :
    loc.cta = i.1 / l.block := by
  obtain ⟨slot,_,rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨_,_,_,_,hl⟩ := actualTensorInputSharedFrame hp hX hi slot
  exact congrArg Loc.cta hl

/-- When a pending input write covers an MMA operand byte, it belongs to the query
subbox observed by that issued MMA's actual acquire. -/
theorem tensorInputBeforeMmaRead (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {tensor mma : EvId} {x y k index : Nat} {isB : Bool} {a b : Acc} {loc : Loc}
    (hInput : X.AsyncFootprint tensor (.write (.load x y k)) a)
    (hRead : X.AsyncFootprint mma (.mmaRead isB index) b) (ha : a.Covers loc) (hb : b.Covers loc) :
    ByteCausality l X loc (.async tensor (.write (.load x y k)))
      (.async mma (.mmaRead isB index)) := by
  obtain ⟨s,address,hi,hLoc,hSize⟩ := hInput
  rw [Acc.loc_of_one ha hSize] at hLoc
  obtain ⟨hReadSize,hReadLoc⟩ := hRead
  rw [Acc.loc_of_one hb hReadSize] at hReadLoc
  obtain ⟨hRange,hCache | hQuery⟩ := Thread.sharedMmaOperandBank hp hX hReadLoc
  · rcases tensorInputWriteLocOutsideKv hp hX hi hLoc with hLow | hHigh
    · omega
    · have := hRange.upper
      omega
  obtain ⟨stage,plane,wait,e,d,op,accum,mask,rfl,hMma,hByte,hLo,hHi,hGet,hKind,hEarlier⟩ := hQuery
  rcases Thread.Loader.tensorInputSubbox hp hX hi with ⟨stage',plane',hInputBox⟩ |
      ⟨stage',half,hBias⟩
  · obtain ⟨hInputLo,hInputHi⟩ := queryBoxRange hp hX hInputBox hLoc
    have hCoords : stage = stage' ∧ plane = plane' := by
      simp only [qStart] at hLo hHi hInputLo hInputHi
      exact sharedSubboxCoordinates hLo hHi hInputLo hInputHi
    obtain ⟨rfl,rfl⟩ := hCoords
    have hCta : tensor.1 / l.block = wait.1 / l.block := by
      rw [hEarlier.1]
      exact (inputWriteCta hp hX hi hLoc).symm.trans hRange.cta
    obtain ⟨hWait,phase,_,hPhase⟩ := queryAcquirePhaseOfZero hp hX ⟨e,hGet,hKind⟩
    obtain ⟨selected,_,hSelectedCta,hSelected,hNotify⟩ :=
      hWait.observedSubbox hp hX hPhase plane
    have hEq := Thread.Loader.querySubboxUnique hp hX
      (hCta.trans hSelectedCta.symm) hInputBox hSelected
    subst selected
    have hObject := hInputBox.2.1
    rw [hCta] at hObject
    exact .direct
      (queryBeforeOperand hp hX hi hObject hWait hPhase hNotify hEarlier hLoc hMma hByte)
  · have hBiasLo := (biasBoxRange hp hX hBias hLoc).1
    have := hRange.upper
    omega

private theorem sameSlotOfWriteLoc {s : TensorCopy.Spec} {loc : Loc}
    {x y k x' y' k' : Nat}
    (ha : TensorCopy.writeLoc s x y k = some loc)
    (hb : TensorCopy.writeLoc s x' y' k' = some loc) : x = x' ∧ y = y' ∧ k = k' := by
  unfold TensorCopy.writeLoc at ha hb
  obtain ⟨a,hSlotA,hLocA⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨b,hSlotB,hLocB⟩ := Option.map_eq_some_iff.mp hb
  have hByte := congrArg Loc.addr (hLocA.trans hLocB.symm)
  have hEq := TensorTransfer.sharedByte_injective s.descriptor s.sharedBase.addr hByte
  subst b
  obtain ⟨hx,hy,hk⟩ := TensorCopy.slotAt_coordinates hSlotA
  obtain ⟨hx',hy',hk'⟩ := TensorCopy.slotAt_coordinates hSlotB
  exact ⟨hx.symm.trans hx', hy.symm.trans hy', hk.symm.trans hk'⟩

private theorem sameInputWriteRef {X : Execution} {i j : EvId}
    {address address' x y k x' y' k' : Nat} {s t : TensorCopy.Spec} {loc : Loc}
    (hSame : i = j) (hi : X.TensorIssue i address s) (hj : X.TensorIssue j address' t)
    (ha : TensorCopy.writeLoc s x y k = some loc) (hb : TensorCopy.writeLoc t x' y' k' = some loc) :
    Ref.async i (.write (.load x y k)) = Ref.async j (.write (.load x' y' k')) := by
  subst j
  obtain ⟨_,hE⟩ := hi
  obtain ⟨_,hE'⟩ := hj
  obtain ⟨_,rfl⟩ :=
    Kind.tensorIssue.inj (congrArg Event.kind (Option.some.inj (hE.symm.trans hE')))
  obtain ⟨rfl,rfl,rfl⟩ := sameSlotOfWriteLoc ha hb
  rfl

/-- Two input transfers sharing a destination byte are either the same effect or two
visits of the same physical Bias half. The single-use query subboxes have one writer. -/
theorem overlappingTensorInputs (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {x y k x' y' k' : Nat} {a b : Acc} {loc : Loc}
    (ha : X.AsyncFootprint i (.write (.load x y k)) a) (hA : a.Covers loc)
    (hb : X.AsyncFootprint j (.write (.load x' y' k')) b) (hB : b.Covers loc) :
    Ref.async i (.write (.load x y k)) = Ref.async j (.write (.load x' y' k')) ∨
      ∃ (stage half : Fin 2) (s t : TensorCopy.Spec),
        Thread.Loader.BiasSubbox p l X i stage half s ∧
        Thread.Loader.BiasSubbox p l X j stage half t ∧
        TensorCopy.writeLoc s x y k = some loc ∧ TensorCopy.writeLoc t x' y' k' = some loc := by
  obtain ⟨s,addr,hi,hl,hSize⟩ := ha
  obtain ⟨t,addr',hj,hl',hSize'⟩ := hb
  rw [Acc.loc_of_one hA hSize] at hl
  rw [Acc.loc_of_one hB hSize'] at hl'
  have hCta := (inputWriteCta hp hX hi hl).symm.trans (inputWriteCta hp hX hj hl')
  rcases Thread.Loader.tensorInputSubbox hp hX hi with ⟨stage,plane,hQuery⟩ | ⟨stage,half,hBias⟩
  · obtain ⟨hLo,hHi⟩ := queryBoxRange hp hX hQuery hl
    rcases Thread.Loader.tensorInputSubbox hp hX hj with
      ⟨stage',plane',hQuery'⟩ | ⟨stage',half',hBias'⟩
    · obtain ⟨hLo',hHi'⟩ := queryBoxRange hp hX hQuery' hl'
      simp only [qStart] at hLo hHi hLo' hHi'
      obtain ⟨rfl,rfl⟩ := sharedSubboxCoordinates hLo hHi hLo' hHi'
      exact .inl (sameInputWriteRef
        (Thread.Loader.querySubboxUnique hp hX hCta hQuery hQuery') hi hj hl hl')
    · have hBiasLo := (biasBoxRange hp hX hBias' hl').1
      have hStage := stage.isLt
      have hPlane := plane.isLt
      simp only [qStart] at hHi
      omega
  · obtain ⟨hLo,hHi⟩ := biasBoxRange hp hX hBias hl
    rcases Thread.Loader.tensorInputSubbox hp hX hj with
      ⟨stage',plane',hQuery'⟩ | ⟨stage',half',hBias'⟩
    · have hQueryHi := (queryBoxRange hp hX hQuery' hl').2
      have hStage := stage'.isLt
      have hPlane := plane'.isLt
      simp only [qStart] at hQueryHi
      omega
    · obtain ⟨hLo',hHi'⟩ := biasBoxRange hp hX hBias' hl'
      obtain ⟨rfl,rfl⟩ := sharedSubboxCoordinates hLo hHi hLo' hHi'
      exact .inr ⟨stage,half,s,t,hBias,hBias',hl,hl'⟩

/-- Every two distinct tensor input write intents that share a byte are ordered. -/
theorem tensorInputWritesOrdered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {x y k x' y' k' : Nat} {a b : Acc} {loc : Loc}
    (ha : X.AsyncFootprint i (.write (.load x y k)) a) (hA : a.Covers loc)
    (hb : X.AsyncFootprint j (.write (.load x' y' k')) b) (hB : b.Covers loc)
    (hNe : Ref.async i (.write (.load x y k)) ≠ Ref.async j (.write (.load x' y' k'))) :
    ByteCausality l X loc (.async i (.write (.load x y k))) (.async j (.write (.load x' y' k'))) ∨
      ByteCausality l X loc (.async j (.write (.load x' y' k')))
        (.async i (.write (.load x y k))) := by
  rcases overlappingTensorInputs hp hX ha hA hb hB with hEq |
    ⟨stage,half,s,t,hEarly,hLater,hLocA,hLocB⟩
  · exact (hNe hEq).elim
  have hCta := (inputWriteCta hp hX hEarly.1 hLocA).symm.trans (inputWriteCta hp hX hLater.1 hLocB)
  have hOrd : Thread.Loader.biasTensorOrdinal l X stage half i ≠
      Thread.Loader.biasTensorOrdinal l X stage half j := by
    intro hEq
    have hSame := Thread.Loader.biasTensorOrdinalInjective hp hX hEarly hLater hCta hEq
    exact hNe (sameInputWriteRef hSame hEarly.1 hLater.1 hLocA hLocB)
  let ownA : AsyncCovers X i (.write (.load x y k)) loc := ⟨a,true,⟨rfl,ha⟩,hA⟩
  let ownB : AsyncCovers X j (.write (.load x' y' k')) loc := ⟨b,true,⟨rfl,hb⟩,hB⟩
  rcases Nat.lt_or_gt_of_ne hOrd with h | h
  · exact .inl (Bias.biasWriteBeforeReuse hp hX hEarly hLater hCta h ownA ownB)
  · exact .inr (Bias.biasWriteBeforeReuse hp hX hLater hEarly hCta.symm h ownB ownA)

end PTX.Kernels.TmlFa4Fwd.Safety
