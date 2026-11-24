-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Flow.Sites.Part000
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.NotWait
import Lemmas.Flow.NotBulk
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.PollFacts
public import Lemmas.Order.GuardSnoc
public import Tactics.KernelRfl

@[expose] public section

/-! # Every poll of the kernel is a canonical spin

The decoded code has 48 `mbarrier.try_wait` instructions, each at the head of a wait loop no branch
enters, whose predicate is read by the loop's branch alone. The code is scanned once per group of
eight polls. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Flow

private def isMbarPoll : Op → Bool
  | .mbarWait .. => true
  | _ => false

private theorem checkedPollSites :
    OpPcsFast kernel.code isMbarPoll Flow.mbarWait.toList = true := by
  decide +kernel

private def protectedPollPcs : List Nat :=
  Flow.mbarWait.toList.flatMap (fun pc => [pc + 1, pc + 2])

private def avoidsPollInterior (op : Op) : Bool :=
  match op with
  | .bra tgt _ => !protectedPollPcs.contains tgt
  | .brx .. => false
  | _ => true

set_option maxRecDepth 100000 in
private theorem protectedPollPcs_checked :
    kernel.code.all (fun i => avoidsPollInterior i.op) = true := by
  kernel_rfl

private theorem protectedPollPcs_notTargeted {pc : Nat} (hp : pc ∈ protectedPollPcs) :
    kernel.targeted pc = false := by
  unfold Kernel.targeted
  apply List.any_eq_false.mpr
  intro ins hi
  have h := List.all_eq_true.mp protectedPollPcs_checked ins hi
  cases ho : ins.op with
  | bra target uni =>
    simp only [avoidsPollInterior, ho] at h
    by_cases he : target = pc
    · subst target
      have hNot : pc ∉ protectedPollPcs := by simpa using h
      exact (hNot hp).elim
    · simpa [ho, beq_iff_eq] using he
  | brx ra targets uni => simp [avoidsPollInterior, ho] at h
  | _ => simp

private def rawPollExit (pc : Nat) : Option Nat :=
  match kernel.pollDst pc, kernel.code[pc + 1]?, kernel.code[pc + 2]? with
  | some p, some ⟨some (q, false), .bra ex _⟩, some ⟨none, .bra back _⟩ =>
    if q == p && back == pc && (ex < pc || pc + 2 < ex) then some ex else none
  | some p, some ⟨some (q, true), .bra back _⟩, _ =>
    if q == p && back == pc then some (pc + 2) else none
  | _, _, _ => none

private theorem rawPollExit_eq {pc : Nat} (hp : pc ∈ Flow.mbarWait.toList) :
    rawPollExit pc = kernel.spinExit? pc := by
  have h1 := protectedPollPcs_notTargeted
    (show pc + 1 ∈ protectedPollPcs from List.mem_flatMap.mpr ⟨pc, hp, by simp⟩)
  have h2 := protectedPollPcs_notTargeted
    (show pc + 2 ∈ protectedPollPcs from List.mem_flatMap.mpr ⟨pc, hp, by simp⟩)
  unfold rawPollExit Kernel.spinExit?
  split <;> simp_all [Bool.and_assoc]

private def canonicalPoll (pc : Nat) : Bool :=
  (rawPollExit pc).isSome && (kernel.pollDst pc).any (fun p => decide (9500 ≤ p))

private def pollGroup (i : Nat) : List Nat := (Flow.mbarWait.toList.drop (8 * i)).take 8

set_option maxRecDepth 100000 in
private theorem checkedPollGroup0 : (pollGroup 0).all canonicalPoll = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedPollGroup1 : (pollGroup 1).all canonicalPoll = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedPollGroup2 : (pollGroup 2).all canonicalPoll = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedPollGroup3 : (pollGroup 3).all canonicalPoll = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedPollGroup4 : (pollGroup 4).all canonicalPoll = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem checkedPollGroup5 : (pollGroup 5).all canonicalPoll = true := by
  kernel_rfl

private theorem checkedPollShapes : Flow.mbarWait.toList.all canonicalPoll = true := by
  have h : Flow.mbarWait.toList =
      pollGroup 0 ++ pollGroup 1 ++ pollGroup 2 ++ pollGroup 3 ++ pollGroup 4 ++ pollGroup 5 := by
    decide +kernel
  rw [h]
  simp only [List.all_append, checkedPollGroup0, checkedPollGroup1, checkedPollGroup2,
    checkedPollGroup3, checkedPollGroup4, checkedPollGroup5, Bool.and_self]

private def pollPredicates : List Nat :=
  [9606, 9607, 9608, 9609, 9610, 9611, 9612, 9613, 9614, 9615, 9616, 9617, 9618, 9619, 9620,
    9621, 9622, 9634, 9635, 9652, 9669, 9670, 9680, 9681, 9698, 9708, 9725, 9726, 9736,
    9737, 9747, 9748, 9749, 9750, 9751, 9752, 9753, 9754, 9755, 9820, 9821, 9886, 9887,
    9888, 9889, 9890, 9891, 9892]

private theorem pollPredicates_eq : Flow.mbarWait.toList.filterMap kernel.pollDst =
    pollPredicates := by
  kernel_rfl

private def instrInputs (ins : Instr) : Option (List Nat) :=
  ins.op.readRegs.map (fun regs => (ins.guard.toList.map Prod.fst) ++ regs)

private def checkedPollRead (p i : Nat) : Bool :=
  if 9500 ≤ p ∧ pollPredicates.contains p then
    decide (1 ≤ i) && Flow.mbarWait.toList.contains (i - 1) && kernel.pollDst (i - 1) == some p
  else true

private def checkedPollInputs (pair : Instr × Nat) : Bool :=
  (instrInputs pair.1).any (fun rs => rs.all (checkedPollRead · pair.2))

set_option maxRecDepth 100000 in
private theorem allPollInputsChecked : kernel.code.zipIdx.all checkedPollInputs = true := by
  kernel_rfl

private theorem spinPredOfChecked {pc p : Nat} (hs : pc ∈ Flow.mbarWait.toList)
    (hDst : kernel.pollDst pc = some p) (hBound : 9500 ≤ p) : kernel.SpinPred p := by
  have hPred : p ∈ pollPredicates := pollPredicates_eq ▸ List.mem_filterMap.mpr ⟨pc, hs, hDst⟩
  have hContains : pollPredicates.contains p = true := List.contains_iff_mem.mpr hPred
  apply List.all_eq_true.mpr
  rintro ⟨ins, i⟩ hi
  have hAll := List.all_eq_true.mp allPollInputsChecked (ins, i) hi
  cases hr : ins.op.readRegs with
  | none => simp [checkedPollInputs, instrInputs, hr] at hAll
  | some rs =>
    simp only [checkedPollInputs, instrInputs, hr, Option.map_some, Option.any_some] at hAll
    by_cases hUses : ins.readsReg p = true
    · have hMem : p ∈ ins.guard.toList.map Prod.fst ++ rs := by
        simp only [Instr.readsReg, hr, Option.map_some, Option.getD_some,
          Bool.or_eq_true] at hUses
        apply List.mem_append.mpr
        rcases hUses with hG | hR
        · left
          cases hh : ins.guard with
          | none => simp [hh] at hG
          | some gp =>
            have he : gp.1 = p := by simpa [hh] using hG
            simp [he]
        · exact .inr (List.contains_iff_mem.mp hR)
      have h := List.all_eq_true.mp hAll p hMem
      simp only [checkedPollRead, hBound, hContains, and_self, ↓reduceIte, Bool.and_eq_true] at h
      have hp := List.contains_iff_mem.mp h.1.2
      have hAt := List.all_eq_true.mp checkedPollShapes (i - 1) hp
      simp only [canonicalPoll, Bool.and_eq_true] at hAt
      have hExit : (kernel.spinExit? (i - 1)).isSome = true := by
        rw [← rawPollExit_eq hp]
        exact hAt.1
      simp only [hUses, Bool.not_true, Bool.false_or, Bool.and_eq_true]
      exact ⟨⟨h.1.1, hExit⟩, h.2⟩
    · simp [show ins.readsReg p = false by simpa using hUses]

variable {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}

/-- Every recorded poll comes from a decoded mbarrier wait. -/
private theorem actualMbarPollSite (hX : Consistent l kernel A m X) {i : EvId} {pc phase : Nat}
    {mb : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get i = some ⟨pc, .wait mb phase ok acq scope⟩) :
    pc ∈ Flow.mbarWait.toList := by
  rcases get_source hX he with ⟨_, hi⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hi
  have hs : isMbarPoll ins.op = true := by
    by_contra hn
    have hw : ∀ p b off par a sc, ins.op ≠ .mbarWait p b off par a sc := by
      intro p b off par a sc ho
      exact hn (ho.symm ▸ rfl)
    exact fires_notWait (eventTmpl_notWait hw) hf mb phase ok acq scope rfl
  exact OpPcsFast.mem checkedPollSites hc hs

/-- Every actual wait executes a canonical spin, with the result predicate consumed at its exit
branch. The audit is over all wait instructions in the decoded kernel. -/
theorem poll_canonical (hX : Consistent l kernel A m X) {i : EvId} {pc phase : Nat} {mb : Loc}
    {ok acq : Bool} {scope : MbarScope} (he : X.get i = some ⟨pc, .wait mb phase ok acq scope⟩) :
    ∃ next, kernel.CanonicalSpin pc next := by
  have hSite := actualMbarPollSite hX he
  have hShape := List.all_eq_true.mp checkedPollShapes pc hSite
  simp only [canonicalPoll, Bool.and_eq_true] at hShape
  obtain ⟨ex, hEx⟩ := Option.isSome_iff_exists.mp hShape.1
  cases hp : kernel.pollDst pc with
  | none => simp [hp] at hShape
  | some p =>
    exact ⟨ex, (rawPollExit_eq hSite).symm.trans hEx, p, hp,
      spinPredOfChecked hSite hp (by simpa [hp] using hShape.2)⟩

end PTX.Kernels.TmlFa4Fwd.Proof
