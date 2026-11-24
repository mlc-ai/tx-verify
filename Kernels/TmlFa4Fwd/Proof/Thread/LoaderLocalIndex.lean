-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalFixed
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

/-- A scratch loop always sets its index to zero on entry and to one on its backedge. -/
structure TwoEntryLoop where
  first : Nat
  second : Nat
  last : Nat
  reg : Nat
  wide : Bool
  deriving DecidableEq

def scratchLoops : List TwoEntryLoop :=
  [⟨486, 512, 514, 7172, false⟩, ⟨919, 954, 956, 7175, false⟩,
   ⟨1399, 1424, 1426, 7182, false⟩, ⟨520, 535, 537, 9535, true⟩,
   ⟨785, 800, 802, 9536, true⟩, ⟨963, 978, 980, 9537, true⟩,
   ⟨1209, 1224, 1226, 9538, true⟩, ⟨1433, 1448, 1450, 9539, true⟩,
   ⟨1614, 1629, 1631, 9540, true⟩]

def TwoEntryLoop.active (b : TwoEntryLoop) (pc : Nat) : Prop :=
  b.first < pc ∧ pc ≤ b.last

instance (b : TwoEntryLoop) (pc : Nat) : Decidable (b.active pc) :=
  inferInstanceAs (Decidable (b.first < pc ∧ pc ≤ b.last))

def TwoEntryLoop.value (b : TwoEntryLoop) (entry : Fin 2) : Value :=
  if b.wide then b64 entry.val else b32 entry.val

def indexInvariant (s : TState) : Prop :=
  ∀ b ∈ scratchLoops, b.active s.pc → ∃ entry, s.regs b.reg = some (b.value entry)

theorem indexInitial {s : TState} (hs : s.pc = 174) : indexInvariant s := by
  intro b hb ha
  rw [hs] at ha
  simp only [scratchLoops, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> contradiction

private def TwoEntryLoop.move (b : TwoEntryLoop) (entry : Fin 2) : MoveInstr :=
  ⟨.scalar, .int .b (if b.wide then 64 else 32), [some b.reg], [.imm entry.val]⟩

private def checkedIndexStep (pc : Nat) (i : Instr) : Bool :=
  scratchLoops.all fun b =>
    (if pc == b.first then i.guard.isNone &&
        (match i.op with | .move mv => decide (mv = b.move 0) | _ => false)
     else if pc == b.second then i.guard.isNone &&
        (match i.op with | .move mv => decide (mv = b.move 1) | _ => false)
     else !decide (b.active pc) || !(Loader.loaderRingWrites i.op).contains b.reg) &&
    (match i.op with
    | .bra target _ => !decide (b.active target) || decide (b.active pc)
    | .brx .. => false
    | _ => true)

private theorem checkedIndexAt {pc : Nat} {i : Instr} (hLo : 174 ≤ pc) (hHi : pc < 1901)
    (hc : kernel.code[pc]? = some i) (b : TwoEntryLoop) (hb : b ∈ scratchLoops) :
    (if pc == b.first then i.guard.isNone &&
        (match i.op with | .move mv => decide (mv = b.move 0) | _ => false)
     else if pc == b.second then i.guard.isNone &&
        (match i.op with | .move mv => decide (mv = b.move 1) | _ => false)
     else !decide (b.active pc) || !(Loader.loaderRingWrites i.op).contains b.reg) &&
    (match i.op with
    | .bra target _ => !decide (b.active target) || decide (b.active pc)
    | .brx .. => false
    | _ => true) = true := by
  let code := ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174
  have hAudit : code.all (fun (ins, site) => checkedIndexStep site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : (i, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - 174)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp (List.all_eq_true.mp hAudit (i, pc) hm) b hb

private theorem isIndexMove {i : Instr} {b : TwoEntryLoop} {entry : Fin 2}
    (h : (i.guard.isNone &&
      (match i.op with | .move mv => decide (mv = b.move entry) | _ => false)) = true) :
    i = ⟨none, .move (b.move entry)⟩ := by
  obtain ⟨guard, op⟩ := i
  obtain ⟨hg, ho⟩ := Bool.and_eq_true_iff.mp h
  have hNone : guard = none := Option.isNone_iff_eq_none.mp hg
  subst guard
  cases op <;> simp_all

private theorem indexMoveValue {l : Launch} {g : Nat} {s u : TState} {b : TwoEntryLoop}
    (entry : Fin 2) (hf : s.fault = none)
    (hc : kernel.code[s.pc]? = some ⟨none, .move (b.move entry)⟩)
    (ht : Tau kernel [] l g s u) : u.regs b.reg = some (b.value entry) := by
  have hLocal : (Op.move (b.move entry)).isLocal = true := by
    cases b.wide <;> rfl
  have hExec : execLocalA [] l g s (.move (b.move entry)) =
      .ok (next (setReg s b.reg (b.value entry))) := by
    have hRule : (b.move entry).rule = some .threadMove := by
      cases hw : b.wide <;> simp only [TwoEntryLoop.move, hw, ↓reduceIte, Bool.false_eq_true]
      all_goals rfl
    rw [execLocalA_nil, execLocal_move hRule]
    cases hw : b.wide <;> fin_cases entry <;>
      simp only [TwoEntryLoop.move, TwoEntryLoop.value, hw, Bool.false_eq_true, ↓reduceIte]
    all_goals simp only [execMove, readValue, readBits, DType.width,
      bind, Except.bind, pure, Except.pure, Value.bytes, ↓reduceIte]
    all_goals rfl
  simp only [Tau, out, hf, hc, guardHolds, pure, Except.pure, hLocal, ↓reduceIte, hExec] at ht
  obtain rfl := Out.tau.inj ht.symm
  exact Function.update_self _ _ _

/-- The two literal assignments and the checked backedges preserve the bounded index. -/
theorem indexStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hInv : indexInvariant s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    indexInvariant u := by
  intro b hb hActive
  have hFall (h : u.pc = s.pc + 1) : s.pc = b.first ∨ b.active s.pc := by
    unfold TwoEntryLoop.active at hActive ⊢
    omega
  have hPreserve (hFirst : s.pc ≠ b.first) (hSecond : s.pc ≠ b.second)
      (hLive : b.active s.pc) : ∃ e, u.regs b.reg = some (b.value e) := by
    obtain ⟨e, he⟩ := hInv b hb hLive
    refine ⟨e, (Loader.loaderPipelineStepRegs hLo hHi ?_ hStep).trans he⟩
    intro i hc
    have h := (Bool.and_eq_true_iff.mp (checkedIndexAt hLo hHi hc b hb)).1
    simpa [hFirst, hSecond, hLive] using h
  rcases hStep with ⟨rfl, ht⟩ | ⟨real, rfl, he⟩
  · have ht' : Tau kernel [] l g s u := by
      unfold Tau at ht ⊢
      rwa [← Loader.loaderOutCore hLo (by omega)]
    obtain ⟨i, hc, hf, _⟩ := Softmax.tauScoreSource ht
    obtain ⟨hDef, hBranch⟩ := Bool.and_eq_true_iff.mp (checkedIndexAt hLo hHi hc b hb)
    by_cases hFirst : s.pc = b.first
    · have hMove : i = ⟨none, .move (b.move 0)⟩ :=
        isIndexMove (by simpa [hFirst] using hDef)
      rw [hMove] at hc
      exact ⟨0, indexMoveValue 0 hf hc ht'⟩
    by_cases hSecond : s.pc = b.second
    · have hMove : i = ⟨none, .move (b.move 1)⟩ :=
        isIndexMove (by simpa [hFirst, hSecond, show b.second ≠ b.first by omega] using hDef)
      rw [hMove] at hc
      exact ⟨1, indexMoveValue 1 hf hc ht'⟩
    apply hPreserve hFirst hSecond
    rcases tau_core_frame hc ht' with rfl | hFrame
    · exact (hFall rfl).resolve_left hFirst
    · have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra target uni =>
        rw [hPc] at hActive
        simpa [ho, hActive] using hBranch
      case brx => simp [ho] at hBranch
      all_goals exact (hFall hPc).resolve_left hFirst
  · obtain ⟨i, hc, hl, _⟩ := estep_event_source he
    have hDef := (Bool.and_eq_true_iff.mp (checkedIndexAt hLo hHi hc b hb)).1
    have hFirst : s.pc ≠ b.first := by
      intro h
      have hi : i = ⟨none, .move (b.move 0)⟩ := isIndexMove (by simpa [h] using hDef)
      rw [hi] at hl
      cases b.wide <;> cases hl
    have hSecond : s.pc ≠ b.second := by
      intro h
      have hi : i = ⟨none, .move (b.move 1)⟩ := isIndexMove
        (by simpa [hFirst, h, show b.second ≠ b.first by omega] using hDef)
      rw [hi] at hl
      cases b.wide <;> cases hl
    apply hPreserve hFirst hSecond
    have he' : EStep kernel [] l g s real (some u) := by
      obtain ⟨tmpl, ho, hf⟩ := he
      exact ⟨tmpl, by rwa [← Loader.loaderOutCore hLo (by omega)], hf⟩
    rcases (estep_return_pc he' (fun _ _ _ h => execLocal_frame h)).2 with h | h
    · exact h ▸ hActive
    · exact (hFall h).resolve_left hFirst

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader.LocalAccessCode
