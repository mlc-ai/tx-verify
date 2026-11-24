-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxCreditReuse
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopOrdinal
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part053
import Kernels.TmlFa4Fwd.Flow.Code.Part076
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part103
import Kernels.TmlFa4Fwd.Flow.Code.Part118

@[expose] public section

noncomputable section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

variable (score : Bool)

private def nodes (score : Bool) : List (Fin 10) :=
  if score then [1, 4, 7] else [0, 3, 6, 8, 9]

private def checkIndex (pc : Nat) : Option (Fin 10) :=
  (nodes score).find? (fun i => (waitSite i).pc + 1 == pc)

private def retryIndex (pc : Nat) : Option (Fin 10) :=
  (nodes score).find? (fun i => (waitSite i).pc + 2 == pc)

private def pollIndex (pc : Nat) : Option (Fin 10) :=
  (nodes score).find? (fun i => (waitSite i).pc == pc)

private abbrev phaseWord (s : TState) (r : Nat) (b : Bool) : Prop :=
  s.regs r = some (b32 b.toNat)

-- The latch retains the old phase between a successful poll and the loop's toggle.
-- The first two polls use separate phase words, and the reinitialization path copies 7253.
private def expected (score : Bool) (pc : Nat) (bit : Bool) : List (Nat × Bool) :=
  if score then
    (if 3425 ≤ pc && pc ≤ 3427 then [(2770, false)] else []) ++
    (if pc = 5023 then [(7258, true)] else []) ++
    (if 5024 ≤ pc && pc ≤ 7604 then
      [(7253, if (5112 ≤ pc && pc ≤ 6649) || (6679 ≤ pc && pc ≤ 7599)
        then bit else !bit)]
      else [])
  else
    (if pc ≤ 3283 then [] else
      [(7258, if (3423 ≤ pc && pc ≤ 4876) || (6561 ≤ pc && pc ≤ 6647) ||
          (7466 ≤ pc && pc ≤ 7600) || 7741 ≤ pc then bit else !bit)]) ++
    (if 3420 ≤ pc && pc ≤ 3422 then [(2768, true)] else []) ++
    (if 4874 ≤ pc && pc ≤ 4876 then [(3949, false)] else []) ++
    (if 5028 ≤ pc && pc ≤ 5030 then [(7253, true)] else [])

private def fixedBit (score : Bool) (pc : Nat) : Option Bool :=
  if score then
    if pc ≤ 3427 then some true
    else if pc ≤ 5031 then some false
    else none
  else if pc ≤ 3422 then some false
  else if pc ≤ 4876 then some true
  else if pc ≤ 5031 then some false
  else none

private def beforeStep (s : TState) (bit : Bool) (pc : Nat) : Prop :=
  (∀ b, fixedBit score pc = some b → bit = b) ∧
    ∀ w ∈ expected score pc bit, phaseWord s w.1 w.2

private def phaseInvariant (s : TState) (bit : Bool) : Prop :=
  3103 ≤ s.pc ∧ s.pc ≤ 7742 ∧ s.sub ≤ 3 ∧
    match checkIndex score s.pc with
    | none => beforeStep score s bit s.pc
    | some i => ∃ passed, s.regs (waitSite i).result = some (.pred passed) ∧
        beforeStep score s (bit ^^ passed) (waitSite i).pc

private inductive WordUpdate
  | keep
  | put (r : Nat) (b : Bool)
  | flip (r : Nat)
  deriving DecidableEq

private def updateSites (score : Bool) : List (Nat × WordUpdate) :=
  if score then
    [(3424, .put 2770 false), (5022, .put 7258 true), (5023, .put 7253 true),
      (5027, .put 7253 true), (6649, .flip 7253), (7599, .flip 7253)]
  else [(3283, .put 7258 true), (3419, .put 2768 true), (4873, .put 3949 false),
   (5022, .put 7258 true), (5027, .put 7253 true), (5030, .put 7258 true),
   (6647, .flip 7258), (7600, .flip 7258)]

private def updateOf (pc : Nat) : WordUpdate :=
  (((updateSites score).find? (fun entry => entry.1 == pc)).map Prod.snd).getD .keep

private def modifies (up : WordUpdate) : Option Nat :=
  match up with
  | .keep => none
  | .put r _ | .flip r => some r

private def provides (up : WordUpdate) (before : List (Nat × Bool)) (word : Nat × Bool) : Bool :=
  match up with
  | .keep => before.contains word
  | .put r b => if word.1 == r then word.2 == b else before.contains word
  | .flip r => before.contains (word.1, word.2 ^^ (word.1 == r))

private def activeBits (pc : Nat) : List Bool :=
  (fixedBit score pc).elim [false,true] List.singleton

private def validOrdinary (pc next : Nat) (up : WordUpdate) : Bool :=
  (3103 ≤ next && next ≤ 7742) && (checkIndex score next).isNone &&
    (activeBits score pc).all fun b =>
      (fixedBit score next).all (· == b) &&
        (expected score next b).all (provides up (expected score pc b))

private def readRegEffect (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def tracked (score : Bool) : List Nat :=
  if score then [2770, 7253, 7258] else [2768, 3949, 7253, 7258]

private def nonSpinCode (pc : Nat) (i : Instr) : Bool :=
  let up := updateOf score pc
  let noOther := (expected score pc false ++ expected score pc true).all
    (fun w => modifies up == some w.1 || !(readRegEffect i.op).contains w.1)
  (i.op.isLocal || scoreEventOp i.op) && noOther &&
  match i.op with
  | .brx .. => false
  | .bra dst _ => validOrdinary score pc dst up &&
      (i.guard.isNone || validOrdinary score pc (pc + 1) up)
  | _ => validOrdinary score pc (pc+1) up

private def spinPc (pc : Nat) : Bool :=
  (pollIndex score pc).isSome || (checkIndex score pc).isSome || (retryIndex score pc).isSome

-- Check every ordinary successor, including both sides of each predicated branch.
private theorem creditPhaseCode :
    (((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103).all
      (fun e => spinPc score e.2 || nonSpinCode score e.2 e.1) = true := by
  cases score <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem rollTransition :
    (nodes score).all (fun i => validOrdinary score (waitSite i).pc ((waitSite i).pc + 2) .keep &&
      validOrdinary score ((waitSite i).pc + 2) (waitSite i).pc .keep &&
      (activeBits score (waitSite i).pc).all (fun b =>
        (fixedBit score ((waitSite i).pc + 3)).all (· == !b) &&
        (expected score ((waitSite i).pc + 3) (!b)).all
          (provides .keep (expected score (waitSite i).pc b)) &&
        (expected score (waitSite i).pc b).contains ((waitSite i).phase, !b))) = true := by
  cases score <;> decide

private def exp2CreditFrame (pc : Nat) : Bool :=
  match cuteExp2.matchAt kernel pc with
  | none => false
  | some matchInfo =>
    validOrdinary score pc matchInfo.stop .keep &&
    (tracked score).all (fun r => !(scoreSegmentWrites matchInfo).contains r)

private theorem exp2CreditCode :
    Assumptions.swExp2Sites.all (exp2CreditFrame score) = true := by
  cases score <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem phaseCodeAt {pc : Nat} {i : Instr} (hLo : 3103 ≤ pc) (hHi : pc < 7742)
    (hc : kernel.code[pc]? = some i) :
    (spinPc score pc || nonSpinCode score pc i) = true := by
  apply List.all_eq_true.mp (creditPhaseCode score) (i,pc)
  apply List.mem_of_getElem? (i := pc-3103)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem bitPresent {s : TState} {bit : Bool} {pc : Nat}
    (hs : beforeStep score s bit pc) : bit ∈ activeBits score pc := by
  cases h : fixedBit score pc with
  | none => cases bit <;> simp [activeBits, h]
  | some b => rw [activeBits, h, hs.1 _ h]; exact List.mem_singleton_self _

private theorem fixedNextOfValid {s : TState} {bit : Bool} {pc dst : Nat} {up : WordUpdate}
    (hs : beforeStep score s bit pc) (hv : validOrdinary score pc dst up = true) :
    ((fixedBit score dst).all (· == bit)) = true ∧
      (expected score dst bit).all (provides up (expected score pc bit)) = true := by
  simp only [validOrdinary, Bool.and_eq_true] at hv
  have h := List.all_eq_true.mp hv.2 bit (bitPresent score hs)
  simpa only [Bool.and_eq_true] using h

private theorem claimOfValid {s u : TState} {bit : Bool} {pc : Nat} {up : WordUpdate}
    (hs : beforeStep score s bit pc) (hv : validOrdinary score pc u.pc up = true) (hSub : u.sub ≤ 3)
    (hRegs : ∀ w ∈ expected score u.pc bit, provides up (expected score pc bit) w = true →
      phaseWord u w.1 w.2) :
    phaseInvariant score u bit := by
  obtain ⟨hFixed, hExpected⟩ := fixedNextOfValid score hs hv
  simp only [validOrdinary, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hv
  refine ⟨hv.1.1.1, hv.1.1.2, hSub, ?_⟩
  rw [hv.1.2]
  refine ⟨fun b hb => ?_, fun w hw => hRegs w hw (List.all_eq_true.mp hExpected _ hw)⟩
  rw [hb] at hFixed
  have hEq : (b == bit) = true := hFixed
  exact (beq_iff_eq.mp hEq).symm

private theorem holdsKeep {s u : TState} {bit : Bool} {pc : Nat}
    (hs : beforeStep score s bit pc)
    (hKeep : ∀ w ∈ expected score pc bit, u.regs w.1 = s.regs w.1)
    (w : Nat × Bool) (hw : provides .keep (expected score pc bit) w = true) :
    phaseWord u w.1 w.2 := by
  have hm : w ∈ expected score pc bit := List.contains_iff_mem.mp hw
  unfold phaseWord
  exact (hKeep w hm).trans (hs.2 _ hm)

private theorem holdsPut {s u : TState} {bit b : Bool} {pc r : Nat}
    (hs : beforeStep score s bit pc)
    (hPut : phaseWord u r b)
    (hKeep : ∀ w ∈ expected score pc bit, w.1 ≠ r → u.regs w.1 = s.regs w.1)
    (w : Nat × Bool) (hw : provides (.put r b) (expected score pc bit) w = true) :
    phaseWord u w.1 w.2 := by
  by_cases he : w.1 = r
  · have h : w.2 = b := by
      simpa only [provides, he, beq_self_eq_true, ite_true, beq_iff_eq] using hw
    simpa only [he, h] using hPut
  · have hm : w ∈ expected score pc bit := by simpa [provides, he] using hw
    unfold phaseWord
    exact (hKeep w hm he).trans (hs.2 _ hm)

private theorem holdsFlip {s u : TState} {bit : Bool} {pc r : Nat}
    (hs : beforeStep score s bit pc)
    (hFlip : ∀ b, phaseWord s r b → phaseWord u r (!b))
    (hKeep : ∀ w ∈ expected score pc bit, w.1 ≠ r → u.regs w.1 = s.regs w.1)
    (w : Nat × Bool) (hw : provides (.flip r) (expected score pc bit) w = true) :
    phaseWord u w.1 w.2 := by
  by_cases he : w.1 = r
  · have hm : (w.1,!w.2) ∈ expected score pc bit := by
      have hh := List.contains_iff_mem.mp hw
      simpa [provides, he, Bool.xor_true] using hh
    have h := hFlip (!w.2) (by simpa only [he] using hs.2 _ hm)
    simpa only [he, Bool.not_not] using h
  · have hm : w ∈ expected score pc bit := by
      have hh := List.contains_iff_mem.mp hw
      have ht : (w.1 == r) = false := beq_eq_false_iff_ne.mpr he
      obtain ⟨r0,b0⟩ := w
      simpa only [ht, Bool.xor_false] using hh
    unfold phaseWord
    exact (hKeep w hm he).trans (hs.2 _ hm)

private def putWord (r : Nat) (a : Opnd) : Op :=
  .move ⟨.scalar, .int .b 32, [some r], [a]⟩

private theorem updateMembership {pc : Nat} (hPut : updateOf score pc ≠ .keep) :
    pc ∈ (updateSites score).map Prod.fst := by
  unfold updateOf at hPut
  cases h : (updateSites score).find? (fun entry => entry.1 == pc) with
  | none => simp only [h, Option.map_none, Option.getD_none, ne_eq, not_true_eq_false] at hPut
  | some v =>
    have hEq : v.1 = pc := beq_iff_eq.mp
      (List.find?_some (p := fun entry : Nat × WordUpdate => entry.1 == pc) h)
    exact List.mem_map.mpr ⟨v, List.mem_of_find?_eq_some h, hEq⟩

private theorem exactUpdate {pc : Nat} {i : Instr} (hc : kernel.code[pc]? = some i)
    (hPut : updateOf score pc ≠ .keep) : i.guard = none ∧ i.op.isLocal = true := by
  have h := updateMembership score hPut
  cases score
  · simp [updateSites] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rw [Flow.code_3283] at hc; cases hc; decide
      | rw [Flow.code_3419] at hc; cases hc; decide
      | rw [Flow.code_4873] at hc; cases hc; decide
      | rw [Flow.code_5022] at hc; cases hc; decide
      | rw [Flow.code_5027] at hc; cases hc; decide
      | rw [Flow.code_5030] at hc; cases hc; decide
      | rw [Flow.code_6647] at hc; cases hc; decide
      | rw [Flow.code_7600] at hc; cases hc; decide
  · simp [updateSites] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | rw [Flow.code_3424] at hc; cases hc; decide
      | rw [Flow.code_5022] at hc; cases hc; decide
      | rw [Flow.code_5023] at hc; cases hc; decide
      | rw [Flow.code_5027] at hc; cases hc; decide
      | rw [Flow.code_6649] at hc; cases hc; decide
      | rw [Flow.code_7599] at hc; cases hc; decide

section
variable {l : Launch} {g : Nat}

private theorem tacMove {s : TState} {dst : Nat} {a : Opnd} {b : Bool}
    (hc : kernel.code[s.pc]? = some ⟨none, putWord dst a⟩) (hf : s.fault = none)
    (hSite : s.pc ∉ Assumptions.swExp2Sites) (hl : (putWord dst a).isLocal = true)
    (hCore : Assumptions.coreOp (putWord dst a) = true)
    (hValue : readValue l g s 32 a = .ok (b32 b.toNat)) :
    Tau kernel Assumptions.all l g s (next (setReg s dst (b32 b.toNat))) := by
  apply tauStep_iff.mp
  rw [Assumptions.tauStep_all_eq_nil (L := l) (g := g) hSite hc hCore]

  have hStep : execLocalA [] l g s (putWord dst a) = .ok (next (setReg s dst (b32 b.toNat))) := by
    rw [execLocalA_nil]
    unfold putWord
    rw [execLocal_move rfl]
    simp only [execMove, hValue, bind, Except.bind, pure, Except.pure, b32, Value.bytes,
      DType.width, reduceCtorEq, ↓reduceIte, reduceIte]
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure,
    hl, ↓reduceIte, hStep]

private theorem putImm {s : TState} {dst : Nat} (b : Bool)
    (hc : kernel.code[s.pc]? = some ⟨none, putWord dst (.imm b.toNat)⟩) (hf : s.fault = none)
    (hSite : s.pc ∉ Assumptions.swExp2Sites) :
    Tau kernel Assumptions.all l g s (next (setReg s dst (b32 b.toNat))) := by
  apply tacMove hc hf hSite rfl rfl
  cases b <;> rfl

private theorem putCopy {s : TState} {dst src : Nat} (b : Bool)
    (hc : kernel.code[s.pc]? = some ⟨none, putWord dst (.reg src)⟩) (hf : s.fault = none)
    (hSite : s.pc ∉ Assumptions.swExp2Sites) (hSrc : phaseWord s src b) :
    Tau kernel Assumptions.all l g s (next (setReg s dst (b32 b.toNat))) := by
  apply tacMove hc hf hSite rfl rfl
  simp [readValue, readReg, hSrc, b32, pure, Except.pure]

private theorem putResult {s : TState} {bit b : Bool} {pc r : Nat}
    (hs : beforeStep score s bit pc) (w : Nat × Bool)
    (hw : provides (.put r b) (expected score pc bit) w = true) :
    phaseWord (next (setReg s r (b32 b.toNat))) w.1 w.2 :=
  holdsPut score hs (by simp [phaseWord, next, setReg])
    (fun v _ hv => by simp [next, setReg, Function.update_of_ne, hv]) w hw

private theorem turnResult {s : TState} {bit old : Bool} {pc r : Nat}
    (hs : beforeStep score s bit pc) (hr : phaseWord s r old) (w : Nat × Bool)
    (hw : provides (.flip r) (expected score pc bit) w = true) :
    phaseWord (next (setReg s r (b32 (!old).toNat))) w.1 w.2 :=
  holdsFlip score hs (fun b hb => by
    have he := Option.some.inj (hr.symm.trans hb)
    have hEq : old = b := by cases old <;> cases b <;> first | rfl | cases he
    subst b
    simp [phaseWord, next, setReg])
    (fun v _ hv => by simp [next, setReg, Function.update_of_ne, hv]) w hw

private theorem nodeIndices {i : Fin 10} (hi : i ∈ nodes score) :
    let spec := waitSite i
    checkIndex score spec.pc = none ∧
    checkIndex score (spec.pc+1) = some i ∧
    checkIndex score (spec.pc+3) = none ∧
    (∀ w ∈ tracked score, w ≠ spec.result) ∧
    (∀ n ≤ 3, 3103 ≤ spec.pc + n ∧ spec.pc + n ≤ 7742) := by
  cases score <;> fin_cases i <;> simp [nodes] at hi
  all_goals
    refine ⟨rfl, rfl, rfl, by decide, ?_⟩
    intro n hn
    dsimp [waitSite]
    omega

private theorem expectedTracked {pc : Nat} {bit : Bool} {w : Nat × Bool}
    (h : w ∈ expected score pc bit) : w.1 ∈ tracked score := by
  unfold expected at h
  cases score <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  repeat' split at h
  all_goals simp [tracked] at *
  all_goals aesop

private theorem bitNotSelf (bit : Bool) : (bit ^^ true) = !bit := by cases bit <;> rfl

private theorem bitUndo (bit passed : Bool) : ((bit ^^ passed) ^^ passed) = bit := by
  cases bit <;> cases passed <;> rfl

private theorem pollMove {l : Launch} {g : Nat} {s : TState} {e : Event}
    {u : Option TState} (i : Fin 10) (hPc : s.pc = (waitSite i).pc)
    (hWord : phaseWord s (waitSite i).phase b)
    (hs : EStep kernel Assumptions.all l g s e u)
    (hWait : u.isSome ∨ ∃ loc q passed acq scope, e.kind = .wait loc q passed acq scope) :
    ∃ loc passed acq scope, e = ⟨s.pc, .wait loc b.toNat passed acq scope⟩ ∧
      ∀ t, u = some t → t = next (setReg s (waitSite i).result (.pred passed)) := by
  obtain ⟨tm, hOut, hf⟩ := hs
  let waitOp := Op.mbarWait (waitSite i).result (waitSite i).base 0
    (.reg (waitSite i).phase) true .cta
  have hHealthy : s.fault = none := by
    cases hFault : s.fault with
    | none => rfl
    | some err =>
      have ht : tm = .ub err := by
        apply Out.ev.inj
        simpa [out, hFault] using hOut.symm
      subst tm
      rcases hf with ⟨rfl,rfl⟩
      rcases hWait with h | ⟨_, _, _, _, _, h⟩ <;> cases h
  have hOut' : out kernel Assumptions.all l g s = .ev (eventTmpl Assumptions.all l g s waitOp) := by
    simp [out, hHealthy, hPc, (waitCode i).1, guardHolds, pure, Except.pure, waitOp, Op.isLocal]
  obtain rfl := Out.ev.inj (hOut'.symm.trans hOut)
  change Fires s.pc (eventTmpl Assumptions.all l g s waitOp) e u at hf
  dsimp only [waitOp] at hf
  have hRead := readBits_b32 (L := l) (g := g) hWord (by cases b <;> decide)
  cases hLoc : mbarLoc l g s (waitSite i).base 0 with
  | ok loc =>
    obtain ⟨passed, acq, scope, he, hT⟩ := fires_wait_at hLoc hRead hf
    have hMod : (BitVec.ofNat 64 b.toNat).toNat % 2 = b.toNat := by cases b <;> decide
    rw [hMod] at he
    exact ⟨loc, passed, acq, scope, he, hT⟩
  | error f =>
    simp only [eventTmpl, tmaTmpl, hLoc, bind, Except.bind, ofExec, Fires] at hf
    rcases hf with ⟨rfl,rfl⟩
    rcases hWait with h | ⟨_, _, _, _, _, h⟩ <;> cases h

private theorem noCheckOfNoSpin {pc : Nat} (h : spinPc score pc = false) :
    checkIndex score pc = none := by
  simp only [spinPc, Bool.or_eq_false_iff, Option.isSome_eq_false_iff] at h
  exact Option.isNone_iff_eq_none.mp h.1.2

private theorem ordinaryAudit {s : TState} {i : Instr} (hLo : 3103 ≤ s.pc)
    (hHi : s.pc < 7742) (hc : kernel.code[s.pc]? = some i) (hSpin : spinPc score s.pc = false) :
    (i.op.isLocal || scoreEventOp i.op) = true ∧
    (∀ bit w, w ∈ expected score s.pc bit → modifies (updateOf score s.pc) ≠ some w.1 →
      w.1 ∉ readRegEffect i.op) ∧
    match i.op with
    | .brx .. => False
    | .bra dst _ => validOrdinary score s.pc dst (updateOf score s.pc) = true ∧
        (i.guard = none ∨ validOrdinary score s.pc (s.pc+1) (updateOf score s.pc) = true)
    | _ => validOrdinary score s.pc (s.pc+1) (updateOf score s.pc) = true := by
  have h := phaseCodeAt score hLo hHi hc
  simp only [hSpin, Bool.false_or, nonSpinCode, Bool.and_eq_true] at h
  refine ⟨h.1.1, ?_, ?_⟩
  · intro bit w hw hMod
    have hw' : w ∈ expected score s.pc false ++ expected score s.pc true := by
      cases bit
      · exact List.mem_append_left _ hw
      · exact List.mem_append_right _ hw
    have ha := List.all_eq_true.mp h.1.2 w hw'
    have hAlt : (modifies (updateOf score s.pc) == some w.1) = true ∨
        (!(readRegEffect i.op).contains w.1) = true := by
      simpa only [Bool.or_eq_true] using ha
    have hNo := hAlt.resolve_left (fun hh => hMod (beq_iff_eq.mp hh))
    intro hr
    rw [List.contains_iff_mem.mpr hr] at hNo
    cases hNo
  · cases hOp : i.op <;> simp only [hOp, Bool.and_eq_true, Bool.or_eq_true,
      Option.isNone_iff_eq_none] at h ⊢
    case brx => exact Bool.noConfusion h.2
    all_goals exact h.2

private theorem ordinaryTauFrame {s u : TState} {i : Instr} (hCode : kernel.code[s.pc]? = some i)
    (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3) (hSpin : spinPc score s.pc = false)
    (hKeep : updateOf score s.pc = .keep) (hTau : Tau kernel Assumptions.all l g s u)
    (hNoSeg : guardHolds s i.guard = .ok true →
      execLocalA Assumptions.all l g s i.op = .ok u →
      LocalFrame i.op s u) {bit : Bool} (hB : beforeStep score s bit s.pc) :
    phaseInvariant score u bit := by
  have hAudit := ordinaryAudit score hLo hHi hCode hSpin
  obtain ⟨k, hc, _, hExec⟩ := tauScoreSource hTau
  obtain rfl := Option.some.inj (hCode.symm.trans hc)
  have hNext (hN : u.pc = s.pc+1) (hNotKnown : i.guard ≠ none ∨
      ∀ dst un, i.op ≠ .bra dst un) : validOrdinary score s.pc u.pc .keep = true := by
    rw [hN, ← hKeep]
    cases hOp : i.op <;> simp only [hOp] at hAudit
    case brx => exact False.elim hAudit.2.2
    case bra dst un =>
      rcases hNotKnown with hg | ho
      · exact hAudit.2.2.2.resolve_left hg
      · exact False.elim (ho dst un hOp)
    all_goals exact hAudit.2.2
  have hRegs (hFrame : ∀ r, r ∉ writesRegs i.op → u.regs r = s.regs r)
      (w : Nat × Bool) (hm : w ∈ expected score s.pc bit) : u.regs w.1 = s.regs w.1 := by
    apply hFrame
    intro hW
    exact hAudit.2.1 bit w hm (by rw [hKeep]; intro h; cases h) (List.mem_append_left _ hW)
  rcases hExec with ⟨rfl, hGuard⟩ | ⟨hGuard, _, hExec⟩
  · have hg : i.guard ≠ none := by
      intro h
      rw [h, show guardHolds s none = .ok true from rfl] at hGuard
      cases hGuard
    exact claimOfValid score hB (hNext rfl (.inl hg)) (Nat.zero_le _)
      (fun w _ hw => holdsKeep score hB (fun _ _ => rfl) w hw)
  · have hFrame := hNoSeg hGuard hExec
    have hVal : validOrdinary score s.pc u.pc .keep = true := by
      have hPc := hFrame.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case brx => simp [ho] at hAudit
      case bra dst un =>
        rw [hPc, ← hKeep]
        have hv := hAudit.2.2
        rw [ho] at hv
        exact hv.1
      all_goals exact hNext hPc (.inr (fun _ _ h => by rw [ho] at h; cases h))
    exact claimOfValid score hB hVal (hFrame.sub.symm ▸ hSub)
      (fun w _ hw => holdsKeep score hB (hRegs hFrame.regs) w hw)

private theorem rollProof {i : Fin 10} (hi : i ∈ nodes score) :
    let spec := waitSite i
    validOrdinary score spec.pc (spec.pc+2) .keep = true ∧
    validOrdinary score (spec.pc+2) spec.pc .keep = true ∧
    ∀ bit ∈ activeBits score spec.pc,
      ((fixedBit score (spec.pc+3)).all (· == !bit)) = true ∧
      (expected score (spec.pc+3) (!bit)).all (provides .keep (expected score spec.pc bit)) = true ∧
      (spec.phase,!bit) ∈ expected score spec.pc bit := by
  have h := List.all_eq_true.mp (rollTransition score) i hi
  simp only [Bool.and_eq_true] at h
  refine ⟨h.1.1, h.1.2, fun b hb => ?_⟩
  have hu := List.all_eq_true.mp h.2 _ hb
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hu
  exact ⟨hu.1.1, hu.1.2, hu.2⟩

private theorem stepWithSuccess {s u : TState} {i : Fin 10} (hi : i ∈ nodes score) {bit : Bool}
    (hs : beforeStep score s bit (waitSite i).pc) (hPc : u.pc = (waitSite i).pc+3)
    (hSub : u.sub ≤ 3) (hSame : u.regs = s.regs) :
    phaseInvariant score u (!bit) := by
  obtain ⟨hCheck, hC1, hC3, hTracked, hBounds⟩ := nodeIndices score hi
  have hB := hBounds 3 (by decide)
  have hRoll := (rollProof score hi).2.2 bit (bitPresent score hs)
  refine ⟨hPc.symm ▸ hB.1, hPc.symm ▸ hB.2, hSub, ?_⟩
  rw [hPc, hC3]
  refine ⟨fun b hb => ?_, fun w hm => ?_⟩
  · have hd := hRoll.1
    rw [hb] at hd
    have he : (b == !bit) = true := hd
    exact (beq_iff_eq.mp he).symm
  · exact holdsKeep score hs (fun _ _ => congrFun hSame _) w (List.all_eq_true.mp hRoll.2.1 _ hm)

private theorem knownPhase {s : TState} {i : Fin 10} (hi : i ∈ nodes score) {bit : Bool}
    (hs : beforeStep score s bit (waitSite i).pc) : phaseWord s (waitSite i).phase (!bit) :=
  hs.2 _ ((rollProof score hi).2.2 bit (bitPresent score hs)).2.2

private theorem observePoll {s u : TState} {e : Event} {i : Fin 10} (hi : i ∈ nodes score)
    {bit : Bool} (hPc : s.pc = (waitSite i).pc) (hs : beforeStep score s bit s.pc)
    (hSub : s.sub ≤ 3) (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ loc passed acq scope, e.kind = .wait loc (!bit).toNat passed acq scope ∧
      phaseInvariant score u (bit ^^ passed) := by
  rw [hPc] at hs
  obtain ⟨loc, passed, acq, scope, hK, hU⟩ := pollMove i hPc (knownPhase score hi hs) he (.inl rfl)
  obtain rfl := hU u rfl
  obtain ⟨_, hC, _, hTracked, hBounds⟩ := nodeIndices score hi
  have hB := hBounds 1 (by decide)
  have hPc' : (next (setReg s (waitSite i).result (.pred passed))).pc = (waitSite i).pc + 1 := by
    simp [next, setReg, hPc]
  refine ⟨loc, passed, acq, scope, by rw [hK], hPc'.symm ▸ hB.1, hPc'.symm ▸ hB.2,
    hSub, ?_⟩
  rw [hPc', hC]
  refine ⟨passed, by simp [next, setReg], ?_⟩
  rw [bitUndo]
  refine ⟨hs.1, fun w hm => ?_⟩
  have hd := hTracked w.1 (expectedTracked score hm)
  unfold phaseWord
  simpa only [next, setReg, Function.update_of_ne hd] using hs.2 w hm

private theorem stepPutAt {s u : TState} {bit b : Bool} {pc r : Nat}
    (hPc : s.pc = pc) (hs : beforeStep score s bit s.pc) (hSub : s.sub ≤ 3)
    (hJump : validOrdinary score pc (pc+1) (.put r b) = true)
    (hu : u = next (setReg s r (b32 b.toNat))) :
    phaseInvariant score u bit := by
  subst u
  have hValid : validOrdinary score s.pc (next (setReg s r (b32 b.toNat))).pc
      (.put r b) = true := by
    simpa only [next, setReg, hPc] using hJump
  exact claimOfValid score hs hValid hSub (fun w _ => putResult score hs w)

private theorem stepTurnAt {s u : TState} {bit old : Bool} {pc r : Nat}
    (hPc : s.pc = pc) (hs : beforeStep score s bit s.pc) (hSub : s.sub ≤ 3)
    (hWord : phaseWord s r old)
    (hJump : validOrdinary score pc (pc+1) (.flip r) = true)
    (hu : u = next (setReg s r (b32 (!old).toNat))) : phaseInvariant score u bit := by
  subst u
  have hValid : validOrdinary score s.pc (next (setReg s r (b32 (!old).toNat))).pc
      (.flip r) = true := by
    simpa only [next, setReg, hPc] using hJump
  exact claimOfValid score hs hValid hSub (fun w _ => turnResult score hs hWord w)

private def flipOp (r : Nat) : Op := .int ⟨.xor, .int .b 32, false, [some r], [.reg r, .imm 1]⟩

private theorem turnTau {s : TState} {old : Bool} {r : Nat}
    (hc : kernel.code[s.pc]? = some ⟨none, flipOp r⟩) (hf : s.fault = none)
    (hOff : s.pc ∉ Assumptions.swExp2Sites) (hWord : phaseWord s r old) :
    Tau kernel Assumptions.all l g s (next (setReg s r (b32 (!old).toNat))) := by
  apply tauStep_iff.mp
  rw [Assumptions.tauStep_all_eq_nil (L := l) (g := g) hOff hc rfl]
  have hExec : execLocalA [] l g s (flipOp r) =
      .ok (next (setReg s r (b32 (!old).toNat))) := by
    unfold flipOp
    rw [execLocalA_nil, execLocal_int rfl]
    have hR := readBits_b32 (L := l) (g := g) hWord (by cases old <;> decide)
    simp only [execInt, DType.width, hR, bind, Except.bind, pure, Except.pure]
    cases old <;> rfl
  simp only [tauStep, out, hf, hc, guardHolds, pure, Except.pure,
    show (flipOp r).isLocal = true from rfl, ↓reduceIte, hExec]

private theorem phaseTauUpdate {s u : TState} {bit : Bool} (hUpdate : updateOf score s.pc ≠ .keep)
    (hTau : Tau kernel Assumptions.all l g s u) (hs : beforeStep score s bit s.pc)
    (hSub : s.sub ≤ 3) : phaseInvariant score u bit := by
  obtain ⟨_, _, hf, _⟩ := tauScoreSource hTau
  have hp := updateMembership score hUpdate
  cases score
  · simp [updateSites] at hp
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
    · exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_3283) hf (hp.symm ▸ by decide)))
    · exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_3419) hf (hp.symm ▸ by decide)))
    · exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putImm false (hp.symm ▸ Flow.code_4873) hf (hp.symm ▸ by decide)))
    · exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_5022) hf (hp.symm ▸ by decide)))
    · exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_5027) hf (hp.symm ▸ by decide)))
    · have hr : phaseWord s 7253 true := hs.2 (7253,true) (by rw [hp]; cases bit <;> decide)
      exact stepPutAt false hp hs hSub (by decide)
        (tau_det hTau (putCopy true (hp.symm ▸ Flow.code_5030) hf (hp.symm ▸ by decide) hr))
    · have hr : phaseWord s 7258 bit := hs.2 (7258,bit) (by rw [hp]; cases bit <;> decide)
      exact stepTurnAt false hp hs hSub hr (by decide)
        (tau_det hTau (turnTau (hp.symm ▸ Flow.code_6647) hf (hp.symm ▸ by decide) hr))
    · have hr : phaseWord s 7258 bit := hs.2 (7258,bit) (by rw [hp]; cases bit <;> decide)
      exact stepTurnAt false hp hs hSub hr (by decide)
        (tau_det hTau (turnTau (hp.symm ▸ Flow.code_7600) hf (hp.symm ▸ by decide) hr))
  · simp [updateSites] at hp
    rcases hp with hp | hp | hp | hp | hp | hp
    · exact stepPutAt true hp hs hSub (by decide)
        (tau_det hTau (putImm false (hp.symm ▸ Flow.code_3424) hf (hp.symm ▸ by decide)))
    · exact stepPutAt true hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_5022) hf (hp.symm ▸ by decide)))
    · have hr : phaseWord s 7258 true := hs.2 (7258,true) (by rw [hp]; cases bit <;> decide)
      exact stepPutAt true hp hs hSub (by decide)
        (tau_det hTau (putCopy true (hp.symm ▸ Flow.code_5023) hf (hp.symm ▸ by decide) hr))
    · exact stepPutAt true hp hs hSub (by decide)
        (tau_det hTau (putImm true (hp.symm ▸ Flow.code_5027) hf (hp.symm ▸ by decide)))
    · have hr : phaseWord s 7253 bit := hs.2 (7253,bit) (by rw [hp]; cases bit <;> decide)
      exact stepTurnAt true hp hs hSub hr (by decide)
        (tau_det hTau (turnTau (hp.symm ▸ Flow.code_6649) hf (hp.symm ▸ by decide) hr))
    · have hr : phaseWord s 7253 bit := hs.2 (7253,bit) (by rw [hp]; cases bit <;> decide)
      exact stepTurnAt true hp hs hSub hr (by decide)
        (tau_det hTau (turnTau (hp.symm ▸ Flow.code_7599) hf (hp.symm ▸ by decide) hr))

private theorem spinIndexSpec {pc step : Nat} {i : Fin 10}
    (h : (nodes score).find? (fun k => (waitSite k).pc + step == pc) = some i) :
    i ∈ nodes score ∧ (waitSite i).pc + step = pc := by
  exact ⟨List.mem_of_find?_eq_some h,
    beq_iff_eq.mp (List.find?_some (p := fun k => (waitSite k).pc + step == pc) h)⟩

private theorem spinOutsideExp2 {i : Fin 10} (k : Fin 3) :
    (waitSite i).pc + k.val ∉ Assumptions.swExp2Sites := by
  fin_cases i <;> fin_cases k <;> decide

private theorem branchForSpin {s : TState} {target : Nat} {cond : Option (Nat × Bool)}
    {taken : Bool} (hc : kernel.code[s.pc]? = some ⟨cond, .bra target true⟩)
    (hE : s.pc ∉ Assumptions.swExp2Sites) (hf : s.fault = none)
    (hGuard : guardHolds s cond = .ok taken) :
    Tau kernel Assumptions.all l g s (if taken then {s with pc := target} else skip s) := by
  apply tauStep_iff.mp
  rw [Assumptions.tauStep_all_eq_nil (L := l) (g := g) hE hc rfl]
  cases taken <;>
    simp [tauStep, out, hf, hc, hGuard, Op.isLocal, execLocalA, execLocalRule,
      execLocal, Op.rule, execBranch, pure, Except.pure]

private theorem spinCheckStep {s u : TState} {bit : Bool} {i : Fin 10}
    (hSite : checkIndex score s.pc = some i) (hs : phaseInvariant score s bit)
    (ht : Tau kernel Assumptions.all l g s u) :
    phaseInvariant score u bit := by
  obtain ⟨hi, hPc⟩ := spinIndexSpec score hSite
  obtain ⟨_, _, hf, _⟩ := tauScoreSource ht
  have hC := hPc ▸ (waitCode i).2.1
  have hS := spinOutsideExp2 (i := i) (1 : Fin 3)
  have hExp : s.pc ∉ Assumptions.swExp2Sites := hPc ▸ hS
  obtain ⟨hLo, hHi, hSub, hPhase⟩ := hs
  rw [hSite] at hPhase
  obtain ⟨passed, hPred, hBefore⟩ := hPhase
  have hGuard : guardHolds s (some ((waitSite i).result, false)) = .ok passed := by
    cases passed <;>
      simp [guardHolds, readReg, hPred, bind, Except.bind, pure, Except.pure]
  obtain rfl := tau_det ht (branchForSpin hC hExp hf hGuard)
  cases passed
  · have hv := (rollProof score hi).1
    have hNew : (skip s).pc = (waitSite i).pc + 2 := by simp [skip, ← hPc, Nat.add_assoc]
    have hValid : validOrdinary score (waitSite i).pc (skip s).pc .keep = true := hNew.symm ▸ hv
    have hBefore' : beforeStep score s bit (waitSite i).pc := by
      simpa only [Bool.xor_false] using hBefore
    exact claimOfValid score hBefore' hValid (Nat.zero_le _) (fun w _ h =>
      holdsKeep score hBefore' (fun _ _ => rfl) w h)
  · have hBefore' : beforeStep score s (!bit) (waitSite i).pc := by
      simpa only [bitNotSelf] using hBefore
    let t := {s with pc := (waitSite i).pc+3}
    have hDone : phaseInvariant score t (!(!bit)) :=
      stepWithSuccess score hi hBefore' rfl hSub rfl
    change phaseInvariant score t bit
    simpa only [Bool.not_not] using hDone

private theorem spinRetryStep {s u : TState} {bit : Bool} {i : Fin 10}
    (hSite : retryIndex score s.pc = some i) (hSub : s.sub ≤ 3) (hs : beforeStep score s bit s.pc)
    (ht : Tau kernel Assumptions.all l g s u) :
    phaseInvariant score u bit := by
  obtain ⟨hi, hPc⟩ := spinIndexSpec score hSite
  obtain ⟨_, _, hf, _⟩ := tauScoreSource ht
  have hC := hPc ▸ (waitCode i).2.2
  have hS := spinOutsideExp2 (i := i) (2 : Fin 3)
  have hExp : s.pc ∉ Assumptions.swExp2Sites := hPc ▸ hS
  obtain rfl := tau_det ht (branchForSpin hC hExp hf (show guardHolds s none = .ok true from rfl))
  have hBefore : beforeStep score s bit ((waitSite i).pc + 2) := hPc.symm ▸ hs
  exact claimOfValid score hBefore (rollProof score hi).2.1 hSub (fun w _ h =>
    holdsKeep score hBefore (fun _ _ => rfl) w h)

private theorem segmentPhase {s u : TState} {bit : Bool} {m : SegMatch CuteSlot}
    (hm : s.pc ∈ Assumptions.swExp2Sites) (hMatch : cuteExp2.matchAt kernel s.pc = some m)
    (hr : Assumptions.execSwExp2 m s = .ok u) (hb : beforeStep score s bit s.pc) :
    phaseInvariant score u bit := by
  have hv := List.all_eq_true.mp (exp2CreditCode score) _ hm
  simp only [exp2CreditFrame, hMatch, Bool.and_eq_true] at hv
  obtain ⟨hStop, hSub, _, hKeep⟩ := scoreSegmentFrame hr
  have hV : validOrdinary score s.pc u.pc .keep = true := by rw [hStop]; exact hv.1
  have hKeep' (w : Nat × Bool) (hw : w ∈ expected score s.pc bit) : u.regs w.1 = s.regs w.1 := by
    have hn := List.all_eq_true.mp hv.2 w.1 (expectedTracked score hw)
    apply hKeep
    intro hWrite
    rw [List.contains_iff_mem.mpr hWrite] at hn
    cases hn
  exact claimOfValid score hb hV (hSub.symm ▸ Nat.zero_le _)
    (fun w _ h => holdsKeep score hb hKeep' w h)

private theorem phaseOrdinaryTau {s u : TState} {bit : Bool} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hSub : s.sub ≤ 3) (hSpin : spinPc score s.pc = false) (hB : beforeStep score s bit s.pc)
    (ht : Tau kernel Assumptions.all l g s u) : phaseInvariant score u bit := by
  by_cases hUpdate : updateOf score s.pc = .keep
  · obtain ⟨i, hc, _, hExec⟩ := tauScoreSource ht
    rcases hExec with ⟨rfl, hg⟩ | ⟨_, _, hLocal⟩
    · exact ordinaryTauFrame score hc hLo hHi hSub hSpin hUpdate ht
        (fun h _ => by rw [hg] at h; cases h) hB
    · rcases scoreExecLocal hLocal with hl | ⟨m, hm, hMatch, hr⟩
      · exact ordinaryTauFrame score hc hLo hHi hSub hSpin hUpdate ht
          (fun _ _ => hl) hB
      · exact segmentPhase score hm hMatch hr hB
  · exact phaseTauUpdate score hUpdate ht hB hSub
end

private theorem freshOne (regs : List Nat) : ∃ r, r ∉ regs := by
  induction regs with
  | nil => exact ⟨0, by simp⟩
  | cons reg regs ih =>
    have hBound : ∃ b, ∀ r ∈ reg :: regs, r < b := by
      clear ih
      induction regs generalizing reg with
      | nil => exact ⟨reg+1, by simp⟩
      | cons top tail ht =>
        obtain ⟨b, hb⟩ := ht top
        refine ⟨max b (reg+1), ?_⟩
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact (Nat.lt_succ_self _).trans_le (Nat.le_max_right ..)
        · exact (hb r hr).trans_le (Nat.le_max_left ..)
    obtain ⟨b,hb⟩ := hBound
    exact ⟨b, fun h => (Nat.lt_irrefl b) (hb b h)⟩

private theorem phaseOrdinaryEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {bit : Bool} (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742) (hSub : s.sub ≤ 3)
    (hSpin : spinPc score s.pc = false) (hB : beforeStep score s bit s.pc)
    (he : EStep kernel Assumptions.all l g s e (some u)) : phaseInvariant score u bit := by
  obtain ⟨i, hc, hl, _⟩ := estep_event_source he
  have hUpdate : updateOf score s.pc = .keep := by
    by_contra hn
    have hh := (exactUpdate score hc hn).2
    rw [hl] at hh
    cases hh
  obtain ⟨hOp, hRegs, hDst⟩ := ordinaryAudit score hLo hHi hc hSpin
  rw [hl, Bool.false_or] at hOp
  obtain ⟨r, hr⟩ := freshOne (scoreEventWrites i.op)
  have hWalk := (scoreEventStep (r := r) hc hOp hSub hr he).1
  have hKeep (w : Nat × Bool) (hw : w ∈ expected score s.pc bit) : u.regs w.1 = s.regs w.1 := by
    apply (scoreEventStep hc hOp hSub ?_ he).2
    intro h
    exact hRegs bit w hw (by rw [hUpdate]; intro hh; cases hh) (List.mem_append_right _ h)
  rcases hWalk.pc with ⟨hNext, _⟩ | ⟨hSame, _⟩
  · have hv : validOrdinary score s.pc u.pc .keep = true := by
      rw [hNext, ← hUpdate]
      cases hop : i.op <;> simp only [hop] at hDst
      case bra => rw [hop] at hl; cases hl
      all_goals exact hDst
    exact claimOfValid score hB hv hWalk.sub (fun w _ h => holdsKeep score hB hKeep w h)
  · refine ⟨hSame.symm ▸ hLo, hSame.symm ▸ hHi.le, hWalk.sub, ?_⟩
    rw [hSame, noCheckOfNoSpin score hSpin]
    exact ⟨hB.1, fun w hm => (hKeep w hm).trans (hB.2 w hm)⟩

private theorem pollIndexSpec {pc : Nat} {i : Fin 10} (h : pollIndex score pc = some i) :
    i ∈ nodes score ∧ (waitSite i).pc = pc := by
  exact ⟨List.mem_of_find?_eq_some h,
    beq_iff_eq.mp (List.find?_some (p := fun k => (waitSite k).pc == pc) h)⟩

private def pollPcs : List Nat := (nodes score).map (fun i => (waitSite i).pc)

private theorem pollIndexSome {pc : Nat} :
    (pollIndex score pc).isSome = true ↔ pc ∈ pollPcs score := by
  rw [pollIndex, List.find?_isSome, pollPcs, List.mem_map]
  simp only [beq_iff_eq]

/-- Recognizes a successful use of a phase cursor, independently of its physical object. -/
@[no_expose] def phaseAcquired (e : Event) : Bool :=
  match e.kind with
  | .wait _ _ true _ _ => (pollIndex score e.pc).isSome
  | _ => false

private theorem markerAtPoll {e : Event} {loc : Loc} {q : Nat} {passed acq : Bool}
    {scope : MbarScope} {i : Fin 10} (hi : pollIndex score e.pc = some i)
    (he : e.kind = .wait loc q passed acq scope) : phaseAcquired score e = passed := by
  cases passed <;> simp [phaseAcquired, he, hi]

private theorem markerNotPoll {e : Event} (hp : pollIndex score e.pc = none) :
    phaseAcquired score e = false := by
  unfold phaseAcquired
  split <;> simp [hp]

private theorem notSpin {pc : Nat} (hp : pollIndex score pc = none)
    (hc : checkIndex score pc = none) (hr : retryIndex score pc = none) :
    spinPc score pc = false := by
  simp [spinPc, hp, hc, hr]

private theorem tailStep {l : Launch} {g : Nat} {s u : TState} {e : Option Event}
    (hTail : 7742 ≤ s.pc) (he : WStep kernel Assumptions.all l g s e u) : 7742 ≤ u.pc := by
  rcases he with ⟨rfl, ht⟩ | ⟨f, rfl, hf⟩
  · obtain ⟨i, hc, _, hx⟩ := tauScoreSource ht
    rcases hx with ⟨rfl, _⟩ | ⟨_, _, hx⟩
    · change 7742 ≤ s.pc+1
      omega
    · rcases scoreExecLocal hx with hLocal | ⟨_, hm, _, _⟩
      · let valid (i : Instr) := match i.op with
          | .bra dst _ => decide (7742 ≤ dst)
          | .brx .. => false
          | _ => true
        have hAudited : (kernel.code.drop 7742).all valid = true := by
          set_option maxRecDepth 100000 in kernel_rfl
        have hOne : (kernel.code.drop 7742)[s.pc-7742]? = some i := by
          rw [List.getElem?_drop, Nat.add_sub_of_le hTail, hc]
        have hValid := List.all_eq_true.mp hAudited _ (List.mem_of_getElem? hOne)
        have hp := hLocal.pc
        cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hp
        case bra dst un =>
          rw [hp]
          simpa only [valid, ho, decide_eq_true_eq] using hValid
        case brx => simp [valid, ho] at hValid
        all_goals omega
      · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hm
        omega
  · obtain ⟨i, hc, hl, hFire⟩ := estep_event_source hf
    have hAudited : kernel.code.all (fun i => i.op.isLocal ||
        Epilogue.ordinaryEvent i.op) = true := by decide +kernel
    have hOrd := List.all_eq_true.mp hAudited _ (List.mem_of_getElem? hc)
    rw [hl, Bool.false_or] at hOrd
    have hFrame := Epilogue.ordinaryEventFrame
      (A := Assumptions.all) (l := l) (g := g) (s := s) hOrd
    rcases callbackFrame_fires hFrame hFire with h | h <;> omega

private def withinPhase (s : TState) (bit : Bool) : Prop :=
  phaseInvariant score s bit ∨ 7742 ≤ s.pc

private theorem stableTau {l : Launch} {g : Nat} {s u : TState} {bit : Bool}
    (hs : withinPhase score s bit) (ht : Tau kernel Assumptions.all l g s u) :
    withinPhase score u bit := by
  rcases hs with hInv | hTail
  · obtain ⟨hLo, hHi, hSub, hB⟩ := hInv
    by_cases hEnd : s.pc = 7742
    · exact .inr (tailStep hEnd.ge (.inl ⟨rfl,ht⟩))
    have hLt : s.pc < 7742 := lt_of_le_of_ne hHi hEnd
    cases hC : checkIndex score s.pc with
    | some i => exact .inl (spinCheckStep score hC ⟨hLo,hHi,hSub,hB⟩ ht)
    | none =>
      rw [hC] at hB
      cases hR : retryIndex score s.pc with
      | some i => exact .inl (spinRetryStep score hR hSub hB ht)
      | none =>
        cases hP : pollIndex score s.pc with
        | none => exact .inl (phaseOrdinaryTau score hLo hLt hSub (notSpin score hP hC hR) hB ht)
        | some i =>
          obtain ⟨_, hp⟩ := pollIndexSpec score hP
          obtain ⟨ins, hc, _, hExec⟩ := tauScoreSource ht
          rw [← hp, (waitCode i).1] at hc
          obtain rfl := Option.some.inj hc.symm
          rcases hExec with h | h
          · cases h.2
          · cases h.2.1
  · exact .inr (tailStep hTail (.inl ⟨rfl,ht⟩))

private theorem stableEvent {l : Launch} {g : Nat} {s u : TState} {e : Event} {bit : Bool}
    (hs : withinPhase score s bit) (he : EStep kernel Assumptions.all l g s e (some u)) :
    withinPhase score u (bit ^^ phaseAcquired score e) := by
  rcases hs with hInv | hTail
  · obtain ⟨hLo, hHi, hSub, hB⟩ := hInv
    by_cases hEnd : s.pc = 7742
    · exact .inr (tailStep hEnd.ge (.inr ⟨e,rfl,he⟩))
    have hLt : s.pc < 7742 := lt_of_le_of_ne hHi hEnd
    have hE : e.pc = s.pc := estep_source_pc he
    obtain ⟨i, hc, hL, _⟩ := estep_event_source he
    cases hC : checkIndex score s.pc with
    | some k =>
      obtain ⟨_, hpc⟩ := spinIndexSpec score hC
      rw [← hpc, (waitCode k).2.1] at hc
      cases hc
      cases hL
    | none =>
      rw [hC] at hB
      cases hR : retryIndex score s.pc with
      | some k =>
        obtain ⟨_, hpc⟩ := spinIndexSpec score hR
        rw [← hpc, (waitCode k).2.2] at hc
        cases hc
        cases hL
      | none =>
        cases hP : pollIndex score s.pc with
        | some k =>
          obtain ⟨hk, hpc⟩ := pollIndexSpec score hP
          obtain ⟨loc, b, acq, sc, hK, hResult⟩ := observePoll score hk hpc.symm hB hSub he
          rw [markerAtPoll score (hE.symm ▸ hP) hK]
          exact .inl hResult
        | none =>
          rw [markerNotPoll score (hE.symm ▸ hP), Bool.xor_false]
          exact .inl (phaseOrdinaryEvent score hLo hLt hSub (notSpin score hP hC hR) hB he)
  · exact .inr (tailStep hTail (.inr ⟨e,rfl,he⟩))

private def countBit (n : Nat) : Bool := decide (n%2 = 1)

private theorem tick (n : Nat) (b : Bool) :
    (countBit n ^^ b) = countBit (n + b.toNat) := by
  cases b
  · simp [countBit]
  · by_cases h : n%2 = 1
    · have hh : (n+1)%2 ≠ 1 := by omega
      simp [countBit, h, hh]
    · have hh : (n+1)%2 = 1 := by omega
      simp [countBit, h, hh]

private theorem phasePath {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (hr : TraceReach kernel Assumptions.all l g s es u) (n : Nat)
    (hs : withinPhase score s (countBit n)) :
    withinPhase score u (countBit (n + es.countP (phaseAcquired score))) := by
  induction hr generalizing n with
  | refl => simpa using hs
  | tau ht _ ih => exact ih n (stableTau score hs ht)
  | @event _ _ _ es e he _ ih =>
    have hU := stableEvent score hs he
    rw [tick] at hU
    have hPath := ih _ hU
    have hCount : (n + (phaseAcquired score e).toNat) +
        es.countP (phaseAcquired score) =
        n + (e :: es).countP (phaseAcquired score) := by
      rw [List.countP_cons]
      cases phaseAcquired score e <;> simp
      omega
    exact hCount ▸ hPath

private theorem noCreditsInPrefixOfFirst {X : Execution} {g k n : Nat} (hn : n ≤ k)
    (hFirst : ∀ j < k, ∀ e, X.get (g,j) = some e → phaseAcquired score e ≠ true) :
    ((X.tr g).take n).countP (phaseAcquired score) = 0 := by
  by_contra h
  have hN : 0 < ((X.tr g).take n).countP (phaseAcquired score) := by omega
  obtain ⟨j, hj, e, he, hm, _⟩ := exists_nth (phaseAcquired score) (X.tr g) hN
  exact hFirst j (lt_of_lt_of_le hj hn) e he hm

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j pc q : Nat} {loc : Loc} {acq : Bool}
    {scope : MbarScope} (he : X.get (g,j) = some ⟨pc, .wait loc q true acq scope⟩)
include hp hX he

private theorem selectedPollParity (hSite : pc ∈ pollPcs score) :
    q = (((X.tr g).take j).countP (phaseAcquired score) + (if score then 0 else 1)) % 2 := by
  classical
  let e : Event := ⟨pc, .wait loc q true acq scope⟩
  let seen (i : Nat) := ∃ f, X.get (g,i) = some f ∧ phaseAcquired score f = true
  have hm : phaseAcquired score e = true := by
    simpa only [e, phaseAcquired] using (pollIndexSome score).mpr hSite
  have hSome : ∃ i, seen i := ⟨j,e,he,hm⟩
  let k := Nat.find hSome
  have hK : k ≤ j := Nat.find_min' hSome ⟨e,he,hm⟩
  obtain ⟨first, hFirst, hMark⟩ := Nat.find_spec hSome
  have hS : first.pc ∈ pollPcs score := by
    unfold phaseAcquired at hMark
    split at hMark
    · exact (pollIndexSome score).mp hMark
    · cases hMark
  have hFirstRange : 3420 ≤ first.pc ∧ first.pc < 7742 := by
    cases score <;> simp [pollPcs, nodes, waitSite] at hS <;> omega
  obtain ⟨w, _, pos, s, _, hPos, hAt, hRun⟩ :=
    softmaxBodySuffix hp hX hFirst hFirstRange.1 hFirstRange.2
  have hPosJ : pos ≤ j := hPos.trans hK
  have hBefore := noCreditsInPrefixOfFirst score hPos (fun i hi f hf hm =>
    Nat.find_min hSome hi ⟨f,hf,hm⟩)
  let k' := j-pos
  have he' : ((X.tr g).drop pos)[k']? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hPosJ]
    exact he
  obtain ⟨u, _, hPath, hE⟩ := hRun.before_event he'
  have hStart : withinPhase score s (countBit score.toNat) := by
    refine .inl ⟨hAt.1.ge, by rw [hAt.1]; decide, hAt.2.1.symm ▸ Nat.zero_le _, ?_⟩
    rw [hAt.1]
    cases score
    · exact ⟨fun b hb => Option.some.inj hb, fun _ hw => (List.not_mem_nil hw).elim⟩
    · exact ⟨fun b hb => Option.some.inj hb, fun _ hw => (List.not_mem_nil hw).elim⟩
  have hProgress := phasePath score hPath score.toNat hStart
  have hPc : u.pc = pc := (estep_source_pc hE).symm
  have hEnd : pc < 7742 := by
    cases score <;> simp [pollPcs, nodes, waitSite] at hSite <;> omega
  have hInv := hProgress.resolve_right (by rw [hPc]; omega)
  obtain ⟨i,hI⟩ := Option.isSome_iff_exists.mp ((pollIndexSome score).mpr hSite)
  have ⟨hi,hIpc⟩ := pollIndexSpec score hI
  have hCheck := (nodeIndices score hi).1
  have hNow := hInv.2.2.2
  have hSame : u.pc = (waitSite i).pc := hPc.trans hIpc.symm
  rw [hSame, hCheck] at hNow
  obtain ⟨a, passed, acq', scope', hKind, _⟩ :=
    pollMove i hSame (knownPhase score hi hNow) hE (.inr ⟨loc,q,true,acq,scope,rfl⟩)
  have hQ := (Kind.wait.inj (congrArg Event.kind hKind)).2.1
  have hSplit := List.take_add (l := X.tr g) (i := pos) (j := k')
  rw [Nat.add_sub_of_le hPosJ] at hSplit
  rw [hSplit, List.countP_append, hBefore, Nat.zero_add]
  rw [hQ]
  let n := ((X.tr g).drop pos |>.take k').countP (phaseAcquired score)
  change (!countBit (score.toNat+n)).toNat = (n + (if score then 0 else 1))%2
  have h0 : n%2 = 0 ∨ n%2 = 1 := by omega
  have h1 : (n+1)%2 = 0 ∨ (n+1)%2 = 1 := by omega
  have hComm : (1+n)%2 = (n+1)%2 := congrArg (·%2) (Nat.add_comm 1 n)
  cases score <;> rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    first | omega | simp [countBit, hComm, h0, h1]

omit hp hX he in
/-- The score-ready marker recognizes a successful poll of the active round. -/
theorem scoreReadyMarkKind (e : Event) : phaseAcquired true e =
    match e.kind with
    | .wait _ _ true _ _ => [3425, 5109, 6676].contains e.pc
    | _ => false := by
  obtain ⟨source, kind⟩ := e
  cases kind <;> try rfl
  rename_i _ _ ok _ _
  cases ok
  · rfl
  · apply Bool.eq_iff_iff.mpr
    exact (pollIndexSome true).trans List.contains_iff_mem.symm

/-- Successful softmax score-ready waits alternate from parity zero. -/
theorem scoreReadySourceParity (hSite : pc ∈ [3425,5109,6676]) :
    q = (((X.tr g).take j).countP (phaseAcquired true)) % 2 :=
  selectedPollParity true hp hX he hSite

/-- The concrete credit wait uses the phase complementary to its earlier acquire count. -/
theorem creditPollParity (hSite : pc ∈ [3420,4874,6558,7463,7738]) :
    q = ((Thread.Scores.before X (g,j)).credits + 1) % 2 := by
  rw [Thread.Scores.beforeCredits]
  have hMark : phaseAcquired false = Thread.Scores.creditAcquired := by
    funext e
    obtain ⟨source, kind⟩ := e
    cases kind <;> try rfl
    rename_i _ _ b _ _
    cases b
    · rfl
    · apply Bool.eq_iff_iff.mpr
      exact (pollIndexSome false).trans List.contains_iff_mem.symm
  simpa only [hMark, Bool.false_eq_true, ↓reduceIte] using
    selectedPollParity false hp hX he hSite

end PTX.Kernels.TmlFa4Fwd.Softmax
