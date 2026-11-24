-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReadyTrace
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Proof.CorrectionPollPrefix
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Order.OrderWaits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

noncomputable section

/-- A successful acquire of the second MMA output stage in the correction lane's CTA. -/
def SecondOutputAcquire (l : Launch) (X : Execution) (wait : EvId) : Prop :=
  ∃ e scope, X.get wait = some e ∧
    e.kind = .wait ⟨.shared, wait.1 / l.block, l.sharedBase + 152⟩ 0 true true scope

private def secondWindow (pc : Nat) : Prop :=
  7755 ≤ pc ∧ (pc ≤ 8769 ∨ 9201 ≤ pc ∧ pc ≤ 9205)

private def secondCode (pc : Nat) (ins : Instr) : Bool :=
  ((ins.op.isLocal || correctionReturningOp ins.op) &&
    (pc == 8472 || !((writesRegs ins.op ++ scoreEventWrites ins.op).contains 6496))) &&
  match ins.op with
  | .bra dest _ => 7755 ≤ dest && (if pc < 8769 then dest ≤ 8769 || dest == 9201
      else 9201 ≤ dest && dest ≤ 9205) &&
      ((dest ≤ 8472) || (8472 < pc) || (9201 ≤ dest))
  | .brx .. => false
  | _ => true

private theorem secondCodeAt {pc : Nat} {ins : Instr}
    (hLo : 7755 ≤ pc) (hHi : pc < 9205)
    (hBand : pc < 8769 ∨ 9201 ≤ pc) (hc : kernel.code[pc]? = some ins) :
    secondCode pc ins = true := by
  let code := ((kernel.code.drop 7755).take (9205 - 7755)).zipIdx 7755
  have hAll : code.all (fun (i, site) => if site < 8769 || 9201 ≤ site then secondCode site i
      else true) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hm : (ins, pc) ∈ code := by
    apply List.mem_of_getElem? (i := pc - 7755)
    dsimp only [code]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  have hBand' : (decide (pc < 8769) || decide (9201 ≤ pc)) = true := by simpa using hBand
  simpa only [hBand', ↓reduceIte] using List.all_eq_true.mp hAll (ins, pc) hm

private theorem secondPhaseSeed {l : Launch} {g : Nat} {s u : TState}
    (hPc : s.pc = 8472) (hClean : s.fault = none)
    (ht : Tau kernel Assumptions.all l g s u) : u.regs 6496 = some (b32 0) := by
  have hc : kernel.code[s.pc]? = some ⟨none,
      .move ⟨.scalar, .int .b 32, [some 6496], [.imm 0]⟩⟩ := hPc.symm ▸ Flow.code_8472
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; decide
  have hExec : execLocalA Assumptions.all l g s
      (.move ⟨.scalar, .int .b 32, [some 6496], [.imm 0]⟩) =
        .ok (next (setReg s 6496 (b32 0))) := by
    rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, DType.width, Value.bytes,
      b32, bind, Except.bind, pure, Except.pure]
    rfl
  obtain rfl := tau_det ht (out_tau hClean hc rfl rfl hExec)
  simp only [next, setReg, Function.update_self]

private def SecondCursor (s : TState) : Prop :=
  secondWindow s.pc ∧ s.sub ≤ 3 ∧ (8472 < s.pc → s.pc ≤ 8769 → s.regs 6496 = some (b32 0))

private theorem secondCursorStep {l : Launch} {g : Nat} {s u : TState} {event : Option Event}
    (h : SecondCursor s) (hPc : s.pc ≠ 8769) (hEnd : s.pc < 9205)
    (hw : WStep kernel Assumptions.all l g s event u) : SecondCursor u := by
  rcases h with ⟨⟨hLo, hWindow⟩, hSub, hPhase⟩
  have hBand : s.pc < 8769 ∨ 9201 ≤ s.pc := by omega
  have hAudit {i : Instr} (hc : kernel.code[s.pc]? = some i) :=
    secondCodeAt hLo hEnd hBand hc
  have keep {i : Instr} (hc : kernel.code[s.pc]? = some i) (hBefore : s.pc ≠ 8472) :
      6496 ∉ writesRegs i.op ++ scoreEventWrites i.op := by
    have hh := (Bool.and_eq_true_iff.mp (hAudit hc)).1
    have hFalse : (s.pc == 8472) = false := by simp [hBefore]
    simpa only [hFalse, Bool.false_or, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] using (Bool.and_eq_true_iff.mp hh).2
  have finish (hNext : u.pc = s.pc ∨ u.pc = s.pc + 1) (hSmall : u.sub ≤ 3)
      (hCarry : s.pc ≠ 8472 → u.regs 6496 = s.regs 6496)
      (hSeed : s.pc = 8472 → u.regs 6496 = some (b32 0)) : SecondCursor u := by
    refine ⟨⟨by omega, by omega⟩, hSmall, ?_⟩
    intro hlo hhi
    by_cases hs : s.pc = 8472
    · exact hSeed hs
    · exact (hCarry hs).trans (hPhase (by omega) (by omega))
  rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hClean, hTau⟩ := correctionTauFrame hOff ht
    have hSeed (hs : s.pc = 8472) := secondPhaseSeed hs hClean ht
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hLoc⟩
    · exact finish (.inr rfl) (Nat.zero_le _) (fun _ => rfl) hSeed
    have hNext := hLoc.pc
    have hJump := (Bool.and_eq_true_iff.mp (hAudit hc)).2
    have hCarry (hs : s.pc ≠ 8472) := hLoc.regs 6496
      (fun hr => keep hc hs (List.mem_append_left _ hr))
    cases hi : i.op <;> simp only [hi, nextPc, BrxTarget, or_false] at hNext
    case brx => simp [hi] at hJump
    case bra dest uni =>
      simp only [hi, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hJump
      have hBranch : (dest ≤ 8769 ∨ 9201 ≤ dest ∧ dest ≤ 9205) ∧
          (dest ≤ 8769 → s.pc ≤ 8769) := by
        by_cases ha : s.pc < 8769
        · rcases (by simpa only [ha, ↓reduceIte, Bool.or_eq_true,
              decide_eq_true_eq, beq_iff_eq] using hJump.1.2 : dest ≤ 8769 ∨ dest = 9201)
            with hd | hd
          · exact ⟨.inl hd, fun _ => ha.le⟩
          · exact ⟨.inr ⟨by omega, by omega⟩, fun _ => ha.le⟩
        · have hd : 9201 ≤ dest ∧ dest ≤ 9205 := by
            simpa only [ha, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] using hJump.1.2
          exact ⟨.inr hd, by omega⟩
      refine ⟨⟨hNext.symm ▸ hJump.1.1, hNext.symm ▸ hBranch.1⟩, hLoc.sub.symm ▸ hSub, ?_⟩
      intro hn hh
      have hPrior : 8472 < s.pc := by omega
      exact (hCarry (by omega)).trans (hPhase hPrior (hBranch.2 (hNext ▸ hh)))
    all_goals exact finish (.inr hNext) (hLoc.sub.symm ▸ hSub) hCarry hSeed
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hSeedOff : s.pc ≠ 8472 := by
      intro hs
      rw [hs, Flow.code_8472] at hc
      obtain rfl := Option.some.inj hc.symm
      cases hLocal
    have hOp : correctionReturningOp i.op = true := by
      simpa only [hLocal, Bool.false_or] using
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (hAudit hc)).1).1
    obtain ⟨hProg, hRegs⟩ := correctionEventProgress hc hOp hSub
      (fun hr => keep hc hSeedOff (List.mem_append_right _ hr)) he
    have hNext := hProg.pc.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
    exact finish hNext hProg.sub (fun _ => hRegs) (fun h => (hSeedOff h).elim)

private theorem secondPollParity {l : Launch} {g : Nat} {s u : TState} {loc : Loc}
    {parity : Nat} {ok : Bool} {scope : MbarScope}
    (hPc : s.pc = 8769) (hZero : s.regs 6496 = some (b32 0))
    (he : EStep kernel Assumptions.all l g s ⟨8769, .wait loc parity ok true scope⟩ (some u)) :
    parity = 0 := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hPc, Flow.code_8769] at hc
  obtain rfl := Option.some.inj hc
  have hBits := readBits_b32 (L := l) (g := g) hZero (by decide : 0 < 2 ^ 32)
  have hWide : (Assumptions.all.any (·.clusterScopeMbar s.pc)) = false := rfl
  change Fires s.pc (eventTmpl Assumptions.all l g s
    (.mbarWait 9890 6499 0 (.reg 6496) true .cta)) _ _ at hf
  cases hLoc : mbarLoc l g s 6499 0 with
  | error f =>
    simp [eventTmpl, tmaTmpl, hLoc, hWide, widenMbarScope, bind, Except.bind, ofExec] at hf
    cases hf.2
  | ok m =>
    simp only [eventTmpl, tmaTmpl, hLoc, hBits, hWide, widenMbarScope, bind,
      Except.bind, pure, Except.pure, ofExec, Bool.false_eq_true, ↓reduceIte] at hf
    obtain ⟨_, hF, _⟩ := hf
    exact (Kind.wait.inj (congrArg Event.kind hF)).2.1

private theorem secondPollPrecedes {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} {target : Event}
    (hw : Walk kernel Assumptions.all l g s events visits) (hCursor : SecondCursor s)
    {index : Nat} (he : events[index]? = some target) (hLate : 8769 < target.pc)
    (hEarly : target.pc < 9201) :
    ∃ wait < index, ∃ loc scope, events[wait]? = some ⟨8769, .wait loc 0 true true scope⟩ := by
  generalize hLen : visits.length = fuel
  induction fuel using Nat.strong_induction_on generalizing s events visits index with
  | h fuel ih =>
    cases hw with
    | stop => simp at he
    | last hs =>
      have hWindow := hCursor.1.2
      have hSource := estep_source_pc hs
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst target; omega
      | succ index => simp at he
    | @tau s u events visits ht hw =>
      have hWindow := hCursor.1.2
      have hEnd : s.pc < 9205 := by
        by_contra hn
        have hOnly := correctionReturnTail (by omega : s.pc = 9205) (.tau ht hw)
          (List.mem_of_getElem? he)
        omega
      have hPc : s.pc ≠ 8769 := by
        intro hs
        have hStop : Stops kernel Assumptions.all l g s := by
          cases hf : s.fault with
          | some fault => exact ⟨.ub fault, by simp only [out, hf]⟩
          | none => exact ⟨_, out_event hf (hs.symm ▸ Flow.code_8769) rfl rfl⟩
        exact not_tau_of_stops hStop ht
      have hNext := secondCursorStep hCursor hPc hEnd (.inl ⟨rfl, ht⟩)
      have hh : visits.length < fuel := by simp at hLen; omega
      exact ih visits.length hh hw hNext he rfl
    | @ev s u event events visits hEvent hw =>
      have hWindow := hCursor.1.2
      have hSource := estep_source_pc hEvent
      cases index with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at he; subst target; omega
      | succ index =>
        have hTail : events[index]? = some target := he
        by_cases hPc : s.pc = 8769
        · obtain ⟨ok, rfl, _, hClean, loc, parity, scope, rfl⟩ :=
            correctionWait_step 2 hPc hEvent
          have hZero := hCursor.2.2 (by omega) hPc.le
          rw [hPc] at hEvent
          have hParity := secondPollParity hPc hZero hEvent
          subst parity
          cases ok with
          | true =>
            refine ⟨0, by omega, loc, scope, ?_⟩
            rw [hPc]
            rfl
          | false =>
            obtain ⟨v, hRun, hv, hSub, _, hRegs, _, _⟩ :=
              correctionPollLocals (l := l) (g := g) 2 hPc hClean false
            obtain hNil | ⟨post, hPostLen, _, hWalk⟩ := Mma.advanceWalkLocals hRun hw
            · subst events
              simp at hTail
            change v.pc = 8769 at hv
            have hSmall := hCursor.2.1
            have hValue : v.regs 6496 = some (b32 0) := by
              rw [hRegs]
              simpa [next, setReg, correctionPoll] using hZero
            have hV : SecondCursor v := ⟨⟨by omega, .inl hv.le⟩, by omega, fun _ _ => hValue⟩
            have hBound : post.length < fuel := by simp at hLen; omega
            obtain ⟨k, hk, loc', scope', hGet⟩ := ih post.length hBound hWalk hV hTail rfl
            exact ⟨k + 1, by omega, loc', scope', hGet⟩
        · have hEnd : s.pc < 9205 := by
            by_contra hn
            have hEq := correctionReturnTail (by omega : s.pc = 9205) (.ev hEvent hw)
              (List.mem_cons_of_mem _ (List.mem_of_getElem? hTail))
            omega
          have hNext := secondCursorStep hCursor hPc hEnd (.inr ⟨_, rfl, hEvent⟩)
          have hBound : visits.length < fuel := by simp at hLen; omega
          obtain ⟨k, hk, loc, scope, hGet⟩ := ih visits.length hBound hw hNext hTail rfl
          exact ⟨k + 1, by omega, loc, scope, hGet⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem secondAcquireBeforeEvent {g index : Nat} {target : Event}
    (he : X.get (g,index) = some target) (hBand : 8769 < target.pc ∧ target.pc < 9201) :
    ∃ wait, SecondOutputAcquire l X wait ∧ po X wait (g,index) := by
  have hHint : target.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  have hWarp : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  have hg := Step.CtaBar.thread_lt_of_get hX he
  obtain ⟨s, o, _, hAt, _, _, _, _, _, _, hRun, hIndex⟩ :=
    correctionEntryBeforeEvent hp hX (g := g) hg hWarp.1 hWarp.2 he (.inl (by omega))
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
  have hGet : ((X.tr g).drop 9)[index - 9]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hCursor : SecondCursor s :=
    ⟨⟨hAt.1.ge, .inl (by rw [hAt.1]; decide)⟩, by rw [hAt.2.1]; decide,
      fun hz _ => (by rw [hAt.1] at hz; omega : False).elim⟩
  obtain ⟨k, hk, loc, scope, hPoll⟩ := secondPollPrecedes hWalk hCursor hGet hBand.1 hBand.2
  have hWait : X.get (g, 9 + k) = some ⟨8769, .wait loc 0 true true scope⟩ := by
    rw [List.getElem?_drop] at hPoll
    exact hPoll
  have hLoc := secondCorrectionWaitAddress hp hX hWait
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  exact ⟨(g, 9 + k), ⟨_, scope, hWait, by rw [← hLoc]⟩,
    po_of_source_not_access rfl (by omega) hLen (by rw [hWait]; rfl)⟩

/-- A real stage-one correction write follows its lane's parity-zero MMA output acquire. -/
theorem _root_.PTX.Kernels.TmlFa4Fwd.Thread.StageStagingWrite.secondAcquire {writer : EvId}
    {a : Acc} {bytes : List Byte} (h : StageStagingWrite X writer 1 a bytes) :
    ∃ wait, SecondOutputAcquire l X wait ∧ po X wait writer := by
  obtain ⟨g,index⟩ := writer
  obtain ⟨box, chunk, hStore⟩ := h.decoded
  exact secondAcquireBeforeEvent hp hX hStore
    ((by decide : ∀ b c, 8769 < outputStorePc 1 b c ∧ outputStorePc 1 b c < 9201) box chunk)

/-- Every actual load of the second output stage follows its lane's acquire. -/
theorem secondAcquireBeforeFinalizationLoad {i : EvId} {chunk : Fin 16} {address : Nat}
    {values : List Value} {shape : TcShape}
    (he : X.get i = some ⟨finalizeLoadPc 1 chunk, .tc (.ld address values shape)⟩) :
    ∃ wait, SecondOutputAcquire l X wait ∧ po X wait i := by
  obtain ⟨g,index⟩ := i
  exact secondAcquireBeforeEvent hp hX he
    ((by decide : ∀ c, 8769 < finalizeLoadPc 1 c ∧ finalizeLoadPc 1 c < 9201) chunk)

/-- A terminal joint probability credit follows the successful MMA output acquire. -/
theorem secondOutputAcquireBeforeTerminalCredit {g index : Nat} {e : Event}
    (he : X.get (g,index) = some e) (hSite : e.pc = 9055) :
    ∃ wait, SecondOutputAcquire l X wait ∧ po X wait (g,index) := by
  exact secondAcquireBeforeEvent hp hX he ⟨by omega, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
