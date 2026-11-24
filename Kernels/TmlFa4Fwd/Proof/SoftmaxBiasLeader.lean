-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMbarAddress
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Flow.Code.Part051
import Kernels.TmlFa4Fwd.Flow.Code.Part052
import Kernels.TmlFa4Fwd.Flow.Code.Part056
import Kernels.TmlFa4Fwd.Flow.Code.Part078
import Kernels.TmlFa4Fwd.Flow.Code.Part079
import Kernels.TmlFa4Fwd.Flow.Code.Part082
import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

private inductive BiasLeaderValue
  | tid | lane | skip
  deriving DecidableEq

private structure BiasLeaderFact where
  write : Nat
  last : Nat
  reg : Nat
  value : BiasLeaderValue
  deriving DecidableEq

private def biasLeaderFacts : List BiasLeaderFact :=
  [⟨3293, 3365, 2775, .tid⟩, ⟨3365, 3366, 2847, .lane⟩, ⟨3366, 3584, 482, .skip⟩,
    ⟨5034, 5102, 3967, .tid⟩, ⟨5102, 5103, 4035, .lane⟩, ⟨5103, 5272, 632, .skip⟩]

private def BiasLeaderFact.live (f : BiasLeaderFact) (pc : Nat) : Prop :=
  f.write < pc ∧ pc ≤ f.last

private instance (f : BiasLeaderFact) (pc : Nat) : Decidable (f.live pc) :=
  inferInstanceAs (Decidable (f.write < pc ∧ pc ≤ f.last))

private def BiasLeaderValue.value (v : BiasLeaderValue) (l : Launch) (g : Nat) : Value :=
  match v with
  | .tid => b32 (g % l.block)
  | .lane => b32 (laneOf l g)
  | .skip => .pred (laneOf l g ≠ 0)

private def releaseBody (repeated : Bool) (pc : Nat) : Prop :=
  if repeated then 5273 ≤ pc ∧ pc ≤ 5278 else 3585 ≤ pc ∧ pc ≤ 3590

private instance (repeated : Bool) (pc : Nat) : Decidable (releaseBody repeated pc) :=
  inferInstanceAs (Decidable (if repeated then 5273 ≤ pc ∧ pc ≤ 5278 else 3585 ≤ pc ∧ pc ≤ 3590))

private structure RawLeaderFrame (l : Launch) (g : Nat) (s : TState) : Prop where
  facts : ∀ f ∈ biasLeaderFacts, f.live s.pc → s.regs f.reg = some (f.value.value l g)
  release : ∀ repeated, releaseBody repeated s.pc → laneOf l g = 0

/-- Exact physical leader selection along a softmax role trace. -/
@[no_expose] def BiasLeaderFrame := RawLeaderFrame

private def leaderCheck (pc : Nat) (op : Op) : Bool :=
  (op.isLocal || scoreEventOp op) &&
    (biasLeaderFacts.all (fun f => !decide (f.live pc) ||
      !((writesRegs op ++ scoreEventWrites op).contains f.reg))) &&
      match op with
      | .bra dst _ => (biasLeaderFacts.all fun f => decide (f.live dst → f.live pc)) &&
          ([false,true].all fun b => decide (releaseBody b dst → releaseBody b pc))
      | .brx .. => false
      | _ => true

private theorem leaderCheckAt {pc : Nat} {ins : Instr}
    (hLo : 3103 ≤ pc) (hHi : pc < 7742) (hc : kernel.code[pc]? = some ins) :
    leaderCheck pc ins.op = true := by
  let code := ((kernel.code.drop 3103).take (7742-3103)).zipIdx 3103
  have hTable : code.all (fun (ins, pc) => leaderCheck pc ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hTable (ins,pc)
  apply List.mem_of_getElem? (i := pc - 3103)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private def leaderSegCheck (pc : Nat) (seg : SegMatch CuteSlot) : Bool :=
  (biasLeaderFacts.all fun f => !decide (f.live seg.stop) ||
    (decide (f.live pc) && !(scoreSegmentWrites seg).contains f.reg)) &&
    ([false,true].all fun b => decide (releaseBody b seg.stop → releaseBody b pc))

private theorem leaderSegCheckAt {pc : Nat} {seg : SegMatch CuteSlot}
    (hSite : pc ∈ Assumptions.swExp2Sites) (hSeg : cuteExp2.matchAt kernel pc = some seg) :
    leaderSegCheck pc seg = true := by
  have hAll : Assumptions.swExp2Sites.all (fun pc =>
    match cuteExp2.matchAt kernel pc with
    | none => false
    | some seg => leaderSegCheck pc seg) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have h := List.all_eq_true.mp hAll _ hSite
  rwa [hSeg] at h

/-- The role entry has yet to compute a Bias leader predicate. -/
theorem leaderStart {l : Launch} {g : Nat} {s : TState} (hs : s.pc = 3103) :
    BiasLeaderFrame l g s := by
  constructor
  · intro f hf h
    rw [hs] at h
    change f ∈ [_, _, _, _, _, _] at hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (by decide : ¬ BiasLeaderFact.live _ 3103) h |>.elim
  · intro b hb
    rw [hs] at hb
    cases b <;> exact (by decide : ¬ releaseBody _ 3103) hb |>.elim


private def leaderPred (repeated : Bool) : Nat := if repeated then 632 else 482
private def leaderGate (repeated : Bool) : Nat := if repeated then 5272 else 3584

private def leaderRawOp (r : Nat) : Op :=
  .move ⟨.scalar, .int .u 32, [some r], [.sreg ⟨.tid, some .x⟩]⟩

private def leaderLaneOp (r src : Nat) : Op :=
  .int ⟨.and, .int .b 32, false, [some r], [.reg src, .imm 31]⟩

private def leaderPredOp (r src : Nat) : Op :=
  .int ⟨.setp .ne none, .int .b 32, false, [some r], [.reg src, .imm 0]⟩

private theorem leaderTidExec {p : Params} {l : Launch} {m : Mem0} {g r : Nat} {s : TState}
    (hp : Pre p l m) :
    execLocal l g s (leaderRawOp r) = .ok (next (setReg s r (b32 (g % l.block)))) := by
  have hTid := (sregValue_oneDim hp.cluster.2.2 g).1
  have hB : g % l.block < 2 ^ 32 := by
    rw [hp.block]
    have h := Nat.mod_lt g (by decide : 0 < 512)
    omega
  unfold leaderRawOp
  rw [execLocal_move rfl]
  simp [execMove, readValue, readBits, SReg.width, DType.width, Value.bytes, hTid,
    bind, Except.bind, pure, Except.pure, truncBits_ofNat hB (by decide), b32]

private theorem leaderLaneExec {p : Params} {l : Launch} {m : Mem0} {g r src : Nat} {s : TState}
    (hp : Pre p l m) (hr : s.regs src = some (b32 (g % l.block))) :
    execLocal l g s (leaderLaneOp r src) = .ok (next (setReg s r (b32 (laneOf l g)))) := by
  have hB : g % l.block < 2 ^ 32 := by
    rw [hp.block]
    have h := Nat.mod_lt g (by decide : 0 < 512)
    omega
  have hRead := readBits_b32 (L := l) (g := g) hr hB
  have hImm : readBits l g s 32 (.imm 31) = .ok 31#64 := rfl
  have hBits : BitVec.ofNat 64 (g % l.block) &&& (31#64) =
      BitVec.ofNat 64 (laneOf l g) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    have hBound : g % l.block < 2 ^ 64 := by omega
    have hLane : laneOf l g < 2 ^ 64 := by unfold laneOf; omega
    rw [Nat.mod_eq_of_lt hBound, Nat.mod_eq_of_lt hLane]
    change g % l.block &&& (2^5-1) = g % l.block % 2^5
    exact Nat.and_two_pow_sub_one_eq_mod _ _
  unfold leaderLaneOp
  rw [execLocal_int rfl]
  simp only [execInt, DType.width, hRead, hImm, bind, Except.bind, pure, Except.pure,
    ite_eq_right (by decide : ¬ (32 : Nat) = 1), b32, hBits]

private theorem leaderPredExec {l : Launch} {g r src : Nat} {s : TState}
    (hr : s.regs src = some (b32 (laneOf l g))) :
    execLocal l g s (leaderPredOp r src) =
      .ok (next (setReg s r (.pred (laneOf l g ≠ 0)))) := by
  have hB : laneOf l g < 2 ^ 32 := by unfold laneOf; omega
  have hBound : laneOf l g < 2 ^ 64 := by omega
  have hRead := readBits_b32 (L := l) (g := g) hr hB
  have hImm : readBits l g s 32 (.imm 0) = .ok 0#64 := rfl
  unfold leaderPredOp
  rw [execLocal_int rfl]
  simp only [execInt, compare, DType.width, DType.kind?, hRead, hImm, bind, Except.bind,
    pure, Except.pure, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hBound]
  by_cases h : laneOf l g = 0
  · simp [h]
  · simp [h]

private theorem leaderWriteStep {l : Launch} {g r : Nat} {s u : TState} {ev : Option Event}
    {op : Op} {value : Value} (hc : kernel.code[s.pc]? = some ⟨none, op⟩)
    (hLoc : op.isLocal = true) (hCore : Assumptions.coreOp op = true)
    (hOff : s.pc ∉ Assumptions.swExp2Sites)
    (hRun : execLocal l g s op = .ok (next (setReg s r value)))
    (hStep : WStep kernel Assumptions.all l g s ev u) : u.regs r = some value := by
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, he⟩
  · obtain ⟨ins, hi, _, h⟩ := tauScoreSource hTau
    obtain rfl := Option.some.inj (hc.symm.trans hi)
    rcases h with ⟨_, hBad⟩ | ⟨_, _, hDo⟩
    · cases hBad
    · change execLocalA Assumptions.all l g s op = .ok u at hDo
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff hCore,
        execLocalA_nil, hRun] at hDo
      obtain rfl := Except.ok.inj hDo
      simp [next, setReg]
  · obtain ⟨ins, hi, hBad, _⟩ := estep_event_source he
    obtain rfl := Option.some.inj (hc.symm.trans hi)
    change op.isLocal = false at hBad
    rw [hLoc] at hBad
    cases hBad

private theorem leaderDefines {p : Params} {l : Launch} {m : Mem0} {g : Nat} {s u : TState}
    {ev : Option Event} (hp : Pre p l m) {f : BiasLeaderFact} (hf : f ∈ biasLeaderFacts)
    (hPc : s.pc = f.write) (hFrame : BiasLeaderFrame l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    u.regs f.reg = some (f.value.value l g) := by
  change f ∈ [_, _, _, _, _, _] at hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  have keep {f : BiasLeaderFact} (hf : f ∈ biasLeaderFacts) (hlive : f.live s.pc) :=
    (show RawLeaderFrame l g s from hFrame).facts f hf hlive
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change s.pc = _ at hPc
  · exact leaderWriteStep (hPc.symm ▸ Flow.code_3293) rfl rfl
      (by rw [hPc]; decide) (leaderTidExec hp) hStep
  · have hPrev := keep (f := ⟨3293, 3365, 2775, .tid⟩) (by decide) (by rw [hPc]; decide)
    exact leaderWriteStep (hPc.symm ▸ Flow.code_3365) rfl rfl
      (by rw [hPc]; decide) (leaderLaneExec hp hPrev) hStep
  · have hPrev := keep (f := ⟨3365, 3366, 2847, .lane⟩) (by decide) (by rw [hPc]; decide)
    exact leaderWriteStep (hPc.symm ▸ Flow.code_3366) rfl rfl
      (by rw [hPc]; decide) (leaderPredExec hPrev) hStep
  · exact leaderWriteStep (hPc.symm ▸ Flow.code_5034) rfl rfl
      (by rw [hPc]; decide) (leaderTidExec hp) hStep
  · have hPrev := keep (f := ⟨5034, 5102, 3967, .tid⟩) (by decide) (by rw [hPc]; decide)
    exact leaderWriteStep (hPc.symm ▸ Flow.code_5102) rfl rfl
      (by rw [hPc]; decide) (leaderLaneExec hp hPrev) hStep
  · have hPrev := keep (f := ⟨5102, 5103, 4035, .lane⟩) (by decide) (by rw [hPc]; decide)
    exact leaderWriteStep (hPc.symm ▸ Flow.code_5103) rfl rfl
      (by rw [hPc]; decide) (leaderPredExec hPrev) hStep

private theorem leaderBranchCode (repeated : Bool) :
    kernel.code[leaderGate repeated]? = some
      ⟨some (leaderPred repeated, false), .bra (leaderGate repeated + 7) false⟩ := by
  cases repeated
  · exact Flow.code_3584
  · exact Flow.code_5272

private theorem leaderBranchGuard {l : Launch} {g : Nat} {s : TState}
    (repeated : Bool) (hPc : s.pc = leaderGate repeated) (hF : BiasLeaderFrame l g s) :
    guardHolds s (some (leaderPred repeated, false)) = .ok (decide (laneOf l g ≠ 0)) := by
  have hReg : s.regs (leaderPred repeated) = some (.pred (laneOf l g ≠ 0)) := by
    cases repeated
    · exact (show RawLeaderFrame l g s from hF).facts ⟨3366, 3584, 482, .skip⟩ (by decide)
        (by rw [hPc]; decide)
    · exact (show RawLeaderFrame l g s from hF).facts ⟨5103, 5272, 632, .skip⟩ (by decide)
        (by rw [hPc]; decide)
  simp [guardHolds, readReg, hReg, bind, Except.bind, pure, Except.pure]

private theorem leaderBodyEntry {pc dst : Nat} (repeated : Bool) (hNext : dst = pc + 1)
    (hBody : releaseBody repeated dst) : releaseBody repeated pc ∨ pc = leaderGate repeated := by
  cases repeated <;> simp [releaseBody, leaderGate] at hBody ⊢ <;> omega

/-- Preserve decoded Bias leader selection through the actual role. -/
theorem leaderWalkStep {p : Params} {l : Launch} {m : Mem0} {g : Nat} {s u : TState}
    {ev : Option Event} (hp : Pre p l m) (hLo : 3103 ≤ s.pc) (hHi : s.pc < 7742)
    (hSub : s.sub ≤ 3) (hFrame : BiasLeaderFrame l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u) :
    BiasLeaderFrame l g u := by
  have preserve {ins : Instr} (hc : kernel.code[s.pc]? = some ins)
      (hKeep : ∀ r, r ∉ (writesRegs ins.op ++ scoreEventWrites ins.op) → u.regs r = s.regs r)
      (hEntry : ∀ f ∈ biasLeaderFacts, f.live u.pc → f.live s.pc ∨ s.pc = f.write)
      (hRelease : ∀ b, releaseBody b u.pc → laneOf l g = 0) : BiasLeaderFrame l g u := by
    refine ⟨?_, hRelease⟩
    intro f hf hu
    rcases hEntry f hf hu with hs | hs
    · have hChecked := (Bool.and_eq_true_iff.mp (leaderCheckAt hLo hHi hc)).1
      have hWrites := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hChecked).2 f hf
      have hr : f.reg ∉ writesRegs ins.op ++ scoreEventWrites ins.op := by
        simpa [hs] using hWrites
      exact (hKeep _ hr).trans ((show RawLeaderFrame l g s from hFrame).facts f hf hs)
    · exact leaderDefines hp hf hs hFrame hStep
  have atNext (hNext : u.pc = s.pc + 1) {f : BiasLeaderFact} (hf : f.live u.pc) :
      f.live s.pc ∨ s.pc = f.write := by
    unfold BiasLeaderFact.live at hf ⊢
    omega
  rcases hStep with ⟨rfl, hTau⟩ | ⟨e, rfl, hE⟩
  · obtain ⟨ins, hc, _, hActual⟩ := tauScoreSource hTau
    rcases hActual with ⟨rfl, hSkip⟩ | ⟨hGuard, _, hExec⟩
    · refine preserve hc (fun _ _ => rfl) (fun _ _ hu => atNext rfl hu) ?_
      intro repeated hB
      rcases leaderBodyEntry repeated rfl hB with hIn | hGate
      · exact (show RawLeaderFrame l g s from hFrame).release repeated hIn
      · rw [hGate, leaderBranchCode repeated] at hc
        obtain rfl := Option.some.inj hc.symm
        rw [leaderBranchGuard repeated hGate hFrame] at hSkip
        simpa using hSkip
    · rcases scoreExecLocal hExec with hFrame' | ⟨seg, hSite, hMatch, hRun⟩
      · have hChecked := (Bool.and_eq_true_iff.mp (leaderCheckAt hLo hHi hc)).2
        refine preserve hc (fun r hr => hFrame'.regs r (fun h => hr (List.mem_append_left _ h)))
          ?_ ?_
        · intro f hf hu
          have hPc := hFrame'.pc
          cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
          case bra dst aligned =>
            rw [ho] at hChecked
            have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hChecked).1 f hf
            exact .inl (of_decide_eq_true h (hPc ▸ hu))
          case brx => simp [ho] at hChecked
          all_goals exact atNext hPc hu
        · intro repeated hB
          have hPc := hFrame'.pc
          by_cases hGate : s.pc = leaderGate repeated
          · rw [hGate, leaderBranchCode repeated] at hc
            obtain rfl := Option.some.inj hc.symm
            change u.pc = leaderGate repeated + 7 ∨ BrxTarget _ u.pc at hPc
            simp only [BrxTarget, or_false] at hPc
            cases repeated <;> rw [hPc] at hB
            all_goals exact (by decide : ¬ releaseBody _ _) hB |>.elim
          cases ho : ins.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
          case bra dst aligned =>
            rw [ho] at hChecked
            have h := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hChecked).2 repeated
              (by cases repeated <;> simp)
            exact (show RawLeaderFrame l g s from hFrame).release repeated
              (of_decide_eq_true h (hPc ▸ hB))
          case brx => simp [ho] at hChecked
          all_goals
            exact (show RawLeaderFrame l g s from hFrame).release repeated
              ((leaderBodyEntry repeated hPc hB).resolve_right hGate)
      · obtain ⟨hPc, _, _, hKeep⟩ := scoreSegmentFrame hRun
        obtain ⟨hF, hR⟩ := Bool.and_eq_true_iff.mp (leaderSegCheckAt hSite hMatch)
        constructor
        · intro f hf hLive
          rw [hPc] at hLive
          have hf := List.all_eq_true.mp hF f hf
          simp [hLive] at hf
          exact (hKeep _ hf.2).trans
            ((show RawLeaderFrame l g s from hFrame).facts f (by assumption) hf.1)
        · intro repeated hB
          rw [hPc] at hB
          have hb := List.all_eq_true.mp hR repeated (by cases repeated <;> simp)
          exact (show RawLeaderFrame l g s from hFrame).release repeated (of_decide_eq_true hb hB)
  · obtain ⟨ins, hc, hLocal, _⟩ := estep_event_source hE
    have hCheck := (Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (leaderCheckAt hLo hHi hc)).1).1
    have hOp : scoreEventOp ins.op = true := by simpa only [hLocal, Bool.false_or] using hCheck
    have hPc := (scoreEventStep (r := 2535) hc hOp hSub (by
      have hAll : ((kernel.code.drop 3103).take (7742 - 3103)).all (fun i =>
          !(scoreEventWrites i.op).contains 2535) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      have hGet : ((kernel.code.drop 3103).take (7742 - 3103))[s.pc - 3103]? = some ins := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo]
        exact hc
      simpa using List.all_eq_true.mp hAll _ (List.mem_of_getElem? hGet)) hE).1.pc
    refine preserve hc (fun _ hr =>
      (scoreEventStep hc hOp hSub (fun h => hr (List.mem_append_right _ h)) hE).2) ?_ ?_
    · intro f hf hu
      rcases hPc with h | h
      · exact atNext h.1 hu
      · exact .inl (h.1 ▸ hu)
    · intro repeated hB
      rcases hPc with h | h
      · rcases leaderBodyEntry repeated h.1 hB with hIn | hGate
        · exact (show RawLeaderFrame l g s from hFrame).release repeated hIn
        · rw [hGate, leaderBranchCode repeated] at hc
          obtain rfl := Option.some.inj hc.symm
          cases hLocal
      · exact (show RawLeaderFrame l g s from hFrame).release repeated (h.1 ▸ hB)

/-- Within the repeated Bias read corridor, the release predicate is the physical lane test. -/
theorem BiasLeaderFrame.repeatedPredicate {l : Launch} {g : Nat} {s : TState}
    (h : BiasLeaderFrame l g s) (hLo : 5103 < s.pc) (hHi : s.pc ≤ 5272) :
    s.regs 632 = some (.pred (laneOf l g ≠ 0)) :=
  (show RawLeaderFrame l g s from h).facts ⟨5103,5272,632,.skip⟩ (by decide) ⟨hLo,hHi⟩

/-- Only the physical leader of a softmax warp executes an actual Bias return instruction. -/
theorem actualBiasReturnLeader {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g,j) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [3590, 5278]) : laneOf l g = 0 := by
  have hs : pc = 3590 ∨ pc = 5278 := by simpa using hSite
  obtain ⟨w, hW, s, o, hPc, hF, hE⟩ := softmaxRoleEventWith hp hX he (by dsimp; omega)
    (by dsimp; omega) (Q := fun _ => BiasLeaderFrame l g)
    (fun _ _ h => leaderStart h.1)
    (by intro _ _ _ _ hLo hHi hSub _ hF h; exact leaderWalkStep hp hLo hHi hSub hF h)
  change s.pc = pc at hPc
  rcases hs with rfl | rfl
  · exact (show RawLeaderFrame l g s from hF).release false (by rw [hPc]; decide)
  · exact (show RawLeaderFrame l g s from hF).release true (by rw [hPc]; decide)
end PTX.Kernels.TmlFa4Fwd.Softmax
