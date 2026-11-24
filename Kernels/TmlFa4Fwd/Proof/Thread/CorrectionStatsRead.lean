-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
public import Kernels.TmlFa4Fwd.Proof.CorrectionStats
import Kernels.TmlFa4Fwd.Flow.Code.Part123
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Proof.CorrectionMbarAddress
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

private def definitionPc (i : Fin 4) : Nat := (#v[7748, 7749, 7935, 7936] : Vector Nat 4)[i]

private def definitionRegister (i : Fin 4) : Nat := (#v[1612, 1613, 5951, 1627] : Vector Nat 4)[i]

private def definitionWord (l : Launch) (g : Nat) (i : Fin 4) : Value :=
  (#v[b32 (g % l.block), b32 (rowOf l g), b32 (4 * rowOf l g),
    b32 (l.sharedBase + 4 * rowOf l g)] : Vector Value 4)[i]

private def inScope (i : Fin 4) (pc : Nat) : Prop := definitionPc i < pc ∧ pc < 9201

private instance (i : Fin 4) (pc : Nat) : Decidable (inScope i pc) :=
  inferInstanceAs (Decidable (definitionPc i < pc ∧ pc < 9201))

private def StatisticsAddressFrame (l : Launch) (g : Nat) (s : TState) : Prop :=
  s.regs 2535 = some (b32 l.sharedBase) ∧
    ∀ i, inScope i s.pc → s.regs (definitionRegister i) = some (definitionWord l g i)

private def statsWrite (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def frameCode (site : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) && !(statsWrite i.op).contains 2535 &&
  (List.finRange 4).all (fun j =>
    ((site == definitionPc j && i.guard.isNone && i.op.isLocal) ||
      !(statsWrite i.op).contains (definitionRegister j)) &&
    match i.op with
    | .bra dst _ => decide (inScope j dst → inScope j site)
    | .brx .. => false
    | _ => true)

private theorem frameCodeAt {site : Nat} {i : Instr} (hLo : 7745 ≤ site) (hHi : site < 9205)
    (hc : kernel.code[site]? = some i) : frameCode site i = true := by
  let table := ((kernel.code.drop 7745).take (9205 - 7745)).zipIdx 7745
  have hAll : table.all (fun (ins, pc) => frameCode pc ins) = true := by
    decide +kernel
  have hAt : table[site-7745]? = some (i, site) := by
    dsimp only [table]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hLo, hc]
    rfl
  exact List.all_eq_true.mp hAll _ (List.mem_of_getElem? hAt)

private theorem tauSeed {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} (hFrame : StatisticsAddressFrame l g s)
    (j : Fin 4) (hSite : s.pc = definitionPc j) (hClean : s.fault = none)
    (ht : Tau kernel Assumptions.all l g s u) :
    u.regs (definitionRegister j) = some (definitionWord l g j) := by
  fin_cases j
  · exact tidDefinition hp hSite hClean ht
  · exact rowDefinition hp hSite hClean (hFrame.2 0 (by rw [hSite]; decide)) ht
  · have hReg : s.regs 1613 = some (b32 (rowOf l g)) :=
      hFrame.2 1 (by rw [hSite]; decide)
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    let op : Op := .int ⟨.shl, .int .b 32, false, [some 5951], [.reg 1613, .imm 2]⟩
    have hc : kernel.code[s.pc]? = some ⟨none, op⟩ := hSite.symm ▸ Flow.code_7935
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hSite]; decide
    have hRun : execLocalA Assumptions.all l g s op =
        .ok (next (setReg s 5951 (b32 (4 * rowOf l g)))) := by
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
      rw [execLocalA_nil, show op = .int _ from rfl, execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readReg, hReg, b32, bind, Except.bind, pure,
        Except.pure, truncBits_ofNat (show rowOf l g < 2 ^ 32 by omega) (by decide)]
      have hShift : BitVec.ofNat 64 (rowOf l g) <<< 2 = BitVec.ofNat 64 (4 * rowOf l g) := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
      simp only [show (truncBits 32 (BitVec.ofInt 64 2)).toNat = 2 from rfl,
        show ¬ 2 ≥ 32 by decide, ite_false, hShift,
        truncBits_ofNat (show 4 * rowOf l g < 2 ^ 32 by omega) (by decide)]
    obtain rfl := tau_det ht (out_tau hClean hc rfl rfl hRun)
    simp [definitionRegister, definitionWord, next, setReg]
  · have hReg : s.regs 5951 = some (b32 (4 * rowOf l g)) :=
      hFrame.2 2 (by rw [hSite]; decide)
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hShared := hp.shared.2.1
    let op : Op := .int ⟨.add, .int .s 32, false, [some 1627], [.reg 2535, .reg 5951]⟩
    have hc : kernel.code[s.pc]? = some ⟨none, op⟩ := hSite.symm ▸ Flow.code_7936
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hSite]; decide
    have hRun : execLocalA Assumptions.all l g s op =
        .ok (next (setReg s 1627 (b32 (l.sharedBase + 4 * rowOf l g)))) := by
      rw [Assumptions.execLocalA_all_eq_numeric, Assumptions.execLocalA_eq_nil hOff rfl]
      rw [execLocalA_nil, show op = .int _ from rfl, execLocal_int rfl]
      simp only [execInt, DType.width, readBits, readReg, hReg, hFrame.1, b32, bind, Except.bind,
        pure, Except.pure, truncBits_ofNat (show l.sharedBase < 2 ^ 32 by omega) (by decide),
        truncBits_ofNat (show 4 * rowOf l g < 2 ^ 32 by omega) (by decide)]
      rw [← BitVec.ofNat_add,
        truncBits_ofNat (show l.sharedBase + 4 * rowOf l g < 2 ^ 32 by omega) (by decide)]
      simp [readValue, readReg, hFrame.1, hReg, b32]
      rfl
    obtain rfl := tau_det ht (out_tau hClean hc rfl rfl hRun)
    simp [definitionRegister, definitionWord, next, setReg]

private theorem frameStep {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s u : TState} {ev : Option Event} (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205)
    (hSub : s.sub ≤ 3) (hFrame : StatisticsAddressFrame l g s)
    (hStep : WStep kernel Assumptions.all l g s ev u) : StatisticsAddressFrame l g u := by
  have stable {i : Instr} (hc : kernel.code[s.pc]? = some i) {j : Fin 4} :
      ((s.pc == definitionPc j && i.guard.isNone && i.op.isLocal) ||
        !(statsWrite i.op).contains (definitionRegister j)) = true ∧
      (match i.op with
      | .bra dst _ => decide (inScope j dst → inScope j s.pc)
      | .brx .. => false
      | _ => true) = true := by
    have hAudit := frameCodeAt hLo hHi hc
    simp only [frameCode, Bool.and_eq_true] at hAudit
    exact Bool.and_eq_true_iff.mp (List.all_eq_true.mp hAudit.2 j (List.mem_finRange _))
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hKeep : ∀ r, r ∉ statsWrite i.op → u.regs r = s.regs r)
      (hScope : ∀ j, inScope j u.pc → s.pc = definitionPc j ∨ inScope j s.pc)
      (hDef : ∀ j, s.pc = definitionPc j →
        u.regs (definitionRegister j) = some (definitionWord l g j)) :
      StatisticsAddressFrame l g u := by
    have hAudit := frameCodeAt hLo hHi hc
    simp only [frameCode, Bool.and_eq_true] at hAudit
    refine ⟨(hKeep 2535 (by simpa using hAudit.1.2)).trans hFrame.1, ?_⟩
    intro j hScope'
    by_cases hSite : s.pc = definitionPc j
    · exact hDef j hSite
    · have hReg : definitionRegister j ∉ statsWrite i.op := by
        simpa [hSite] using (stable hc (j := j)).1
      exact (hKeep _ hReg).trans (hFrame.2 j ((hScope j hScope').resolve_left hSite))
  rcases hStep with ⟨rfl, ht⟩ | ⟨e, rfl, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hClean, hFlow⟩ := correctionTauFrame hOff ht
    have hSeed := fun j hSite => tauSeed hp hFrame j hSite hClean ht
    rcases hFlow with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · apply finish hc (fun _ _ => rfl) _ hSeed
      intro j hScope
      change definitionPc j < s.pc + 1 ∧ s.pc + 1 < 9201 at hScope
      change s.pc = definitionPc j ∨ definitionPc j < s.pc ∧ s.pc < 9201
      omega
    · apply finish hc (fun r h => hLocal.regs r
        (fun hm => h (List.mem_append_left _ hm))) _ hSeed
      intro j hScope
      have hPc := hLocal.pc
      have hJump := (stable hc (j := j)).2
      cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        have hBranch : inScope j dst → inScope j s.pc :=
          of_decide_eq_true (by simpa only [hop] using hJump)
        exact .inr (hBranch (hPc ▸ hScope))
      case brx => simp [hop] at hJump
      all_goals unfold inScope at hScope ⊢; omega
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hAudit := frameCodeAt hLo hHi hc
    simp only [frameCode, Bool.and_eq_true, hLocal, Bool.false_or] at hAudit
    have hEvent := hAudit.1.1
    have hKept (r : Nat) (hr : r ∉ statsWrite i.op) : r ∉ scoreEventWrites i.op :=
      fun h => hr (List.mem_append_right _ h)
    have hBaseKeep : 2535 ∉ statsWrite i.op := by simpa using hAudit.1.2
    have hPc := (correctionEventProgress hc hEvent hSub (hKept _ hBaseKeep) he).1.pc
    apply finish hc (fun r h => (correctionEventProgress hc hEvent hSub (hKept r h) he).2)
    · intro j hScope
      unfold inScope at hScope ⊢
      rcases hPc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
    · intro j hAt
      have hDefinition : ∀ j : Fin 4,
          kernel.code[definitionPc j]?.map (fun ins => ins.op.isLocal) = some true := by
        decide +kernel
      obtain ⟨ins, hCode, hIsLocal⟩ := Option.map_eq_some_iff.mp (hDefinition j)
      have hEq := Option.some.inj ((hAt ▸ hc).symm.trans hCode)
      rw [hEq, hIsLocal] at hLocal
      cases hLocal

private def StatsSubClear (s : TState) : Prop :=
  ∀ stage kind, s.pc = statsPc stage kind → s.fault = none → s.sub = 0

private def scalarLoad (op : Op) : Bool :=
  match op with | .mem a => a.kind != .load || a.regs.length ≤ 1 | _ => true

private theorem scalarCorrectionLoad {pc : Nat} {ins : Instr} (hLo : 7745 ≤ pc)
    (hHi : pc < 9205) (hCode : kernel.code[pc]? = some ins) :
    match ins.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True := by
  let table := (kernel.code.drop 7745).take (9205-7745)
  have hAll : table.all (fun i => scalarLoad i.op) = true := by decide +kernel
  have hAt : table[pc-7745]? = some ins := by
    dsimp only [table]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hCode]
  have hCheck := List.all_eq_true.mp hAll ins (List.mem_of_getElem? hAt)
  cases hOp : ins.op <;> simp only [hOp, scalarLoad] at hCheck ⊢
  case mem a =>
    intro hKind
    simpa [hKind] using hCheck

/-- Ordinary correction transitions preserve the scratch shape and clear it on advance. -/
theorem correctionScratchStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hScratch : SetupScratch s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    SetupScratch u ∧ (ev = none ∨ u.pc ≠ s.pc → u.sub = 0) := by
  rcases hStep with ⟨rfl,ht⟩ | ⟨e,rfl,he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨ins,hCode,_,h⟩ := correctionTauFrame hOff ht
    obtain ⟨hSubU,hAccU⟩ : u.sub = 0 ∧ u.acc = [] := by
      rcases h with ⟨rfl,_⟩ | ⟨_,hLoc,hFrame⟩
      · exact ⟨rfl,rfl⟩
      · obtain ⟨hSubS,hAccS⟩ := scratchLocal hScratch hCode hLoc
        exact ⟨hFrame.sub.trans hSubS,hFrame.acc.trans hAccS⟩
    exact ⟨SetupScratch.clear hSubU hAccU, fun _ => hSubU⟩
  · obtain ⟨ins,hCode,hNonlocal,_⟩ := estep_event_source he
    have hAudit := frameCodeAt hLo hHi hCode
    simp only [frameCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hAudit
    have hKeep : 2535 ∉ scoreEventWrites ins.op := by
      have hOutside : 2535 ∉ statsWrite ins.op := by simpa using hAudit.1.2
      exact fun h => hOutside (List.mem_append_right _ h)
    obtain ⟨hNext,hClear⟩ := scratchReturningAndClears hScratch hSub hCode hNonlocal
      hAudit.1.1 hKeep (scalarCorrectionLoad hLo hHi hCode) he
    exact ⟨hNext, fun h => hClear (h.resolve_left (by simp))⟩

private theorem statsScratchStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hSub : s.sub ≤ 3)
    (hScratch : SetupScratch s) (hStep : WStep kernel Assumptions.all l g s ev u) :
    SetupScratch u ∧ StatsSubClear u := by
  have hFrame := correctionScratchStep hLo hHi hSub hScratch hStep
  refine ⟨hFrame.1, fun stage kind hSite hFault => ?_⟩
  rcases hStep with ⟨rfl, _⟩ | ⟨_, rfl, he⟩
  · exact hFrame.2 (.inl rfl)
  · by_cases hSame : u.pc = s.pc
    · exact (statsStepSamePcFault stage kind (hSame.symm.trans hSite) he hSame hFault).elim
    · exact hFrame.2 (.inr hSame)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem statisticsReadWarp (stage : Fin 2) (kind : StatsKind) {g j : Nat} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (g, j) = some ⟨statsPc stage kind, .rd a bytes⟩) :
    8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
  have hLate : 173 < statsPc stage kind ∧ statsPc stage kind < 9201 ∧
      statsPc stage kind ∉ registerHintSites := by cases kind <;> fin_cases stage <;> decide
  have hLower : 7747 < statsPc stage kind := by cases kind <;> fin_cases stage <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hLate.1 hLate.2.2
  change roleBodyPc (warpIndex l g) (statsPc stage kind) at hRole
  unfold roleBodyPc at hRole
  rcases hRole with h | h
  · omega
  · split_ifs at h <;> omega

/-- Every actual correction statistics read carries the row pointer derived at role entry. -/
private theorem statsReadRegisterExact (stage : Fin 2) (kind : StatsKind) {g j : Nat} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (g, j) = some ⟨statsPc stage kind, .rd a bytes⟩) :
    ∃ s o, s.pc = statsPc stage kind ∧ s.sub = 0 ∧
      s.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)) ∧
      EStep kernel Assumptions.all l g s ⟨statsPc stage kind, .rd a bytes⟩ o := by
  have hBounds : 173 < statsPc stage kind ∧ statsPc stage kind < 9205 := by
    cases kind <;> fin_cases stage <;> decide
  have hWarp := statisticsReadWarp hp hX stage kind he
  obtain ⟨s, o, hSite, hSub, hFrame, hEvent⟩ := correctionRoleEventWith hp hX hWarp.1 hWarp.2 he
    hBounds.1 hBounds.2
    (Q := fun s => StatisticsAddressFrame l g s ∧ SetupScratch s ∧ StatsSubClear s) (by
      intro t ht
      refine ⟨⟨holds_mem ht.2.2.2.2 (by simp [nonzeroBarrierFacts]), ?_⟩,
        SetupScratch.clear ht.2.1 ht.2.2.1, fun _ _ _ _ => ht.2.1⟩
      intro i hAt
      rw [ht.1] at hAt
      fin_cases i <;> exact (by decide : ¬inScope _ 7745) hAt |>.elim)
    (fun hLo hHi hSub hs hw =>
      ⟨frameStep hp hLo hHi hSub hs.1 hw, statsScratchStep hLo hHi hSub hs.2.1 hw⟩)
  have hScope : inScope 3 (statsPc stage kind) := by cases kind <;> fin_cases stage <;> decide
  have hFault : s.fault = none := by
    cases hf : s.fault with
    | none => rfl
    | some f =>
      obtain ⟨a,hOut,hFire⟩ := hEvent
      simp only [out,hf,Out.ev.injEq] at hOut
      subst a
      exact (Kind.noConfusion (congrArg Event.kind hFire.1))
  exact ⟨s,o,hSite,hFrame.2.2 stage kind hSite hFault,
    hFrame.1.2 3 (by rw [hSite]; exact hScope),hEvent⟩

/-- Every actual correction statistics read carries the row pointer derived at role entry. -/
theorem statsReadRegister (stage : Fin 2) (kind : StatsKind) {g j : Nat} {a : Acc}
    {bytes : List (Option Byte)} (he : X.get (g, j) = some ⟨statsPc stage kind, .rd a bytes⟩) :
    ∃ s o, s.pc = statsPc stage kind ∧ s.sub ≤ 3 ∧
      s.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)) ∧
      EStep kernel Assumptions.all l g s ⟨statsPc stage kind, .rd a bytes⟩ o := by
  obtain ⟨s,o,hPc,hSub,hReg,hEvent⟩ := statsReadRegisterExact hp hX stage kind he
  exact ⟨s,o,hPc,hSub.symm ▸ Nat.zero_le _,hReg,hEvent⟩

omit hp hX in
/-- The correction role's observation of a statistics word. -/
def StatisticsRead (X : Execution) (i : EvId) (stage : Fin 2) (kind : StatsKind)
    (access : Acc) (bytes : List (Option Byte)) : Prop :=
  X.get i = some ⟨statsPc stage kind, .rd access bytes⟩

/-- A statistics read belongs to one of the four correction warps. -/
theorem StatisticsRead.warp {i : EvId} {stage : Fin 2} {kind : StatsKind} {a : Acc}
    {bytes : List (Option Byte)} (he : StatisticsRead X i stage kind a bytes) :
    8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 :=
  statisticsReadWarp hp hX stage kind he

/-- Every actual scalar statistics load reads exactly its own row's word. -/
theorem StatisticsRead.footprint {i : EvId} {stage : Fin 2} {kind : StatsKind} {a : Acc}
    {bytes : List (Option Byte)} (he : StatisticsRead X i stage kind a bytes) :
    a = {loc := statsLoc l i.1 stage kind, size := 4} := by
  obtain ⟨g,j⟩ := i
  obtain ⟨s,o,hPc,hSub,hReg,hEvent⟩ := statsReadRegisterExact hp hX stage kind he
  simpa [hSub, Loc.at] using statsReadAtRegister hp stage kind hPc hReg hEvent

/-- Statistics loads use allocated data above the shared-memory object area. -/
theorem statisticsReadRange {i : EvId} {stage : Fin 2} {kind : StatsKind} {a : Acc}
    {bytes : List (Option Byte)} (he : StatisticsRead X i stage kind a bytes) :
    l.sharedBase + 368 ≤ a.loc.addr ∧ a.size = 4 ∧
      a.loc.addr + a.size ≤ l.sharedBase + 3072 := by
  obtain ⟨g, j⟩ := i
  obtain ⟨t, o, hPc, hSub, hReg, hEvent⟩ := statsReadRegister hp hX stage kind he
  have hAccess := statsReadAtRegister hp stage kind hPc hReg hEvent
  rw [hAccess]
  change l.sharedBase + 368 ≤ l.sharedBase + 4 * rowOf l g + statsOff stage kind + 4 * t.sub ∧
    (4 : Nat) = 4 ∧
    l.sharedBase + 4 * rowOf l g + statsOff stage kind + 4 * t.sub + 4 ≤ l.sharedBase + 3072
  obtain ⟨hLower, hUpper⟩ : 368 ≤ statsOff stage kind ∧ statsOff stage kind ≤ 1904 := by
    cases kind <;> fin_cases stage <;> decide
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  exact ⟨by omega, rfl, by omega⟩

theorem statisticsReadLower {i : EvId} {stage : Fin 2} {kind : StatsKind} {a : Acc}
    {bytes : List (Option Byte)} (he : StatisticsRead X i stage kind a bytes) :
    l.sharedBase + 368 ≤ a.loc.addr ∧ a.size = 4 :=
  let h := statisticsReadRange hp hX he
  ⟨h.1, h.2.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
