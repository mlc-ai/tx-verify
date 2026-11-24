-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseIssuer
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStaging
import Kernels.TmlFa4Fwd.Proof.CorrectionFinalLayout
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Lemmas.Order.DependencyWitness
import Lemmas.Flow.Recip

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame PTX.Assumption Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

private def lseWindow (stage : Fin 2) : Nat := if stage = 0 then 9061 else 9074

private def terminalRegs : List Nat := [1627]

private def VectorCursor (s : TState) : Prop :=
  ∃ m, kernel.code[s.pc]? = some ⟨none, .mem m⟩ ∧ scoreStoreOp m = true

private def ValidSub (s : TState) : Prop := PartialLoad s ∨ VectorCursor s

private def validSubOp (i : Instr) : Bool :=
  stagingEvent i.op ||
    match i.op with
    | .mem m => i.guard.isNone && scoreStoreOp m
    | .fence .. => true
    | _ => false

private theorem vectorNotLocal {m : MemAccess} (h : scoreStoreOp m = true) :
    (Op.mem m).isLocal = false := by
  simp only [scoreStoreOp, Bool.and_eq_true, beq_iff_eq] at h
  simp [Op.isLocal, h.1.1.1.1.1]

private theorem validSubLocal {s : TState} {i : Instr} (hc : kernel.code[s.pc]? = some i)
    (hl : i.op.isLocal = true) (hs : ValidSub s) : s.sub = 0 := by
  rcases hs with (hz | ⟨ds, addr, sh, ht, _⟩) | ⟨m, ht, hm⟩
  · exact hz
  · rw [hc] at ht
    obtain rfl := Option.some.inj ht
    cases hl
  · rw [hc] at ht
    obtain rfl := Option.some.inj ht
    rw [vectorNotLocal hm] at hl
    cases hl

private theorem validSubEvent {l : Launch} {g : Nat} {s u : TState} {e : Event} {i : Instr}
    (hc : kernel.code[s.pc]? = some i) (hl : 7955 ≤ s.pc) (hi : validSubOp i = true)
    (hs : ValidSub s) (hf : Fires s.pc (eventTmpl Assumptions.all l g s i.op) e (some u)) :
    ValidSub u := by
  simp only [validSubOp, Bool.or_eq_true] at hi
  rcases hi with h | h
  · apply Or.inl
    apply partialLoadTail hc hl h _ hf
    rcases hs with hOld | ⟨a, ha, hStore⟩
    · exact hOld
    · rw [hc] at ha
      obtain rfl := Option.some.inj ha
      simp only [scoreStoreOp, Bool.and_eq_true, beq_iff_eq] at hStore
      simp [stagingEvent, hStore.1.1.1.1.1] at h
  · cases ho : i.op <;> simp only [ho, Bool.false_eq_true] at h
    case mem a =>
      have h' : i.guard.isNone && scoreStoreOp a = true := h
      obtain ⟨hGuard, hStore⟩ := Bool.and_eq_true_iff.mp h'
      have hStoreState := correctionStoreState hStore (ho ▸ hf)
      rw [hStoreState]
      by_cases hMore : s.sub + 1 < a.srcs.length
      · right
        unfold afterStore
        rw [ite_eq_left hMore]
        exact ⟨a, by rw [hc, ← ho, ← Option.isNone_iff_eq_none.mp hGuard], hStore⟩
      · left
        left
        simp [afterStore, hMore]
    case fence f =>
      have hz : s.sub = 0 := by
        rcases hs with (hz | ⟨ds, addr, sh, ht, _⟩) | ⟨a, ht, _⟩
        · exact hz
        all_goals rw [hc] at ht
        all_goals have hOp := congrArg Instr.op (Option.some.inj ht)
        all_goals rw [ho] at hOp
        all_goals cases hOp
      obtain rfl := fires_next (op := .fence f) trivial (ho ▸ hf)
      exact .inl (.inl hz)

private def preStatsCode (stage : Fin 2) (i : Instr) : Bool :=
  (i.op.isLocal || (correctionReturningOp i.op && validSubOp i)) &&
    terminalRegs.all (fun r => !(writesRegs i.op).contains r &&
      !(scoreEventWrites i.op).contains r) &&
    (match i.op with
      | .mem a => a.kind != .load || a.regs.length ≤ 1
      | _ => true) &&
    match i.op with
    | .bra pc _ => 7955 ≤ pc && pc ≤ statsBarrierPc stage false
    | .brx .. => false
    | _ => true

private theorem preStatsCodeAt (stage : Fin 2) {pc : Nat} {i : Instr}
    (hl : 7955 ≤ pc) (hh : pc < statsBarrierPc stage false)
    (hc : kernel.code[pc]? = some i) : preStatsCode stage i = true := by
  have hAll : ((kernel.code.drop 7955).take (statsBarrierPc stage false - 7955)).all
      (preStatsCode stage) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - 7955)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl, hc]

private theorem preStatsStep (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hl : 7955 ≤ s.pc) (hh : s.pc < statsBarrierPc stage false)
    (hSub : s.sub ≤ 3) (hValid : ValidSub s) (hAcc : s.acc = []) (hAddr : s.regs 1627 = some
      (b32 (l.sharedBase + 4 * rowOf l g)))
    (he : WStep kernel Assumptions.all l g s e u) :
    (7955 ≤ u.pc ∧ u.pc ≤ statsBarrierPc stage false) ∧ u.sub ≤ 3 ∧ ValidSub u ∧ u.acc = [] ∧
      u.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)) := by
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    have hCode := preStatsCodeAt stage hl hh hc
    simp only [preStatsCode, Bool.and_eq_true] at hCode
    rcases hTau with ⟨rfl, _⟩ | ⟨_, hLoc, hLocal⟩
    · exact ⟨⟨by change 7955 ≤ s.pc + 1; omega,
        by change s.pc + 1 ≤ statsBarrierPc stage false; omega⟩,
        Nat.zero_le _, .inl (.inl rfl), rfl, hAddr⟩
    have hReg : 1627 ∉ writesRegs i.op := by
      have h := List.all_eq_true.mp hCode.1.1.2 1627 (by decide)
      simpa using (Bool.and_eq_true_iff.mp h).1
    refine ⟨?_, hLocal.sub ▸ hSub, .inl (.inl (hLocal.sub.trans (validSubLocal hc hLoc hValid))),
      hLocal.acc.trans hAcc, (hLocal.regs 1627 hReg).trans hAddr⟩
    have hp := hLocal.pc
    cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
    case bra d uni =>
      have hDst : 7955 ≤ d ∧ d ≤ statsBarrierPc stage false := by simpa [hop] using hCode.2
      exact hp.symm ▸ hDst
    case brx => simp [hop] at hCode
    all_goals exact ⟨by omega, by omega⟩
  · obtain ⟨i, hc, hNonlocal, hf⟩ := estep_event_source he
    have hCode := preStatsCodeAt stage hl hh hc
    simp only [preStatsCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hCode
    have hPlan := hCode.1.1.1.1
    have hScalar : match i.op with | .mem a => a.kind = .load → a.regs.length ≤ 1 | _ => True := by
      cases hop : i.op <;> simp_all
      case mem a => exact hCode.2.elim (fun h hn => (h hn).elim) (fun h _ => h)
    have hReg : 1627 ∉ scoreEventWrites i.op := by
      have h := List.all_eq_true.mp hCode.1.1.2 1627 (by decide)
      simpa using (Bool.and_eq_true_iff.mp h).2
    obtain ⟨hP, hKeep⟩ := correctionEventProgress hc hPlan hSub hReg he
    refine ⟨?_, hP.sub, validSubEvent hc hl hCode.1.1.1.2 hValid hf,
      correctionEventAccumulator hc hPlan hScalar hAcc he, hKeep.trans hAddr⟩
    rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private abbrev KnownScale (p : Params) (s : TState) : Prop :=
  8448 ≤ s.pc → s.regs 7134 = some (b32 p.scaleLog2Bits)

private def scaleFrameCode (pc : Nat) (i : Instr) : Bool :=
  if pc = 8447 then true else
    !(writesRegs i.op).contains 7134 && !(scoreEventWrites i.op).contains 7134 &&
      match i.op with
      | .bra dst _ => decide (8448 ≤ dst → 8448 ≤ pc)
      | .brx .. => false
      | _ => true

private theorem scaleFrameAtCode {pc : Nat} {i : Instr}
    (hl : 7955 ≤ pc) (hh : pc < 8761) (hc : kernel.code[pc]? = some i) :
    scaleFrameCode pc i = true := by
  let slice := ((kernel.code.drop 7955).take (8761 - 7955)).zipIdx 7955
  have h := (show slice.all (fun (ins, pc) => scaleFrameCode pc ins) = true from by
    set_option maxRecDepth 100000 in kernel_rfl)
  have hAt : slice[pc - 7955]? = some (i, pc) := by
    dsimp only [slice]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hl, hc]
    rfl
  exact List.all_eq_true.mp h _ (List.mem_of_getElem? hAt)

section
variable {p : Params} {l : Launch} {m : Mem0}

private theorem knownScaleStep (hp : Pre p l m) (stage : Fin 2) {g : Nat} {s u : TState}
    {e : Option Event} (hl : 7955 ≤ s.pc) (hh : s.pc < statsBarrierPc stage false)
    (hSub : s.sub ≤ 3) (hValid : ValidSub s) (hAcc : s.acc = []) (hs : KnownScale p s)
    (he : WStep kernel Assumptions.all l g s e u) : KnownScale p u := by
  have hHi : s.pc < 8761 := hh.trans_le (by fin_cases stage <;> decide)
  intro hPast
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hFault, hLocal⟩ := correctionTauFrame hOff ht
    by_cases hScale : s.pc = 8447
    · obtain ⟨ins, hCode, hGuard, _⟩ := finalizeScaleInstruction
      rw [hScale, hCode] at hc
      obtain rfl := Option.some.inj hc
      rcases hLocal with ⟨_, hSkip⟩ | ⟨_, hLoc, _⟩
      · rw [hGuard] at hSkip
        cases hSkip
      · have hZero := validSubLocal (hScale.symm ▸ hCode) hLoc hValid
        obtain ⟨t, hTac, hVal⟩ := finalizeScaleStep hp (l := l) (g := g)
          (F := []) ⟨hScale, hZero, hAcc, hFault, trivial⟩ (by simp)
        obtain rfl := Out.tau.inj (ht.symm.trans hTac)
        exact hVal.2.2.2.2.1
    have hCode := scaleFrameAtCode hl hHi hc
    simp only [scaleFrameCode, hScale, ↓reduceIte, Bool.and_eq_true] at hCode
    rcases hLocal with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact hs (by change 8448 ≤ s.pc + 1 at hPast; omega)
    have hKeep : 7134 ∉ writesRegs i.op := by simpa using hCode.1.1
    have hSrc : 8448 ≤ s.pc := by
      have hPc := hF.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        have hDest : dst < 8448 ∨ 8448 ≤ s.pc := by simpa [ho] using hCode.2
        omega
      case brx => simp [ho] at hCode
      all_goals omega
    exact (hF.regs _ hKeep).trans (hs hSrc)
  · obtain ⟨i, hc, hNonlocal, _⟩ := estep_event_source he
    have hScale : s.pc ≠ 8447 := by
      intro heq
      obtain ⟨ins, hCode, _, hLoc⟩ := finalizeScaleInstruction
      rw [heq, hCode] at hc
      obtain rfl := Option.some.inj hc
      rw [hLoc] at hNonlocal
      cases hNonlocal
    have hCode := scaleFrameAtCode hl hHi hc
    simp only [scaleFrameCode, hScale, ↓reduceIte, Bool.and_eq_true] at hCode
    have hPlan := preStatsCodeAt stage hl hh hc
    simp only [preStatsCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hPlan
    have hKeep : 7134 ∉ scoreEventWrites i.op := by simpa using hCode.1.2
    obtain ⟨hP, hRegs⟩ := correctionEventProgress hc hPlan.1.1.1.1 hSub hKeep he
    exact hRegs.trans (hs (by rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega))

private theorem cutTerminalBarrier (hp : Pre p l m) (stage : Fin 2) {g : Nat} {s u : TState}
    {es : List Event} (hr : TraceReach kernel Assumptions.all l g s es u) (hl : 7955 ≤ s.pc)
    (hh : s.pc ≤ statsBarrierPc stage false) (hSub : s.sub ≤ 3) (hValid : ValidSub s)
    (hAcc : s.acc = []) (hAddr : s.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hScale : KnownScale p s) (hu : statsBarrierPc stage false < u.pc) :
    ∃ t before rest, t.pc = statsBarrierPc stage false ∧ ValidSub t ∧ t.acc = [] ∧
      t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)) ∧ KnownScale p t ∧
      es = before ++ rest ∧ TraceReach kernel Assumptions.all l g s before t ∧
      TraceReach kernel Assumptions.all l g t rest u := by
  induction hr with
  | refl => omega
  | @tau s v w es ht hr ih =>
    by_cases hs : s.pc = statsBarrierPc stage false
    · exact ⟨s, [], es, hs, hValid, hAcc, hAddr, hScale, rfl, .refl _, .tau ht hr⟩
    obtain ⟨hRange, hSub, hV, hAcc, hAddr⟩ :=
      preStatsStep stage hl (by omega) hSub hValid hAcc hAddr (.inl ⟨rfl, ht⟩)
    have hS := knownScaleStep hp stage hl (by omega) ‹s.sub ≤ 3› hValid ‹s.acc = []› hScale
      (.inl ⟨rfl, ht⟩)
    obtain ⟨t, before, rest, hAt, htValid, htAcc, htAddr, htScale, hEq, hPrefix, hRest⟩ :=
      ih hRange.1 hRange.2 hSub hV hAcc hAddr hS hu
    exact ⟨t, before, rest, hAt, htValid, htAcc, htAddr, htScale, hEq, .tau ht hPrefix, hRest⟩
  | @event s v w es e he hr ih =>
    by_cases hs : s.pc = statsBarrierPc stage false
    · exact ⟨s, [], e :: es, hs, hValid, hAcc, hAddr, hScale, rfl, .refl _, .event he hr⟩
    obtain ⟨hRange, hSub, hV, hAcc, hAddr⟩ :=
      preStatsStep stage hl (by omega) hSub hValid hAcc hAddr (.inr ⟨e, rfl, he⟩)
    have hS := knownScaleStep hp stage hl (by omega) ‹s.sub ≤ 3› hValid ‹s.acc = []› hScale
      (.inr ⟨e, rfl, he⟩)
    obtain ⟨t, before, rest, ht, hV, hAcc, hAddr, hScale, hEq, hPrefix, hTail⟩ :=
      ih hRange.1 hRange.2 hSub hV hAcc hAddr hS hu
    exact ⟨t, e :: before, rest, ht, hV, hAcc, hAddr, hScale, congrArg (e :: ·) hEq,
      .event he hPrefix, hTail⟩

private def barrierCode (stage : Fin 2) : Instr :=
  ⟨none, .barSyncN (.reg (statsBarrierReg stage)) (.imm 64) true⟩

private theorem terminalBarrierDecoded (stage : Fin 2) :
    kernel.code[statsBarrierPc stage false]? = some (barrierCode stage) := by
  fin_cases stage
  · exact Flow.code_8465
  · exact Flow.code_8761

private def terminalReadCode (stage : Fin 2) (kind : StatsKind) : Instr :=
  { guard := none
    op := .mem {
      kind := .load, space := some (.shared .cta), sem := .weak, elem := .int .b 32
      addr := ⟨.reg 1627 32, statsOff stage kind⟩
      dsts := [some (statsReg stage kind)] } }

private theorem terminalReadDecoded (stage : Fin 2) {kind : StatsKind}
    (hk : kind = .sum ∨ kind = .maximum) :
    kernel.code[statsPc stage kind]? = some (terminalReadCode stage kind) := by
  rcases hk with rfl | rfl
  · fin_cases stage
    · exact Flow.code_8466
    · exact Flow.code_8762
  · fin_cases stage
    · exact Flow.code_8467
    · exact Flow.code_8763

private theorem reachMandatoryEvent {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    {i : Instr} (hc : kernel.code[s.pc]? = some i) (hguard : i.guard = none)
    (hl : i.op.isLocal = false) (hPc : s.pc < u.pc)
    (hr : TraceReach kernel Assumptions.all l g s es u) :
    ∃ e t rest, es = e :: rest ∧ EStep kernel Assumptions.all l g s e (some t) ∧
      TraceReach kernel Assumptions.all l g t rest u := by
  cases hr with
  | refl => omega
  | tau h _ =>
    unfold Tau at h
    cases hf : s.fault
    · rw [out, hf, hc] at h
      simp [hguard, guardHolds, hl, pure, Except.pure] at h
    · simp [out, hf] at h
  | event he hr => exact ⟨_, _, _, rfl, he, hr⟩

private theorem terminalBarrierContinues {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (hpc : s.pc = statsBarrierPc stage false)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    u = next s := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rw [hpc, terminalBarrierDecoded] at hc
  obtain rfl := Option.some.inj hc
  apply callbackFrame_fires (P := (· = next s)) _ hf
  simp only [barrierCode, eventTmpl, barTmpl]
  repeat' split
  all_goals first | rfl | trivial

private theorem terminalReadStep {g : Nat} {s u : TState} {e : Event} (hp : Pre p l m)
    (stage : Fin 2) {kind : StatsKind} (hk : kind = .sum ∨ kind = .maximum)
    (hpc : s.pc = statsPc stage kind) (hs : s.sub = 0)
    (hBase : s.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ bs, e = ⟨statsPc stage kind, .rd {loc := statsLoc l g stage kind, size := 4} bs⟩ ∧
      u = afterLoad s [statsReg stage kind] bs := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rw [hpc, terminalReadDecoded stage hk] at hc
  obtain rfl := Option.some.inj hc
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hOff : statsOff stage kind ≤ 1904 ∧ statsOff stage kind % 4 = 0 := by
    rcases hk with rfl | rfl <;> fin_cases stage <;> decide
  have hAddr : l.sharedBase + 4 * rowOf l g + statsOff stage kind < 2 ^ 32 := by
    have := hp.shared.2.1
    omega
  have hAlign : (l.sharedBase + 4 * rowOf l g + statsOff stage kind) % 4 = 0 := by
    have := hp.shared.1
    omega
  have hEff : effAddr l g s .shared 1627 (↑(statsOff stage kind)) =
      .ok (statsLoc l g stage kind) := effAddr_b32_off hBase hAddr
  change Fires s.pc (loadTmpl Assumptions.all l g s .shared false 32
    [statsReg stage kind] 1627 (↑(statsOff stage kind))) e (some u) at hf
  have ht : elemAcc (statsLoc l g stage kind) 4 1 s.sub =
      .ok {loc := statsLoc l g stage kind, size := 4} := by
    simp [elemAcc, hs, statsLoc, hAlign, pure, Except.pure, Loc.at]
  simp only [loadTmpl, hEff, List.length_singleton, Nat.reduceDiv, bind, Except.bind, ht] at hf
  obtain ⟨bs, _, he, hu⟩ := hf
  rw [hpc] at he
  exact ⟨bs, he, Option.some.inj hu⟩

private theorem terminalBarrierSub {s : TState} (stage : Fin 2)
    (hpc : s.pc = statsBarrierPc stage false) (h : ValidSub s) : s.sub = 0 := by
  have hc := hpc.symm ▸ terminalBarrierDecoded stage
  rcases h with (h | ⟨ds, addr, shape, he, _⟩) | ⟨a, he, _⟩
  · exact h
  all_goals rw [hc] at he
  all_goals cases he

private theorem terminalBarrierEvent (hp : Pre p l m) {g : Nat} {s u : TState} {e : Event}
    (stage : Fin 2) (hpc : s.pc = statsBarrierPc stage false)
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ id, e = ⟨statsBarrierPc stage false, .bar id (some 64) .sync⟩ := by
  obtain ⟨i, hc, _, hf⟩ := estep_event_source he
  rw [hpc, terminalBarrierDecoded] at hc
  obtain rfl := Option.some.inj hc
  have hn : readBits l g s 32 (.imm 64) = .ok (BitVec.ofNat 64 64) := rfl
  change Fires s.pc (barTmpl l g s (.reg (statsBarrierReg stage)) (some (.imm 64)) .sync)
    e (some u) at hf
  cases hId : readBits l g s 32 (.reg (statsBarrierReg stage)) with
  | error f =>
    simp only [barTmpl, hId] at hf
    cases hf.2
  | ok id =>
    by_cases h : 16 ≤ id.toNat
    · simp only [barTmpl, hId, h, ↓reduceIte] at hf
      cases hf.2
    · have hKind : e = ⟨s.pc, .bar id.toNat (some 64) .sync⟩ := by
        have hWord : BitVec.ofNat 64 id.toNat = id := BitVec.ofNat_toNat 64 id
        exact fires_barTmpl_at (hWord.symm ▸ hId) hn (by omega) (by decide)
          (by decide) (by decide) (by rw [hp.block]; decide) hf
      exact ⟨id.toNat, hpc ▸ hKind⟩

private theorem reachFromFault {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (hf : s.fault.isSome) (hr : TraceReach kernel Assumptions.all l g s es u) :
    u.pc = s.pc := by
  obtain ⟨fault, hFault⟩ := Option.isSome_iff_exists.mp hf
  cases hr with
  | refl => rfl
  | tau h _ => simp [Tau, out, hFault] at h
  | event he _ =>
    obtain ⟨m, ho, hf⟩ := he
    rw [out, hFault] at ho
    obtain rfl := Out.ev.inj ho
    cases hf.2

private theorem afterStatsRead {l : Launch} {g : Nat} {s u : TState} {es : List Event}
    (stage : Fin 2) (kind : StatsKind) (bs : List (Option Byte))
    (hAcc : s.acc = []) (hPc : s.pc < u.pc)
    (hReach : TraceReach kernel Assumptions.all l g (afterLoad s [statsReg stage kind] bs) es u) :
    ∃ value, rebuild 3 bs = .ok value ∧
      afterLoad s [statsReg stage kind] bs = { next (setReg s (statsReg stage kind) value)
        with sub := 0, acc := [] } := by
  cases h : rebuild 3 bs with
  | error f =>
    have he : (afterLoad s [statsReg stage kind] bs).pc = s.pc := by simp [afterLoad, h]
    have hf : (afterLoad s [statsReg stage kind] bs).fault.isSome := by simp [afterLoad, h]
    exact (Nat.ne_of_lt hPc (he.symm.trans (reachFromFault hf hReach).symm)).elim
  | ok v =>
    refine ⟨v, rfl, ?_⟩
    rw [afterLoad_last h (by simp)]
    simp [hAcc, setRegs, next, setReg]

private theorem terminalStatsInPath (hp : Pre p l m) {g : Nat} {s u : TState} {es : List Event}
    (stage : Fin 2) (hStart : s.pc = 7955) (hSub : s.sub = 0) (hAcc : s.acc = [])
    (hAddr : s.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hu : statsPc stage .maximum < u.pc) (hr : TraceReach kernel Assumptions.all l g s es u) :
    ∃ before id sumBytes maxBytes rest t,
      es = before ++
        ⟨statsBarrierPc stage false, .bar id (some 64) .sync⟩ ::
        ⟨statsPc stage .sum, .rd {loc := statsLoc l g stage .sum, size := 4} sumBytes⟩ ::
        ⟨statsPc stage .maximum, .rd {loc := statsLoc l g stage .maximum, size := 4} maxBytes⟩ ::
        rest ∧ t.pc = statsPc stage .maximum + 1 ∧ t.sub = 0 ∧
      (∀ value, rebuild 3 sumBytes = .ok value → t.regs (statsReg stage .sum) = some value) ∧
      (∀ value, rebuild 3 maxBytes = .ok value → t.regs (statsReg stage .maximum) = some value) ∧
      t.regs 7134 = some (b32 p.scaleLog2Bits) ∧
      TraceReach kernel Assumptions.all l g s
        (before ++ [⟨statsBarrierPc stage false, .bar id (some 64) .sync⟩,
          ⟨statsPc stage .sum, .rd {loc := statsLoc l g stage .sum, size := 4} sumBytes⟩,
          ⟨statsPc stage .maximum, .rd {loc := statsLoc l g stage .maximum, size := 4} maxBytes⟩])
        t ∧ TraceReach kernel Assumptions.all l g t rest u := by
  have hBS : statsBarrierPc stage false + 1 = statsPc stage .sum := by fin_cases stage <;> rfl
  have hSM : statsPc stage .sum + 1 = statsPc stage .maximum := by fin_cases stage <;> rfl
  have hStart' : s.pc ≤ statsBarrierPc stage false := by rw [hStart]; fin_cases stage <;> decide
  obtain ⟨v, before, rest, hv, hs, hAcc, hAddr', hvScale, hEq, hLead, hr⟩ :=
    cutTerminalBarrier hp stage hr hStart.ge hStart' (by rw [hSub]; decide)
      (.inl (.inl hSub)) hAcc hAddr (fun h => by omega) (by omega)
  have hvSub := terminalBarrierSub stage hv hs
  obtain ⟨bar, w, rest', hRest, hBar, hW⟩ :=
    reachMandatoryEvent (hv.symm ▸ terminalBarrierDecoded stage) rfl rfl (by omega) hr
  obtain ⟨id, rfl⟩ := terminalBarrierEvent hp stage hv hBar
  obtain rfl := terminalBarrierContinues stage hv hBar
  have hw : (next v).pc = statsPc stage .sum := by change v.pc + 1 = _; omega
  obtain ⟨readS, x, rest'', hRest', hrS, hX⟩ :=
    reachMandatoryEvent (hw.symm ▸ terminalReadDecoded stage (.inl rfl)) rfl rfl (by omega) hW
  obtain ⟨sumBytes, rfl, rfl⟩ :=
    terminalReadStep hp stage (.inl rfl) hw hvSub hAddr' hrS
  obtain ⟨sum, hSum, hLoaded⟩ :=
    afterStatsRead (s := next v) stage .sum sumBytes hAcc (by omega) hX
  rw [hLoaded] at hX
  let tx := { next (setReg (next v) (statsReg stage .sum) sum) with sub := 0, acc := [] }
  change TraceReach _ _ _ _ tx rest'' u at hX
  have hx : tx.pc = statsPc stage .maximum := by
    change (next v).pc + 1 = _
    omega
  have hxAddr : tx.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)) := by
    have hNe : 1627 ≠ statsReg stage .sum := by fin_cases stage <;> decide
    simpa [tx, next, setReg, Function.update_of_ne hNe] using hAddr'
  obtain ⟨readM, y, tail, hRest'', hrM, hY⟩ :=
    reachMandatoryEvent (hx.symm ▸ terminalReadDecoded stage (.inr rfl)) rfl rfl (by omega) hX
  obtain ⟨maxBytes, rfl, rfl⟩ :=
    terminalReadStep hp stage (.inr rfl) hx rfl hxAddr hrM
  obtain ⟨maximum, hMax, hLoadedMax⟩ :=
    afterStatsRead (s := tx) stage .maximum maxBytes rfl (by omega) hY
  rw [hLoadedMax] at hY
  refine ⟨before, id, sumBytes, maxBytes, tail, _, ?_, ?_, rfl, ?_, ?_, ?_, ?_, hY⟩
  · rw [hEq, hRest, hRest', hRest'']
  · exact congrArg (· + 1) hx
  · intro value he
    have hNE : statsReg stage .sum ≠ statsReg stage .maximum := by fin_cases stage <;> decide
    rw [hSum] at he
    obtain rfl := Except.ok.inj he
    simp [tx, setReg, next, Function.update_of_ne hNE]
  · intro value he
    rw [hMax] at he
    obtain rfl := Except.ok.inj he
    simp [setReg, next]
  · have hS : 7134 ≠ statsReg stage .sum := by fin_cases stage <;> decide
    have hM : 7134 ≠ statsReg stage .maximum := by fin_cases stage <;> decide
    have hScale := hvScale (by rw [hv]; fin_cases stage <;> decide)
    simpa [tx, next, setReg, Function.update_of_ne hS, Function.update_of_ne hM] using hScale
  · rw [hLoaded] at hrS
    rw [hLoadedMax] at hrM
    exact hLead.append (.event hBar (.event hrS (.event hrM (.refl _))))
end

private def tailStatsCode (stage : Fin 2) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
    [statsReg stage .sum, statsReg stage .maximum, 7134].all (fun r =>
      !(writesRegs i.op).contains r && !(scoreEventWrites i.op).contains r) &&
    match i.op with
    | .bra dst _ => statsPc stage .maximum < dst && dst ≤ lseWindow stage
    | .brx .. => false
    | _ => true

private theorem tailStatsCodeAt (stage : Fin 2) {pc : Nat} {i : Instr}
    (hl : statsPc stage .maximum < pc) (hh : pc < lseWindow stage)
    (hc : kernel.code[pc]? = some i) : tailStatsCode stage i = true := by
  let lo := statsPc stage .maximum + 1
  have hAll : ((kernel.code.drop lo).take (lseWindow stage - lo)).all
      (tailStatsCode stage) = true := by
    fin_cases stage <;> set_option maxRecDepth 100000 in kernel_rfl
  have hLo : lo ≤ pc := hl
  apply List.all_eq_true.mp hAll i
  apply List.mem_of_getElem? (i := pc - lo)
  rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hLo, hc]

private theorem tailStatsStep (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {e : Option Event} (hl : statsPc stage .maximum < s.pc) (hh : s.pc < lseWindow stage)
    (hSub : s.sub ≤ 3) (he : WStep kernel Assumptions.all l g s e u) :
    (statsPc stage .maximum < u.pc ∧ u.pc ≤ lseWindow stage) ∧
      u.sub ≤ 3 ∧
      ∀ r ∈ [statsReg stage .sum, statsReg stage .maximum, 7134], u.regs r = s.regs r := by
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      have hlo : 8467 ≤ statsPc stage .maximum := by fin_cases stage <;> decide
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, _, hTau⟩ := correctionTauFrame hOff ht
    have hCode := tailStatsCodeAt stage hl hh hc
    simp only [tailStatsCode, Bool.and_eq_true] at hCode
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hLocal⟩
    · exact ⟨⟨by change statsPc stage .maximum < s.pc + 1; omega,
        by change s.pc + 1 ≤ lseWindow stage; omega⟩,
        Nat.zero_le _, fun _ _ => rfl⟩
    refine ⟨?_, hLocal.sub ▸ hSub, fun r hr => hLocal.regs r (by
      simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hCode.1.2 r hr)).1)⟩
    have hp := hLocal.pc
    cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hp
    case bra dst uni =>
      have hDst : statsPc stage .maximum < dst ∧ dst ≤ lseWindow stage := by
        simpa [hop] using hCode.2
      exact hp.symm ▸ hDst
    case brx => simp [hop] at hCode
    all_goals exact ⟨by omega, by omega⟩
  · obtain ⟨i, hc, hNonlocal, _⟩ := estep_event_source he
    have hCode := tailStatsCodeAt stage hl hh hc
    simp only [tailStatsCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hCode
    have hKeep (r : Nat) (hr : r ∈ [statsReg stage .sum, statsReg stage .maximum, 7134]) :=
      correctionEventProgress hc hCode.1.1 hSub (r := r) (by
        simpa using (Bool.and_eq_true_iff.mp (List.all_eq_true.mp hCode.1.2 r hr)).2) he
    have hP := (hKeep (statsReg stage .sum) List.mem_cons_self).1
    refine ⟨?_, hP.sub, fun r hr => (hKeep r hr).2⟩
    rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-- The first LSE uses the decoded nonzero comparison of its own terminal sum. -/
def FirstLseSelector (s : TState) (sum : List (Option Byte)) : Prop :=
  ∀ x : ℝ, rebuild 3 sum = .ok (fl x) → s.regs 739 = some (.pred (decide (x ≠ 0)))

private abbrev KnownSelector (stage : Fin 2) (s : TState) (sum : List (Option Byte)) : Prop :=
  stage = 0 → 8470 ≤ s.pc → FirstLseSelector s sum

private def selectorFrameCode (pc : Nat) (i : Instr) : Bool :=
  if pc = 8469 then true else
    !(writesRegs i.op).contains 739 && !(scoreEventWrites i.op).contains 739 &&
      match i.op with
      | .bra dst _ => decide (8470 ≤ dst → 8470 ≤ pc)
      | .brx .. => false
      | _ => true

private theorem selectorFrameAtCode {pc : Nat} {i : Instr}
    (hl : 8468 ≤ pc) (hh : pc < 9061) (hc : kernel.code[pc]? = some i) :
    selectorFrameCode pc i = true := by
  let slice := ((kernel.code.drop 8468).take (9061 - 8468)).zipIdx 8468
  have h := (show slice.all (fun (ins, pc) => selectorFrameCode pc ins) = true from by
    set_option maxRecDepth 100000 in kernel_rfl)
  have hAt : slice[pc - 8468]? = some (i, pc) := by
    dsimp only [slice]
    rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
      Nat.add_sub_of_le hl, hc]
    rfl
  exact List.all_eq_true.mp h _ (List.mem_of_getElem? hAt)

private theorem firstSelectorWritten {l : Launch} {g : Nat} {s u : TState} {x : ℝ}
    (hPc : s.pc = 8469) (hFault : s.fault = none)
    (hSum : s.regs 6512 = some (fl x)) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs 739 = some (.pred (decide (x ≠ 0))) := by
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [hPc]; decide
  have hIdeal : IdealAt Assumptions.numeric (.setp .f32) l g s :=
    idealAt_head (by decide) (Assumptions.numeric_segSites.pc hOff).tail
  have hAt := fsetp_imm (K := kernel) (A := Assumptions.numeric) (L := l) (g := g)
    (hPc.symm ▸ Flow.code_8469) (Or.inl rfl) rfl hIdeal hFault hSum valFloat_zero
  have hTau := hAt.1 x rfl
  rw [erealCompare_ne_coe_zero] at hTau
  have hActual := tauStep_iff.mpr ht
  rw [Assumptions.tauStep_all_eq_numeric] at hActual
  have he := Option.some.inj (hActual.symm.trans (tauStep_iff.mpr hTau))
  rw [he]
  simp [next, setReg]

private theorem firstSelectorStep (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {sum : List (Option Byte)} {e : Option Event}
    (hl : statsPc stage .maximum < s.pc) (hh : s.pc < lseWindow stage) (hSub : s.sub ≤ 3)
    (hSum : ∀ value, rebuild 3 sum = .ok value → s.regs (statsReg stage .sum) = some value)
    (hSel : KnownSelector stage s sum) (he : WStep kernel Assumptions.all l g s e u) :
    KnownSelector stage u sum := by
  intro hStage hPast x hx
  subst stage
  change 8468 ≤ s.pc at hl
  change s.pc < 9061 at hh
  rcases he with ⟨_, ht⟩ | ⟨e, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hFault, hLocal⟩ := correctionTauFrame hOff ht
    by_cases hSet : s.pc = 8469
    · exact firstSelectorWritten hSet hFault (hSum _ hx) ht
    have hCode := selectorFrameAtCode hl hh hc
    simp only [selectorFrameCode, hSet, ↓reduceIte, Bool.and_eq_true] at hCode
    rcases hLocal with ⟨rfl, _⟩ | ⟨_, _, hF⟩
    · exact hSel rfl (by change 8470 ≤ s.pc + 1 at hPast; omega) x hx
    have hKeep : 739 ∉ writesRegs i.op := by simpa using hCode.1.1
    have hSrc : 8470 ≤ s.pc := by
      have hPc := hF.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
      case bra dst uni =>
        have hDst : dst < 8470 ∨ 8470 ≤ s.pc := by simpa [ho] using hCode.2
        omega
      case brx => simp [ho] at hCode
      all_goals omega
    exact (hF.regs _ hKeep).trans (hSel rfl hSrc x hx)
  · obtain ⟨i, hc, hNonlocal, _⟩ := estep_event_source he
    have hSet : s.pc ≠ 8469 := by
      intro heq
      rw [heq, Flow.code_8469] at hc
      obtain rfl := Option.some.inj hc
      cases hNonlocal
    have hCode := selectorFrameAtCode hl hh hc
    simp only [selectorFrameCode, hSet, ↓reduceIte, Bool.and_eq_true] at hCode
    have hPlan := tailStatsCodeAt 0 hl hh hc
    simp only [tailStatsCode, Bool.and_eq_true, hNonlocal, Bool.false_or] at hPlan
    have hKeep : 739 ∉ scoreEventWrites i.op := by simpa using hCode.1.2
    obtain ⟨hP, hRegs⟩ := correctionEventProgress hc hPlan.1.1 hSub hKeep he
    exact hRegs.trans (hSel rfl (by rcases hP.pc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega) x hx)

private theorem cutLseWindow (stage : Fin 2) {l : Launch} {g : Nat} {s u : TState}
    {es : List Event} (hr : TraceReach kernel Assumptions.all l g s es u)
    (hStart : statsPc stage .maximum < s.pc) (hUpper : s.pc ≤ lseWindow stage)
    (hSub : s.sub ≤ 3) (hEnd : lseWindow stage < u.pc) {sum : List (Option Byte)}
    (hSum : ∀ value, rebuild 3 sum = .ok value → s.regs (statsReg stage .sum) = some value)
    (hSel : KnownSelector stage s sum) :
    ∃ t before after, t.pc = lseWindow stage ∧ es = before ++ after ∧
      TraceReach kernel Assumptions.all l g s before t ∧
      TraceReach kernel Assumptions.all l g t after u ∧ KnownSelector stage t sum ∧
      ∀ r ∈ [statsReg stage .sum, statsReg stage .maximum, 7134], t.regs r = s.regs r := by
  induction hr with
  | refl => omega
  | @tau s v u es ht hr ih =>
    by_cases hAt : s.pc = lseWindow stage
    · exact ⟨s, [], es, hAt, rfl, .refl _, .tau ht hr, hSel, fun _ _ => rfl⟩
    obtain ⟨hRange, hV, hKeep⟩ := tailStatsStep stage hStart (by omega) hSub (.inl ⟨rfl, ht⟩)
    have hv := firstSelectorStep stage hStart (by omega) hSub hSum hSel (.inl ⟨rfl, ht⟩)
    obtain ⟨t, before, after, hAt, hEq, hInto, hAfter, hSel, hFrame⟩ :=
      ih hRange.1 hRange.2 hV hEnd (fun v h => (hKeep _ List.mem_cons_self).trans (hSum v h)) hv
    exact ⟨t, before, after, hAt, hEq, .tau ht hInto, hAfter, hSel,
      fun r hr => (hFrame r hr).trans (hKeep r hr)⟩
  | @event s v u es e he hr ih =>
    by_cases hAt : s.pc = lseWindow stage
    · exact ⟨s, [], e :: es, hAt, rfl, .refl _, .event he hr, hSel, fun _ _ => rfl⟩
    obtain ⟨hRange, hV, hKeep⟩ :=
      tailStatsStep stage hStart (by omega) hSub (.inr ⟨e, rfl, he⟩)
    have hv := firstSelectorStep stage hStart (by omega) hSub hSum hSel (.inr ⟨e, rfl, he⟩)
    obtain ⟨t, before, after, hAt, hEq, hInto, hAfter, hSel, hFrame⟩ :=
      ih hRange.1 hRange.2 hV hEnd (fun v h => (hKeep _ List.mem_cons_self).trans (hSum v h)) hv
    exact ⟨t, e :: before, after, hAt, congrArg (e :: ·) hEq, .event he hInto, hAfter, hSel,
      fun r hr => (hFrame r hr).trans (hKeep r hr)⟩

/-- Values read by a correction lane at the numerical window preceding its LSE store. -/
@[no_expose] def LseWindowInputs (l : Launch) (X : Execution) (store : EvId)
    (stage : Fin 2) (first : Nat) (s : TState) (sum maximum : List (Option Byte)) : Prop :=
  ∃ before after outState event result,
    X.get store = some event ∧
    event.pc = lseGuardPc stage + 1 ∧ s.pc = lseWindow stage ∧
    ((X.tr store.1).drop first).take (store.2 - first) = before ++ after ∧
    TraceReach kernel Assumptions.all l store.1 s after outState ∧
    EStep kernel Assumptions.all l store.1 outState event result ∧
    (∀ v, rebuild 3 sum = .ok v → s.regs (statsReg stage .sum) = some v) ∧
    (∀ v, rebuild 3 maximum = .ok v → s.regs (statsReg stage .maximum) = some v)

/-- The reached state is at this stage's numerical window. -/
theorem LseWindowInputs.atWindow {l : Launch} {X : Execution} {store : EvId}
    {stage : Fin 2} {first : Nat} {s : TState} {sum maximum : List (Option Byte)}
    (hWindow : LseWindowInputs l X store stage first s sum maximum) :
    s.pc = (if stage = 0 then 9061 else 9074) := by
  obtain ⟨_, _, _, _, _, _, _, hPc, _⟩ := hWindow
  exact hPc

/-- The two observed byte words supply the sum and maximum registers used by this LSE. -/
theorem LseWindowInputs.loadedRegisters {l : Launch} {X : Execution} {store : EvId}
    {stage : Fin 2} {first : Nat} {s : TState} {sum maximum : List (Option Byte)}
    (hWindow : LseWindowInputs l X store stage first s sum maximum)
    (sumValue maxValue : Value)
    (hSum : rebuild 3 sum = .ok sumValue) (hMax : rebuild 3 maximum = .ok maxValue) :
    s.regs (statsReg stage .sum) = some sumValue ∧
      s.regs (statsReg stage .maximum) = some maxValue := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hS, hM⟩ := hWindow
  exact ⟨hS _ hSum, hM _ hMax⟩

/-- A correction lane issued its scalar LSE store for the given stage. -/
@[no_expose] def LseStored (X : Execution) (store : EvId) (stage : Fin 2) : Prop :=
  ∃ a bytes, X.get store = some ⟨lseGuardPc stage + 1, .wr a bytes⟩

/-- A recorded scalar write at the selected stage establishes an LSE store. -/
theorem LseStored.ofEvent {X : Execution} {store : EvId} {stage : Fin 2} {a : Acc}
    {bytes : List Byte} (he : X.get store = some ⟨lseGuardPc stage + 1, .wr a bytes⟩) :
    LseStored X store stage := ⟨a, bytes, he⟩

/-- The two actual consecutive shared reads following the terminal statistics rendezvous. -/
structure TerminalLseReads (l : Launch) (X : Execution) (store : EvId)
    (stage : Fin 2) (wait : Nat) (sum maximum : List (Option Byte)) : Prop where
  terminal : CorrectionWaits X (store.1, wait) .terminal stage
  resumes : Resumes kernel X (store.1, wait) store
  sumRead : X.Reads (store.1, wait + 1) {loc := statsLoc l store.1 stage .sum, size := 4} sum
  maxRead : X.Reads (store.1, wait + 2)
    {loc := statsLoc l store.1 stage .maximum, size := 4} maximum
  readsBeforeStore : wait + 2 < store.2
  released : ∃ key, CtaBarK l X (store.1, wait) key ∧ CtaBarDone l X (store.1 / l.block) key

/-- The actual LSE arithmetic window is reached from the selected correction checkpoint.
Its terminal reads supply the two statistic words, ABI scale and stage-zero selector. -/
theorem terminalInputsOfSelectedLse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch lane pos j : Nat} {stage : Fin 2} {initial : TState} {o : Option TState}
    (hb : batch < p.batch)
    (hInitial : At initial 7932 (correctionActiveTileFacts p l g batch lane))
    (hRun : Run kernel Assumptions.all l (warpLane l g lane) initial
      ((X.tr (warpLane l g lane)).drop pos) o)
    (hIndex : pos ≤ j) (hStore : LseStored X (warpLane l g lane, j) stage) :
    let thread := warpLane l g lane
    let store := (thread, j)
    ∃ wait sum maximum state reached rest,
      (X.tr thread).drop pos = reached ++ rest ∧
        TraceReach kernel Assumptions.all l thread initial reached state ∧
        TerminalLseReads l X store stage wait sum maximum ∧
        LseWindowInputs l X store stage pos state sum maximum ∧
        state.regs 7134 = some (b32 p.scaleLog2Bits) ∧
        (stage = 0 → FirstLseSelector state sum) := by
  let thread := warpLane l g lane
  obtain ⟨a, bytes, he⟩ := hStore
  let pc := lseGuardPc stage + 1
  let target : Event := ⟨pc, .wr a bytes⟩
  have hMore : (X.tr thread).drop pos ≠ [] := by
    have hLen := (List.getElem?_eq_some_iff.mp he).1
    change j < (X.tr thread).length at hLen
    intro hn
    have hEnd := List.drop_eq_nil_iff.mp hn
    omega
  obtain ⟨t, hLocal, ht⟩ := correctionInputRun hp hb hInitial
  have hRun := hRun.after_local_nonempty (run_rtg hLocal) hMore
  let k := j - pos
  let es := (X.tr thread).drop pos
  have hReadout : es[k]? = some target := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  have hk := (List.getElem?_eq_some_iff.mp hReadout).1
  obtain ⟨w, _, hReach, hW⟩ := hRun.before_event hReadout
  have hPc := estep_source_pc hW
  have hFinish : statsPc stage .maximum < w.pc := by
    rw [← hPc]
    change statsPc stage .maximum < pc
    fin_cases stage <;> decide
  have hBase : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l thread)) :=
    holds_lookup ht.2.2.2.2 (by rfl)
  obtain ⟨pre, id, sum, maximum, tail, u, hCut, hu, huSub, huSum, huMax, huScale, hPre, hTail⟩ :=
    terminalStatsInPath hp stage ht.1 ht.2.1 ht.2.2.1 hBase hFinish hReach
  let wait := pos + pre.length
  have hTake : (es.take k).length = k := List.length_take_of_le hk.le
  rw [hCut] at hTake
  simp only [List.length_append, List.length_cons] at hTake
  have hj : j < (X.tr thread).length := (List.getElem?_eq_some_iff.mp he).1
  have hBound : wait + 2 < j := by dsimp [k, wait] at hTake ⊢; omega
  have atIndex (n : Nat) (hn : n < 3) :
      (X.tr thread)[wait + n]? = (es.take k)[pre.length + n]? := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    rw [show wait + n = pos + (pre.length + n) by dsimp [wait]; omega]
  have hRawBar : X.get (thread, wait) =
      some ⟨statsBarrierPc stage false, .bar id (some 64) .sync⟩ := by
    have hi := atIndex 0 (by decide)
    rw [hCut] at hi
    change (X.tr thread)[wait]? = _
    simpa only [Nat.add_zero, List.getElem?_append_right le_rfl, Nat.sub_self,
      List.getElem?_cons_zero] using hi
  have hRawSum : X.get (thread, wait + 1) =
      some ⟨statsPc stage .sum, .rd {loc := statsLoc l thread stage .sum, size := 4} sum⟩ := by
    have hi := atIndex 1 (by decide)
    rw [hCut, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hi
    exact hi
  have hRawMax : X.get (thread, wait + 2) =
      some ⟨statsPc stage .maximum,
        .rd {loc := statsLoc l thread stage .maximum, size := 4} maximum⟩ := by
    have hi := atIndex 2 (by decide)
    rw [hCut, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hi
    exact hi
  have hRelease := ctaBarDone_of_returned hX hRawBar (show wait + 1 < (X.tr thread).length by omega)
  have hResume : Resumes kernel X (thread, wait) (thread, j) := by
    refine ⟨⟨rfl, by omega, hj⟩, ?_⟩
    simp [hRawBar, Kind.resume]
  have hLower : statsPc stage .maximum < u.pc := by omega
  have hUpper : u.pc ≤ lseWindow stage := by rw [hu]; fin_cases stage <;> decide
  have hAfter : lseWindow stage < w.pc := by
    rw [← hPc]
    change lseWindow stage < pc
    fin_cases stage <;> decide
  have hSel : KnownSelector stage u sum := by
    intro hStage hU
    have hu' : u.pc = 8468 := hu.trans (hStage.symm ▸ rfl)
    omega
  obtain ⟨state, before, after, hAt, hSplit, hInto, hOut, hSel, hFrame⟩ :=
    cutLseWindow stage hTail hLower hUpper (by rw [huSub]; decide) hAfter huSum hSel
  let bEvent : Event := ⟨statsBarrierPc stage false, .bar id (some 64) .sync⟩
  let sEvent : Event := ⟨statsPc stage .sum,
    .rd {loc := statsLoc l thread stage .sum, size := 4} sum⟩
  let mEvent : Event := ⟨statsPc stage .maximum,
    .rd {loc := statsLoc l thread stage .maximum, size := 4} maximum⟩
  let reached := (pre ++ [bEvent, sEvent, mEvent]) ++ before
  have hSplit' : es.take k = reached ++ after := by
    rw [hCut, hSplit]
    simp only [reached, List.append_assoc, List.cons_append, List.nil_append]
    rfl
  refine ⟨wait, sum, maximum, state, reached, after ++ es.drop k,
    by rw [← List.append_assoc, ← hSplit', List.take_append_drop],
    (TraceReach.of_local (run_rtg hLocal)).append (hPre.append hInto),
    ⟨terminalWaitObservation stage hRawBar, hResume, ⟨_, hRawSum⟩, ⟨_, hRawMax⟩,
      hBound, hRelease⟩, ?_, (hFrame 7134 (by simp)).trans huScale,
    fun h => hSel h (by rw [hAt, h]; decide)⟩
  refine ⟨reached, after, w, target, _, he, rfl, hAt, hSplit', hOut, hW, ?_, ?_⟩
  · intro v h
    exact (hFrame _ List.mem_cons_self).trans (huSum _ h)
  · intro v h
    exact (hFrame _ (List.mem_cons_of_mem _ List.mem_cons_self)).trans (huMax _ h)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {store : EvId} {stage : Fin 2}
    (hWork : store.1 / l.block < tilePrefix p p.batch * p.heads)
include hp hX hWork

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
