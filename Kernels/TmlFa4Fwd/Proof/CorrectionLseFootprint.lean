-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionLseEntry
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseAfter
public import Lemmas.Flow.TraceReach
import Kernels.TmlFa4Fwd.Proof.MmaLoopRank
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Lemmas.Flow.Final
import Lemmas.Flow.Footprint
import Lemmas.Flow.WriteSpace

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue Mma

noncomputable section

/-- The numerical LSE computations preserve the row/address registers needed by the stores. -/
private def lsePureWindow (second : Bool) : Nat × Nat × List Nat :=
  if second then (9074, 9079, [7077, 1613, 7491]) else (9061, 9065, [1635, 5967, 1613, 9525])

private def lseFallthrough (keys : List Nat) (i : Instr) : Bool :=
  i.op.isLocal && keys.all (fun r => !(writesRegs i.op).contains r) &&
    match i.op with
    | .bra .. | .brx .. => false
    | _ => true

theorem terminalNotWrite {l : Launch} {g pc : Nat} {s : TState} {a : Acc} {bs : List Byte}
    (he : EStep kernel Assumptions.all l g s ⟨pc, .wr a bs⟩ none) : False := by
  obtain ⟨m, _, hf⟩ := he
  rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h

/-- When the walk contains a later event, it crosses the intervening numerical instructions.
They may compute any legal payload, and any fault in that slice would terminate the walk. -/
private theorem crossLseNumerics (second : Bool) {l : Launch} {g lo hi : Nat}
    {s : TState} {target : Event} {F : List (Nat × Value)}
    {es : List Event} {vs : List Visit}
    (hLo : lo = (lsePureWindow second).1) (hHi : hi = (lsePureWindow second).2.1)
    (hF : ∀ rv ∈ F, rv.1 ∈ (lsePureWindow second).2.2)
    (hS : At s s.pc F) (hl : lo ≤ s.pc) (hh : s.pc ≤ hi)
    (hTerminal : ∀ t, t.pc ≤ hi → EStep kernel Assumptions.all l g t target none → False)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ u rest, At u hi F ∧ Walk kernel Assumptions.all l g u es rest ∧
      TraceReach kernel Assumptions.all l g s [] u := by
  induction hw with
  | stop => simp at he
  | @tau s u es vs ht hw ih =>
    by_cases hEnd : s.pc = hi
    · exact ⟨s, _, hEnd ▸ hS, .tau ht hw, .refl _⟩
    have hLower : 9061 ≤ s.pc := by
      cases second <;> simp [lsePureWindow] at hLo <;> omega
    have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hHealthy, hTau⟩ := correctionTauFrame hOff ht
    have hAll : ((kernel.code.drop lo).take (hi - lo)).all
        (lseFallthrough (lsePureWindow second).2.2) = true := by
      rw [hLo, hHi]
      cases second <;> set_option maxRecDepth 100000 in kernel_rfl
    have hMem : i ∈ (kernel.code.drop lo).take (hi - lo) := by
      apply List.mem_of_getElem? (i := s.pc - lo)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl, hc]
    have hCode := List.all_eq_true.mp hAll i hMem
    rcases hTau with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · have hp : (skip s).pc = s.pc + 1 := rfl
      obtain ⟨v, rest, hv, hWalk, hPath⟩ :=
        ih ⟨rfl, rfl, rfl, hHealthy, hS.2.2.2.2⟩ (by omega) (by omega) he
      exact ⟨v, rest, hv, hWalk, .tau ht hPath⟩
    · have hNext := hFrame.pc
      have hp : u.pc = s.pc + 1 := by
        cases hop : i.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
        case bra => simp [lseFallthrough, hop] at hCode
        case brx => simp [lseFallthrough, hop] at hCode
        all_goals exact hNext
      have hKeep (r : Nat) (hm : r ∈ (lsePureWindow second).2.2) : r ∉ writesRegs i.op := by
        simp only [lseFallthrough, Bool.and_eq_true] at hCode
        have h := List.all_eq_true.mp hCode.1.2 r hm
        simpa using h
      obtain ⟨v, rest, hv, hWalk, hPath⟩ :=
        ih ⟨rfl, hFrame.sub.trans hS.2.1, hFrame.acc.trans hS.2.2.1,
        hFrame.fault.trans hHealthy, holdsSchedulerFrame hS.2.2.2.2
          (fun r hm => hFrame.regs r (hKeep r hm)) hF⟩ (by omega) (by omega) he
      exact ⟨v, rest, hv, hWalk, .tau ht hPath⟩
  | @ev s u e es vs he' hw _ =>
    by_cases hEnd : s.pc = hi
    · exact ⟨s, _, hEnd ▸ hS, .ev he' hw, .refl _⟩
    obtain ⟨i, hc, hn, _⟩ := estep_event_source he'
    have hMem : i ∈ (kernel.code.drop lo).take (hi - lo) := by
      apply List.mem_of_getElem? (i := s.pc - lo)
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hl, hc]
    have hAll : ((kernel.code.drop lo).take (hi - lo)).all
        (lseFallthrough (lsePureWindow second).2.2) = true := by
      rw [hLo, hHi]
      cases second <;> set_option maxRecDepth 100000 in kernel_rfl
    have hCode := List.all_eq_true.mp hAll i hMem
    simp [lseFallthrough, hn] at hCode
  | @last s e h =>
    obtain rfl := (List.mem_singleton.mp he).symm
    exact (hTerminal _ hh h).elim


private theorem lseFootprintStoreCode (stage : Fin 2) :
    kernel.code[lseGuardPc stage + 1]? =
      some ⟨none, .mem {
        kind := .store, space := some .global, sem := .weak, elem := .int .b 32
        addr := ⟨.reg 7491 64, (512 * stage.val : Nat)⟩
        srcs := [.reg (lseOutReg stage)] }⟩ := by
  fin_cases stage
  · exact Flow.code_9073
  · exact Flow.code_9082

private theorem lseFootprintGuardCode (stage : Fin 2) :
    kernel.code[lseGuardPc stage]? =
      some ⟨some (lseTailPred stage, false), .bra (lseGuardPc stage + 2) false⟩ := by
  fin_cases stage
  · exact Flow.code_9072
  · exact Flow.code_9081

variable {p : Params} {l : Launch} {m : Mem0}

private theorem lseStoreEvent (hp : Pre p l m) (stage : Fin 2) {g batch head tile : Nat}
    {s u : TState} {e : Event} (hb : batch < p.batch) (hh : head < p.heads)
    (hr : stageRow tile stage + rowOf l g < p.qLength batch) (hPc : s.pc = lseGuardPc stage + 1)
    (hSub : s.sub = 0)
    (hB : s.regs 7491 = some (b64
      (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr))
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    ∃ bs, e = ⟨lseGuardPc stage + 1, .wr
        {loc := p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head, size := 4} bs⟩ ∧
      u = next s ∧
      (∀ v, s.regs (lseOutReg stage) = some v → v.bytes = 4 → bs = v.toBytes) := by
  let q := p.qOffset batch + stageRow tile stage + rowOf l g
  let base := (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr
  have hPacked : q < p.totalQ := by
    dsimp only [q]
    rw [Nat.add_assoc]
    exact hp.packedRow_lt hb hr
  have hRegion := lseByte_in (p := p) hPacked hh (k := 0) (by decide)
  have hRange := hp.ranges p.lseRegion (by simp)
  have hAddr : (p.lseLoc q head).addr < 2 ^ 64 := by
    have hz := hRegion.2.2.2
    change (p.lseLoc q head).addr + 0 < p.lseRegion.base + p.lseRegion.bytes at hz
    omega
  have hCalc : base + 512 * stage.val = (p.lseLoc q head).addr := by
    simp only [base, q, Params.lseLoc, globalLoc, stageRow]
    omega
  have hBase : base < 2 ^ 64 := by omega
  have hAlign : (p.lseLoc q head).addr % 4 = 0 := by
    have hLse := hp.alignment.2.2.2.2.2.2.2.2.2.2.2
    change (p.lseBase + 4 * (head * p.lseStride + q)) % 4 = 0
    omega
  have hEff : effAddr l g s .global 7491 (512 * stage.val : Nat) = .ok (p.lseLoc q head) := by
    change s.regs 7491 = some (b64 base) at hB
    have hBase' := truncBits_ofNat hBase (by decide : 64 ≤ 64)
    simp only [effAddr, readBits, readReg, hB, b64, hBase', bind, Except.bind,
      pure, Except.pure, BitVec.ofInt_natCast, ← BitVec.ofNat_add, hCalc]
    rw [toNat_ofNat_lt hAddr]
    rfl
  have hElem : elemAcc (p.lseLoc q head) (32 / 8) 1 0 =
      .ok {loc := p.lseLoc q head, size := 4} := by
    rw [elemAcc_ok (by decide) (by simpa only [Nat.mul_one] using hAlign)]
    simp only [Params.lseLoc, globalLoc, Loc.at, Nat.mul_zero, Nat.add_zero]
  obtain ⟨i, hc, _, hFire⟩ := estep_event_source he
  rw [hPc, lseFootprintStoreCode stage] at hc
  obtain rfl := Option.some.inj hc
  change Fires s.pc (storeTmpl l g s .global 32 7491 (512 * stage.val : Nat)
    [.reg (lseOutReg stage)]) e (some u) at hFire
  have hAfter : afterStore s [.reg (lseOutReg stage)] = next s := by
    unfold afterStore
    change (if s.sub + 1 < 1 then _ else _) = _
    rw [ite_eq_right (by omega), next, ← hSub]
  simp only [storeTmpl, hEff, bind, Except.bind, hSub, List.length_cons, List.length_nil,
    Nat.zero_add, hElem, List.getElem?_cons_zero] at hFire
  cases hv : readValue l g s 32 (.reg (lseOutReg stage)) with
  | error f => simp [hv, Fires] at hFire
  | ok v =>
    cases hs : storeValue 32 v with
    | error f => simp [hv, hs, Fires] at hFire
    | ok w =>
      simp only [hv, hs, Fires, Option.some.injEq, hPc, hAfter] at hFire
      refine ⟨w.toBytes, hFire.1, hFire.2, ?_⟩
      intro value hValue hBytes
      have hRead : readValue l g s 32 (.reg (lseOutReg stage)) = .ok value := by
        simp [readValue, readReg, hValue, pure, Except.pure]
      obtain rfl := Except.ok.inj (hv.symm.trans hRead)
      exact congrArg Value.toBytes (Except.ok.inj (hs.symm.trans (storeValue_of_bytes hBytes)))


/-- The actual guard skips a padded row or emits the corresponding store.
The payload is determined when the input frame supplies its four-byte register. -/
theorem traceLseStoreBranch (hp : Pre p l m) (stage : Fin 2) {g batch head tile : Nat} {s : TState}
    {F : List (Nat × Value)} {target : Event} {es : List Event} {vs : List Visit}
    (hb : batch < p.batch) (hh : head < p.heads)
    (hTest : s.regs (lseTailPred stage) =
      some (.pred (decide (p.qLength batch ≤ stageRow tile stage + rowOf l g))))
    (hBase : (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) ∈ F)
    (ht : At s (lseGuardPc stage) F)
    (hTerminal : ∀ t, t.pc = lseGuardPc stage + 1 →
      EStep kernel Assumptions.all l g t target none → False)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ u es' vs', At u (lseGuardPc stage + 2) F ∧ Walk kernel Assumptions.all l g u es' vs' ∧
      ((p.qLength batch ≤ stageRow tile stage + rowOf l g ∧ es = es') ∨
        (stageRow tile stage + rowOf l g < p.qLength batch ∧ ∃ bytes, (es =
          ⟨lseGuardPc stage + 1, .wr
            {loc := p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head, size := 4}
            bytes⟩ :: es') ∧
          (∀ v, (lseOutReg stage, v) ∈ F → v.bytes = 4 → bytes = v.toBytes))) ∧
      ∃ consumed, es = consumed ++ es' ∧ TraceReach kernel Assumptions.all l g s consumed u := by
  let test := p.qLength batch ≤ stageRow tile stage + rowOf l g
  obtain ⟨v, hv, hvAt⟩ := run_bra (A := []) (L := l) (g := g)
    (lseFootprintGuardCode stage) (decide test) ht hTest (by simp)
  have hOff : s.pc ∉ Assumptions.swExp2Sites := by rw [ht.1]; fin_cases stage <;> decide
  have hRun : run kernel Assumptions.all l g 1 s = some v := by
    simpa only [run, Assumptions.tauStep_all_eq_nil hOff
      (ht.1.symm ▸ lseFootprintGuardCode stage) rfl] using hv
  obtain hEmpty | ⟨tail, _, _, hW⟩ := advanceWalkLocals hRun hw
  · simp [hEmpty] at he
  by_cases hRow : stageRow tile stage + rowOf l g < p.qLength batch
  · have hFlag : ¬ test := Nat.not_le_of_gt hRow
    have hv' : At v (lseGuardPc stage + 1) F := by
      simpa only [hFlag, decide_false, Bool.false_eq_true, ↓reduceIte] using hvAt
    have hV := holds_mem hv'.2.2.2.2 hBase
    cases hW with
    | stop => simp at he
    | tau ht' _ =>
      have hDec := hv'.1.symm ▸ lseFootprintStoreCode stage
      have hOff' : v.pc ∉ Assumptions.swExp2Sites := by rw [hv'.1]; fin_cases stage <;> decide
      obtain ⟨i, hi, _, ht''⟩ := correctionTauFrame hOff' ht'
      rw [hDec] at hi
      obtain rfl := Option.some.inj hi
      rcases ht'' with ⟨_, hNever⟩ | ⟨_, hLocal, _⟩
      · cases hNever
      · cases hLocal
    | @last w e h =>
      obtain rfl := (List.mem_singleton.mp he).symm
      exact (hTerminal _ hv'.1 h).elim
    | @ev w u e es' vs' he' hw' =>
      obtain ⟨written, hEq, rfl, hValue⟩ :=
        lseStoreEvent hp stage hb hh hRow hv'.1 hv'.2.1 hV he'
      exact ⟨_, es', vs', hv'.next, hw', .inr ⟨hRow, written, by rw [hEq],
        fun v hm hv => hValue v (holds_mem hv'.2.2.2.2 hm) hv⟩,
        [e], rfl, (TraceReach.of_local (run_rtg hRun)).append (.event he' (.refl _))⟩
  · have hFlag : test := Nat.le_of_not_gt hRow
    have hv' : At v (lseGuardPc stage + 2) F := by
      simpa only [hFlag, decide_true, ↓reduceIte] using hvAt
    exact ⟨v, es, tail, hv', hW, .inl ⟨hFlag, rfl⟩,
      [], rfl, TraceReach.of_local (run_rtg hRun)⟩


/-- If the store site is live, its only returning step is the decoded row store. -/
private theorem cutLseStorePrefix (hp : Pre p l m) (stage : Fin 2) {g batch head tile target : Nat}
    {s : TState} {F : List (Nat × Value)} {a : Acc} {bs : List Byte} {es : List Event}
    {vs : List Visit} (hb : batch < p.batch) (hh : head < p.heads)
    (hTest : s.regs (lseTailPred stage) =
      some (.pred (decide (p.qLength batch ≤ stageRow tile stage + rowOf l g))))
    (hBase : (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr) ∈ F)
    (ht : At s (lseGuardPc stage) F) (hw : Walk kernel Assumptions.all l g s es vs)
    (he : ⟨target, .wr a bs⟩ ∈ es) :
    (target = lseGuardPc stage + 1 ∧ stageRow tile stage + rowOf l g < p.qLength batch ∧
      a.loc = p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head ∧ a.size = 4) ∨
    ∃ u es' vs', At u (lseGuardPc stage + 2) F ∧
      Walk kernel Assumptions.all l g u es' vs' ∧ ⟨target, .wr a bs⟩ ∈ es' := by
  obtain ⟨u, es', vs', hu, hWalk, hBranch, _⟩ :=
    traceLseStoreBranch hp stage hb hh hTest hBase ht (fun _ _ => terminalNotWrite) hw he
  rcases hBranch with ⟨_, rfl⟩ | ⟨hRow, bytes, hEs, _⟩
  · exact .inr ⟨u, es, vs', hu, hWalk, he⟩
  rw [hEs] at he
  rcases List.mem_cons.mp he with h | h
  · obtain ⟨hPc, hAcc, _⟩ := by simpa only [Event.mk.injEq, Kind.wr.injEq] using h
    exact .inl ⟨hPc, hRow, congrArg Acc.loc hAcc, congrArg Acc.size hAcc⟩
  · exact .inr ⟨u, es', vs', hu, hWalk, h⟩


theorem lseFirstGuardRun (hp : Pre p l m) {g batch head tile : Nat} {s : TState}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9065
      [(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)), (1613, b32 (rowOf l g)),
        (9525, b64 (p.lseLoc (p.qOffset batch) head).addr)]) :
    ∃ u, run kernel Assumptions.all l g 7 s = some u ∧
      u.regs 741 = some (.pred (decide (p.qLength batch ≤ stageRow tile 0 + rowOf l g))) ∧
      At u (lseGuardPc 0)
        [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
          (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)] ∧
      u.regs 1655 = s.regs 1655 := by
  have hLen := hp.qLength_fits hb
  have h31 : p.qLength batch < 2 ^ 31 := by omega
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hRun, ht⟩ := lseFirstTail (l := l) (g := g) h31 hTile hRow s
    (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hActual, hFrame⟩ := lseTailLinear (regs := [9525, 1655]) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRun
  have hPacked := (hFrame _ (by simp)).trans hs.2.2.2.2.2.2.2.1
  obtain ⟨u, hNext, hu⟩ := lseRowAddress (by omega) hRow t
    (ht.mono ⟨ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, hPacked, trivial⟩)
  obtain ⟨hActual', hFrame'⟩ := lseTailLinear (regs := [741, 7077, 1613, 1655]) (by decide) ht.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hNext
  exact ⟨u, run_comp hActual hActual',
    (hFrame' 741 (by simp)).trans ht.2.2.2.2.1,
    hu.mono ⟨(hFrame' 7077 (by simp)).trans ht.2.2.2.2.2.1,
      (hFrame' 1613 (by simp)).trans ht.2.2.2.2.2.2.2.1, hu.2.2.2.2.1, trivial⟩,
    (hFrame' 1655 (by simp)).trans (hFrame 1655 (by simp))⟩

theorem lseSecondGuardRun (hp : Pre p l m) {g batch head tile : Nat} {s : TState}
    (hb : batch < p.batch) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9079
      [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
        (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)]) :
    ∃ u, run kernel Assumptions.all l g 2 s = some u ∧
      u.regs 743 = some (.pred (decide (p.qLength batch ≤ stageRow tile 1 + rowOf l g))) ∧
      At u (lseGuardPc 1)
        [(7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)] ∧
      u.regs 1656 = s.regs 1656 := by
  have hLen := hp.qLength_fits hb
  have h31 : p.qLength batch < 2 ^ 31 := by omega
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  obtain ⟨t, hRun, ht⟩ := lseSecondTail (l := l) (g := g) h31 hTile hRow s
    (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, trivial⟩)
  obtain ⟨hActual, hFrame⟩ := lseTailLinear (regs := [7491, 1656]) (by decide) hs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hRun
  exact ⟨t, hActual, ht.2.2.2.2.1,
    ht.mono ⟨(hFrame _ (by simp)).trans hs.2.2.2.2.2.2.1, trivial⟩, hFrame 1656 (by simp)⟩


def lseFootprintEntryFacts (p : Params) (l : Launch) (g batch head tile : Nat) :
    List (Nat × Value) :=
  [(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)), (1613, b32 (rowOf l g)),
    (1634, b32 (p.qOffset batch)), (9605, b64 head), (7501, b64 p.lseStride),
    (7500, b64 p.lseBase)]

/-- Enter the first numerical LSE window with the exact packed-row address registers. -/
theorem lseFirstStartFromWalk (hp : Pre p l m) {g batch head tile : Nat} {s : TState}
    {target : Event} {es : List Event} {vs : List Visit} (hb : batch < p.batch)
    (hh : head < p.heads) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9057 (lseFootprintEntryFacts p l g batch head tile))
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ t rest, At t 9061
      [(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)), (1613, b32 (rowOf l g)),
        (9525, b64 (p.lseLoc (p.qOffset batch) head).addr)] ∧
      Walk kernel Assumptions.all l g t es rest ∧ TraceReach kernel Assumptions.all l g s [] t := by
  obtain ⟨t, ht, hRun⟩ := correctionLseBaseRun hp (g := g) hb hh (by omega) hs
    (by simp [lseFootprintEntryFacts]) (by simp [lseFootprintEntryFacts])
    (by simp [lseFootprintEntryFacts]) (by simp [lseFootprintEntryFacts])
    (by set_option maxRecDepth 100000 in kernel_rfl)
  rcases advanceWalkLocals hRun hw with h | ⟨tail, _, _, hW⟩
  · simp [h] at he
  let packed := (9525, b64 (p.lseLoc (p.qOffset batch) head).addr)
  let F := [(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)),
    (1613, b32 (rowOf l g)), packed]
  have ht' : At t 9061 F :=
    ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.1, trivial⟩
  exact ⟨t, tail, ht', hW, TraceReach.of_local (run_rtg hRun)⟩

theorem lseFirstGuardFromWalk (hp : Pre p l m) {g batch head tile : Nat} {s : TState}
    {target : Event} {es : List Event} {vs : List Visit} (hb : batch < p.batch)
    (hh : head < p.heads) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9057 (lseFootprintEntryFacts p l g batch head tile))
    (hBeforeNumerics : ∀ t, t.pc ≤ 9065 → EStep kernel Assumptions.all l g t target none → False)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ v rest, v.regs 741 = some (.pred (decide (p.qLength batch ≤ stageRow tile 0 + rowOf l g))) ∧
      At v (lseGuardPc 0)
        [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
          (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)] ∧
      Walk kernel Assumptions.all l g v es rest ∧ TraceReach kernel Assumptions.all l g s [] v := by
  obtain ⟨t, _, ht, hW, hStart⟩ := lseFirstStartFromWalk hp hb hh hTile hs hw he
  let packed := (9525, b64 (p.lseLoc (p.qOffset batch) head).addr)
  let F := [(1635, b32 (p.qLength batch)), (5967, b32 (256 * tile)),
    (1613, b32 (rowOf l g)), packed]
  have ht' : At t t.pc F := ⟨rfl, ht.2⟩
  have hTp : t.pc = 9061 := ht.1
  obtain ⟨u, uvs, hu, hUW, hNumeric⟩ := crossLseNumerics false (hi := 9065) (lo := 9061)
    rfl rfl (by intro rv hm; simpa [F, packed, lsePureWindow] using
      List.mem_map_of_mem (f := Prod.fst) hm) ht' hTp.ge (by omega) hBeforeNumerics hW he
  obtain ⟨v, hVRun, hPred, hv, _⟩ := lseFirstGuardRun hp hb hTile hu
  rcases advanceWalkLocals hVRun hUW with h | ⟨vvs, _, _, hVW⟩
  · simp [h] at he
  exact ⟨v, vvs, hPred, hv, hVW,
    (hStart.append hNumeric).append (TraceReach.of_local (run_rtg hVRun))⟩

private theorem lseSecondGuardFromWalk (hp : Pre p l m) {g batch head tile : Nat} {w : TState}
    {target : Event} {wes : List Event} {vs : List Visit} (hb : batch < p.batch)
    (hTile : 256 * tile < p.qLength batch)
    (hwAt : At w 9074
        [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
          (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)])
    (hBeforeNumerics : ∀ t, t.pc ≤ 9079 → EStep kernel Assumptions.all l g t target none → False)
    (hwW : Walk kernel Assumptions.all l g w wes vs) (he : target ∈ wes) :
    ∃ y rest, y.regs 743 = some (.pred (decide (p.qLength batch ≤ stageRow tile 1 + rowOf l g))) ∧
      At y (lseGuardPc 1)
        [(7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)] ∧
      Walk kernel Assumptions.all l g y wes rest := by
  have hWp : w.pc = 9074 := hwAt.1
  have hwAt' : At w w.pc
      [(7077, b32 (p.qLength batch - 256 * tile)), (1613, b32 (rowOf l g)),
       (7491, b64 (p.lseLoc (p.qOffset batch + stageRow tile 0 + rowOf l g) head).addr)] :=
    ⟨rfl, hwAt.2⟩
  obtain ⟨x, xvs, hx, hxW, _⟩ := crossLseNumerics true (hi := 9079) (lo := 9074)
    rfl rfl (by intro rv hm; simpa [lsePureWindow] using
      List.mem_map_of_mem (f := Prod.fst) hm) hwAt' hWp.ge (by omega) hBeforeNumerics hwW he
  obtain ⟨y, hYRun, hyPred, hy, _⟩ := lseSecondGuardRun hp hb hTile hx
  rcases advanceWalkLocals hYRun hxW with h | ⟨yvs, _, _, hyW⟩
  · simp [h] at he
  exact ⟨y, yvs, hyPred, hy, hyW⟩

/-- Any actual LSE write from the tile address checkpoint is a full word on a valid query row.
The numerical LSE payload is arbitrary, and the walk may stop anywhere. -/
theorem correctionLseFootprintFromReady (hp : Pre p l m) {g batch head tile pc : Nat} {s : TState}
    {a : Acc} {bs : List Byte} {es : List Event} {vs : List Visit} (hb : batch < p.batch)
    (hh : head < p.heads) (hTile : 256 * tile < p.qLength batch)
    (hs : At s 9057 (lseFootprintEntryFacts p l g batch head tile)) (hPc : pc = 9073 ∨ pc = 9082)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : ⟨pc, .wr a bs⟩ ∈ es) :
    ∃ stage : Fin 2, pc = lseGuardPc stage + 1 ∧
      stageRow tile stage + rowOf l g < p.qLength batch ∧
      a.loc = p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head ∧ a.size = 4 := by
  obtain ⟨v, _, hPred, hv, hVW, _⟩ :=
    lseFirstGuardFromWalk hp hb hh hTile hs (fun _ _ => terminalNotWrite) hw he
  rcases cutLseStorePrefix hp 0 hb hh hPred (by simp) hv hVW he with h |
      ⟨w, wes, wvs, hwAt, hwW, hwE⟩
  · exact ⟨0, h⟩
  obtain ⟨y, _, hyPred, hy, hyW⟩ :=
    lseSecondGuardFromWalk hp hb hTile hwAt (fun _ _ => terminalNotWrite) hwW hwE
  rcases cutLseStorePrefix hp 1 hb hh hyPred (by simp) hy hyW hwE with h |
      ⟨z, zs, zvs, hz, hzW, hzE⟩
  · exact ⟨1, h⟩
  · have hZ : z.pc = 9083 := hz.1
    have hSub : z.sub ≤ 3 := by rw [hz.2.1]; decide
    exact (noLseAfterTile (by omega) hZ.ge hSub hzW hzE).elim

/-- A correction row that is in bounds writes one FP32 LSE word en route to a later event. -/
theorem correctionLseWriterFromReady (hp : Pre p l m) {g batch head tile : Nat} {s : TState}
    {target : Event} {es : List Event} {vs : List Visit} (stage : Fin 2) (hb : batch < p.batch)
    (hh : head < p.heads) (hTile : 256 * tile < p.qLength batch)
    (hRow : stageRow tile stage + rowOf l g < p.qLength batch)
    (hs : At s 9057 (lseFootprintEntryFacts p l g batch head tile)) (hLate : 9083 < target.pc)
    (hw : Walk kernel Assumptions.all l g s es vs) (he : target ∈ es) :
    ∃ bytes, (⟨lseGuardPc stage + 1, .wr
      {loc := p.lseLoc (p.qOffset batch + stageRow tile stage + rowOf l g) head, size := 4}
      bytes⟩ : Event) ∈ es := by
  have hTerminal {n : Nat} (hn : n < target.pc) :
      ∀ t, t.pc ≤ n → EStep kernel Assumptions.all l g t target none → False := by
    intro t ht he
    have hPC := estep_source_pc he
    omega
  obtain ⟨v, _, hPred, hv, hVW, _⟩ :=
    lseFirstGuardFromWalk hp hb hh hTile hs (hTerminal (by omega)) hw he
  obtain ⟨w, wes, _, hwAt, hwW, hBranch, _⟩ :=
    traceLseStoreBranch hp 0 hb hh hPred (by simp) hv
      (fun _ hPc => hTerminal (n := 9073) (by omega) _ hPc.le) hVW he
  fin_cases stage
  · have hRow' : stageRow tile 0 + rowOf l g < p.qLength batch := hRow
    rcases hBranch with ⟨hTail, _⟩ | ⟨_, bytes, hEs, _⟩
    · exact (Nat.not_le_of_gt hRow' hTail).elim
    · exact ⟨bytes, hEs.symm ▸ List.mem_cons_self⟩
  have hRest : target ∈ wes ∧ wes ⊆ es := by
    rcases hBranch with ⟨_, rfl⟩ | ⟨_, bytes, hEs, _⟩
    · exact ⟨he, fun _ h => h⟩
    · rw [hEs, List.mem_cons] at he
      refine ⟨he.resolve_left ?_, fun _ h => hEs.symm ▸ List.mem_cons_of_mem _ h⟩
      intro hEq
      have hp := congrArg Event.pc hEq
      change target.pc = 9073 at hp
      omega
  obtain ⟨y, _, hyPred, hy, hyW⟩ :=
    lseSecondGuardFromWalk hp hb hTile hwAt (hTerminal (by omega)) hwW hRest.1
  obtain ⟨_, _, _, _, _, hBranch, _⟩ :=
    traceLseStoreBranch hp 1 hb hh hyPred (by simp) hy
      (fun _ hPc => hTerminal (n := 9082) (by omega) _ hPc.le) hyW hRest.1
  have hRow' : stageRow tile 1 + rowOf l g < p.qLength batch := hRow
  rcases hBranch with ⟨hTail, _⟩ | ⟨_, bytes, hEs, _⟩
  · exact (Nat.not_le_of_gt hRow' hTail).elim
  · exact ⟨bytes, hRest.2 (hEs.symm ▸ List.mem_cons_self)⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
