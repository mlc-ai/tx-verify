-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalNumerics
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOccurrence
public import Kernels.TmlFa4Fwd.Proof.SoftmaxStats
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsStoreGeometry
import Kernels.TmlFa4Fwd.Flow.Code.Part118
import Kernels.TmlFa4Fwd.Flow.Code.Part119

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax

open PTX PTX.Flow PTX.Proof PTX.EventFrame Thread

noncomputable section

private def terminalAddressInstruction (pc : Nat) (ins : Instr) : Bool :=
  ins.op.isLocal && nextPc ins.op pc == pc + 1 &&
    !(writesRegs ins.op).contains 7257 && !(writesRegs ins.op).contains 7256 &&
    match ins.op with
    | .brx .. => false
    | _ => true

private theorem terminalAddressCode {pc : Nat} {ins : Instr}
    (hLo : 7605 ≤ pc) (hHi : pc < 7614) (hc : kernel.code[pc]? = some ins) :
    terminalAddressInstruction pc ins = true := by
  let code := ((kernel.code.drop 7605).take 9).zipIdx 7605
  have hAudit : code.all (fun (i, n) => terminalAddressInstruction n i) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAudit (ins, pc)
  apply List.mem_of_getElem? (i := pc - 7605)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem noTerminalTau {l : Launch} {g : Nat} {s u : TState}
    (hSite : s.pc = 7614 ∨ s.pc = 7615 ∨ s.pc = 7616)
    (hStep : Tau kernel Assumptions.all l g s u) : False := by
  obtain ⟨ins, hc, _, hSource⟩ := tauScoreSource hStep
  rcases hSite with h | h | h
  · rw [h, Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_, hGuard⟩ | ⟨_, hLocal, _⟩
    · cases hGuard
    · cases hLocal
  · rw [h, Flow.code_7615] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_, hGuard⟩ | ⟨_, hLocal, _⟩
    · cases hGuard
    · cases hLocal
  · rw [h, Flow.code_7616] at hc
    obtain rfl := Option.some.inj hc
    rcases hSource with ⟨_, hGuard⟩ | ⟨_, hLocal, _⟩
    · cases hGuard
    · cases hLocal

private theorem terminalAddressFrame {l : Launch} {g : Nat} {t u : TState}
    (hPc : t.pc = 7605)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    7605 ≤ u.pc ∧ u.pc ≤ 7614 ∧ u.regs 7257 = t.regs 7257 ∧ u.regs 7256 = t.regs 7256 := by
  induction hLocal with
  | refl => exact ⟨hPc.ge, by omega, rfl, rfl⟩
  | @tail s u _ hStep ih =>
    obtain ⟨hLo, hHi, hSum, hMax⟩ := ih
    have hLt : s.pc < 7614 := by
      by_contra! h
      exact noTerminalTau (.inl (by omega)) hStep
    obtain ⟨ins, hc, _, hSource⟩ := tauScoreSource hStep
    have hAudit := terminalAddressCode hLo hLt hc
    simp only [terminalAddressInstruction, Bool.and_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at hAudit
    obtain ⟨⟨⟨⟨_, hNext⟩, hSumKept⟩, hMaxKept⟩, hNoBrx⟩ := hAudit
    rcases hSource with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
    · exact ⟨by simp [skip]; omega, by simp [skip]; omega, hSum, hMax⟩
    · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
        simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
        omega
      have hFrame := (scoreExecLocal hExec).resolve_right (fun ⟨_, h, _, _⟩ => hOff h)
      have hSucc := hFrame.pc.resolve_right (by cases hop : ins.op <;> simp_all [BrxTarget])
      rw [hNext] at hSucc
      exact ⟨by omega, by omega,
        (hFrame.regs _ (by simpa using hSumKept)).trans hSum,
        (hFrame.regs _ (by simpa using hMaxKept)).trans hMax⟩

private def threadReturn : Event := ⟨9205, .exit⟩

private theorem nextBeforeReturn {l : Launch} {g : Nat} {t : TState} {es : List Event}
    (hRun : Run kernel Assumptions.all l g t es none) (hExit : threadReturn ∈ es)
    (hBefore : ∀ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u → u.pc < 9205) :
    ∃ s u e rest, es = e :: rest ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t s ∧
      EStep kernel Assumptions.all l g s e (some u) ∧
      Run kernel Assumptions.all l g u rest none := by
  cases hRun with
  | step hs he hRun => exact ⟨_, _, _, _, rfl, hs, he, hRun⟩
  | last hs he =>
    have hPc := estep_source_pc he
    rw [← List.mem_singleton.mp hExit] at hPc
    exact (Nat.ne_of_lt (hBefore _ hs) hPc.symm).elim

private theorem terminalSiteLocal {l : Launch} {g : Nat} {t u : TState}
    (hSite : t.pc = 7614 ∨ t.pc = 7615 ∨ t.pc = 7616)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) : u = t := by
  rcases Relation.ReflTransGen.cases_head hLocal with h | ⟨_, h, _⟩
  · exact h.symm
  · exact (noTerminalTau hSite h).elim

private theorem storedValue {l : Launch} {g base src : Nat} {off : Int} {s u : TState}
    {e : Event} {v : Value} (hReg : s.regs src = some v) (hBytes : v.bytes = 4)
    (hFire : Fires s.pc (storeTmpl l g s .shared 32 base off [.reg src]) e (some u)) :
    (∃ a, e = ⟨s.pc, .wr a v.toBytes⟩) ∧ u.pc = s.pc + 1 ∧ u.regs = s.regs := by
  unfold storeTmpl at hFire
  split at hFire
  · cases hFire.2
  · cases hSub : s.sub with
    | zero =>
      simp only [hSub, List.getElem?_cons_zero, readValue, readReg, hReg, pure, Except.pure,
        bind, Except.bind, storeValue_of_bytes (w := 32) hBytes, Fires] at hFire
      obtain ⟨hEvent, hState⟩ := hFire
      cases hState
      exact ⟨⟨_, hEvent⟩, by simp [afterStore, hSub], by simp [afterStore, hSub]⟩
    | succ n =>
      simp only [hSub, List.getElem?_cons_succ, List.getElem?_nil, Fires] at hFire
      cases hFire.2

private theorem terminalStoreData {l : Launch} {g : Nat} {s u : TState} {e : Event} {v : Value}
    (hSource : (s.pc = 7614 ∧ s.regs 7257 = some v) ∨ (s.pc = 7615 ∧ s.regs 7256 = some v))
    (hBytes : v.bytes = 4) (he : EStep kernel Assumptions.all l g s e (some u)) :
    (∃ a, e = ⟨s.pc, .wr a v.toBytes⟩) ∧ u.pc = s.pc + 1 ∧ u.regs = s.regs := by
  obtain ⟨ins, hc, _, hFire⟩ := estep_event_source he
  rcases hSource with ⟨hPc, hReg⟩ | ⟨hPc, hReg⟩
  · rw [hPc, Flow.code_7614] at hc
    obtain rfl := Option.some.inj hc
    exact storedValue (base := 5814) (off := 368) hReg hBytes hFire
  · rw [hPc, Flow.code_7615] at hc
    obtain rfl := Option.some.inj hc
    exact storedValue (base := 5814) (off := 1392) hReg hBytes hFire

private theorem terminalDrainEvents {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {sum maximum : ℝ} (hPc : t.pc = 7605) (hSum : t.regs 7257 = some (fl sum))
    (hMax : t.regs 7256 = some (fl maximum))
    (hRun : Run kernel Assumptions.all l g t es none) (hExit : threadReturn ∈ es) :
    ∃ sumAcc maxAcc id count mode rest,
      es = ⟨7614, .wr sumAcc (fl sum).toBytes⟩ :: ⟨7615, .wr maxAcc (fl maximum).toBytes⟩ ::
        ⟨7616, .bar id count mode⟩ :: rest := by
  obtain ⟨s, u, e, rest, hes, hSteps, hStore, hRest⟩ := nextBeforeReturn hRun hExit
    (fun _ hu => (terminalAddressFrame hPc hu).2.1.trans_lt (by decide))
  obtain ⟨hLo, hHi, hsSum, hsMax⟩ := terminalAddressFrame hPc hSteps
  have hsPc : s.pc = 7614 := by
    by_contra! h
    obtain ⟨ins, hc, _, _⟩ := estep_event_source hStore
    have hCode := terminalAddressCode hLo (by omega) hc
    exact noLocalEvent hc (by
      simp only [terminalAddressInstruction, Bool.and_eq_true] at hCode
      exact hCode.1.1.1.1) hStore
  obtain ⟨⟨sumAcc, he⟩, huPc, huRegs⟩ :=
    terminalStoreData (.inl ⟨hsPc, hsSum.trans hSum⟩) rfl hStore
  rw [hsPc] at he huPc
  have hRestExit : threadReturn ∈ rest := by
    rw [hes, he, List.mem_cons] at hExit
    exact hExit.resolve_left (by simp [threadReturn])
  have huSite : u.pc = 7615 := huPc
  obtain ⟨v, w, f, tail, hr, hvSteps, hStoreMax, hTail⟩ :=
    nextBeforeReturn hRest hRestExit (fun _ hv => by
      rw [terminalSiteLocal (.inr (.inl huSite)) hv, huSite]
      decide)
  have hv := terminalSiteLocal (.inr (.inl huSite)) hvSteps
  subst v
  obtain ⟨⟨maxAcc, hf⟩, hwPc, _⟩ := terminalStoreData
    (.inr ⟨huSite, (congrFun huRegs 7256).trans (hsMax.trans hMax)⟩) rfl hStoreMax
  rw [huSite] at hf hwPc
  have hTailExit : threadReturn ∈ tail := by
    rw [hr, hf, List.mem_cons] at hRestExit
    exact hRestExit.resolve_left (by simp [threadReturn])
  have hwSite : w.pc = 7616 := hwPc
  obtain ⟨z, _, a, last, ht, hzSteps, hBar, _⟩ :=
    nextBeforeReturn hTail hTailExit (fun _ hz => by
      rw [terminalSiteLocal (.inr (.inr hwSite)) hz, hwSite]
      decide)
  have hz := terminalSiteLocal (.inr (.inr hwSite)) hzSteps
  subst z
  obtain ⟨id, count, mode, hKind⟩ :=
    (markedBarrierContinues hwSite Flow.code_7616 rfl hBar).2
  have hNotice : a = ⟨7616, .bar id count mode⟩ := by
    have ha := (estep_source_pc hBar).trans hwSite
    cases a
    simp_all
  exact ⟨sumAcc, maxAcc, id, count, mode, last, by rw [hes, he, hr, hf, ht, hNotice]⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- A reached drain with its two numerical words publishes their bytes in the actual trace.
The proof is independent of the number of preceding visits. -/
theorem terminalDrainPublication {g pos : Nat} {t : TState} {maximum sum : ℝ} (hPc : t.pc = 7605)
    (hSum : t.regs 7257 = some (fl sum)) (hMax : t.regs 7256 = some (fl maximum))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) (hExit : Thread.Exited X g) :
    ∃ sumAcc maxAcc : Acc,
      X.get (g, pos) = some ⟨7614, .wr sumAcc (fl sum).toBytes⟩ ∧
      X.get (g, pos + 1) = some ⟨7615, .wr maxAcc (fl maximum).toBytes⟩ ∧
      X.get (g, pos + 2) = some ⟨7616, .bar (3 + Prologue.warpIndex l g) (some 64) .arrive⟩ := by
  obtain ⟨last, ⟨site, kind⟩, he, hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  have hLen := Execution.exit_last hX (Step.CtaBar.thread_lt_of_get hX he) he
  change last + 1 = (X.tr g).length at hLen
  rw [actualExitPc hX he] at he
  have hPos : pos ≤ last := by
    by_contra! h
    have hNil : (X.tr g).drop pos = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [hNil] at hRun
    cases hRun
  have hReturn : threadReturn ∈ (X.tr g).drop pos := by
    apply List.mem_of_getElem? (i := last - pos)
    rw [List.getElem?_drop, Nat.add_sub_of_le hPos]
    exact he
  obtain ⟨sumAcc, maxAcc, id, count, mode, rest, hEvents⟩ :=
    terminalDrainEvents hPc hSum hMax hRun hReturn
  have get (n : Nat) : X.get (g, pos + n) = ((X.tr g).drop pos)[n]? :=
    List.getElem?_drop.symm
  refine ⟨sumAcc, maxAcc, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero, hEvents, List.getElem?_cons_zero] using get 0
  · simpa only [hEvents, List.getElem?_cons_succ, List.getElem?_cons_zero] using get 1
  · have hEvent : X.get (g, pos + 2) = some ⟨7616, .bar id count mode⟩ := by
      simpa only [hEvents, List.getElem?_cons_succ, List.getElem?_cons_zero] using get 2
    have hBarrier := actualNamedBarrier hp hX hEvent
    have hMode : mode = .arrive := hBarrier.2.2.1
    have hCount : count = some 64 := hBarrier.2.1
    subst mode
    have hId := actualSoftmaxStatsBarrierId hp hX (by decide : 7616 ∈ softmaxStatsSites) hEvent
    rwa [hId, hCount] at hEvent

/-- A reached drain publishes its words at the uniquely matched terminal notification. -/
theorem terminalDrainAtFinalPublication (warp : Fin 8) {g pos publication : Nat} {t : TState}
    {maximum sum : ℝ} (hWarp : warp.val = Prologue.warpIndex l g) (hPc : t.pc = 7605)
    (hSum : t.regs 7257 = some (fl sum)) (hMax : t.regs 7256 = some (fl maximum))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) (hExit : Thread.Exited X g)
    (hFinal : Scores.Publishes X (g, publication) .final) :
    X.get (g, publication - 2) = some ⟨7614, .wr (statsAcc l g warp 2) (fl sum).toBytes⟩ ∧
      X.get (g, publication - 2 + 1) = some ⟨7615, .wr (statsAcc l g warp 3) (fl maximum).toBytes⟩ ∧
      X.get (g, publication) = some ⟨7616, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      2 ≤ publication := by
  obtain ⟨sumAcc, maxAcc, hSum, hMax, hBar⟩ :=
    terminalDrainPublication hp hX hPc hSum hMax hRun hExit
  have hPub : Scores.Publishes X (g, pos + 2) .final := ⟨_, hBar, rfl⟩
  have hPos : publication = pos + 2 := by
    rcases lt_trichotomy publication (pos + 2) with h | h | h
    · exact (Scores.noPublicationAfterFinal hX hFinal h hPub).elim
    · exact h
    · exact (Scores.noPublicationAfterFinal hX hPub h hFinal).elim
  obtain ⟨sumWarp, hSumWarp, rfl⟩ := Scores.statisticsStoreFootprint hp hX 2 hSum
  obtain ⟨maxWarp, hMaxWarp, rfl⟩ := Scores.statisticsStoreFootprint hp hX 3 hMax
  have hSumWarp' : sumWarp = warp := Fin.ext (hSumWarp.trans hWarp.symm)
  have hMaxWarp' : maxWarp = warp := Fin.ext (hMaxWarp.trans hWarp.symm)
  subst sumWarp
  subst maxWarp
  subst publication
  refine ⟨?_, ?_, ?_, by omega⟩
  · simpa only [Nat.add_sub_cancel] using hSum
  · simpa only [Nat.add_sub_cancel] using hMax
  · simpa only [← hWarp] using hBar
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (warp : Fin 8)
    {g j batch head row biasCap pastTile publication : Nat}
    (hWarp : warp.val = Prologue.warpIndex l g) (hb : batch < p.batch)
    (hRow : row < p.qLength batch) (hBias : 0 < biasCap) (hCap : biasCap < 2^31)
    (hPast : pastTile + 256 < 2^31)
    (hRound : FirstRoundProgress p l X warp g j batch head row 1 biasCap pastTile)
    (hExit : Thread.Exited X g) (hFinal : Scores.Publishes X (g, publication) .final)
include hp hX warp hWarp hb hRow hBias hCap hPast hRound hExit hFinal

/-- The selected final publication receives the numerical words of the exiting one-visit
lane at the exact shared addresses used by the correction peer. -/
theorem singleVisitAtFinalPublicationWithReference :
    ∃ (maximum sum : ℝ),
      SoftmaxSumRun p batch head row 1 (fun _ => some (abiFloat p.scaleLog2Bits * maximum))
        (fun _ => sum) ∧
      firstReference p batch head row 1 = abiFloat p.scaleLog2Bits * maximum ∧
      X.get (g, publication - 2) = some ⟨7614, .wr (statsAcc l g warp 2) (fl sum).toBytes⟩ ∧
      X.get (g, publication - 2 + 1) = some ⟨7615, .wr (statsAcc l g warp 3) (fl maximum).toBytes⟩ ∧
      X.get (g, publication) = some ⟨7616, .bar (3 + warp.val) (some 64) .arrive⟩ ∧
      2 ≤ publication := by
  obtain ⟨t, pos, maximum, sum, hVisits, hReference, hPc, hSum, hMax, hRun⟩ :=
    oneVisitTerminalSumWithReference hp warp hb hRow hBias hCap hPast hRound
  exact ⟨maximum, sum, hVisits, hReference,
    terminalDrainAtFinalPublication hp hX warp hWarp hPc hSum hMax hRun hExit hFinal⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
