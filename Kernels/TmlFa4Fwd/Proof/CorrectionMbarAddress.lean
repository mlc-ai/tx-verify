-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionEntry
public import Kernels.TmlFa4Fwd.Proof.CorrectionPrefixEvents
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Step.CtaBar
import Lemmas.Flow.EventCont
import Lemmas.Flow.TcTmpl
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
import Kernels.TmlFa4Fwd.Flow.Code.Part121
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Flow.Code.Part128
import Kernels.TmlFa4Fwd.Flow.Code.Part131
import Kernels.TmlFa4Fwd.Flow.Code.Part132
import Kernels.TmlFa4Fwd.Flow.Code.Part136
import Kernels.TmlFa4Fwd.Flow.Code.Part137
import Kernels.TmlFa4Fwd.Flow.Code.Part141
import Kernels.TmlFa4Fwd.Flow.Code.Part143

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Prologue Softmax Epilogue Mma

noncomputable section

private def fixedCorrections (l : Launch) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (1069, b32 (l.sharedBase + 192)),
   (6495, b32 (l.sharedBase + 144)), (6497, b32 (l.sharedBase + 224)),
   (2390, b32 (l.sharedBase + 208))]

private def corrAddrScope (defPc pc : Nat) : Prop :=
  if defPc = 8768 then 8769 ≤ pc ∧ pc < 8775
  else if defPc = 7751 then 7752 ≤ pc ∧ pc ≤ 7754
  else if defPc = 7986 then pc = 7987
  else if defPc = 8222 then 8223 ≤ pc ∧ pc ≤ 8224
  else if defPc = 8441 then 8442 ≤ pc ∧ pc ≤ 8443
  else if defPc = 8463 then 8464 ≤ pc ∧ pc ≤ 9056
  else defPc < pc

private instance (defPc pc : Nat) : Decidable (corrAddrScope defPc pc) := by
  unfold corrAddrScope
  infer_instance

private def corrAddrAdds : List (Nat × Nat × Nat) :=
  [(7750, 1614, 96), (7753, 1615, 104), (7937, 1628, 200),
   (7948, 7131, 232), (8768, 6499, 152)]

private def corrCreditCounts : List (Nat × Nat × Nat) :=
  [(7751, 5868, 0), (7986, 5978, 0), (8222, 6236, 0), (8441, 6494, 0), (8463, 6498, 0)]

private def corrDefinitions : List (Nat × Nat × Nat) := corrAddrAdds ++ corrCreditCounts

private def correctionValue (l : Launch) (defPc delta : Nat) : Value :=
  b32 (if defPc ∈ [7751, 7986, 8222, 8441, 8463] then 1 else l.sharedBase + delta)

private def corrAddrFrame (l : Launch) (t : TState) : Prop :=
  t.sub ≤ 3 ∧ Holds t.regs (fixedCorrections l) ∧
  ∀ defPc reg delta, (defPc, reg, delta) ∈ corrDefinitions → corrAddrScope defPc t.pc →
    t.regs reg = some (correctionValue l defPc delta)

private def corrAddrWrites (op : Op) : List Nat := writesRegs op ++ scoreEventWrites op

private def corrAddrCode (pc : Nat) (i : Instr) : Bool :=
  (i.op.isLocal || correctionReturningOp i.op) &&
  [2535, 1069, 6495, 6497, 2390].all (fun r => !(corrAddrWrites i.op).contains r) &&
  corrDefinitions.all (fun (defPc, r, _) =>
    (pc == defPc && i.guard.isNone || !(corrAddrWrites i.op).contains r) &&
    (if corrAddrScope defPc (pc + 1) then pc == defPc || decide (corrAddrScope defPc pc)
      else true)) &&
  match i.op with
  | .bra target _ => 7745 ≤ target && target ≤ 9205 &&
      corrDefinitions.all (fun (defPc, _, _) =>
        !decide (corrAddrScope defPc target) || decide (corrAddrScope defPc pc))
  | .brx .. => false
  | _ => true

private theorem corrAddrCodeAt {pc : Nat} {i : Instr}
    (hLo : 7745 ≤ pc) (hHi : pc < 9205) (hc : kernel.code[pc]? = some i) :
    corrAddrCode pc i = true := by
  let code := ((kernel.code.drop 7745).take (9205 - 7745)).zipIdx 7745
  have hAll : code.all (fun (ins, site) => corrAddrCode site ins) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hAll (i, pc)
  apply List.mem_of_getElem? (i := pc - 7745)
  dsimp only [code]
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

section
variable {p : Params} {l : Launch} {m : Mem0}

private theorem corrAddrAdd (hp : Pre p l m) {g : Nat} {s u : TState} {defPc reg delta : Nat}
    (hDef : (defPc, reg, delta) ∈ corrAddrAdds) (hPc : s.pc = defPc) (hf : s.fault = none)
    (hb : s.regs 2535 = some (b32 l.sharedBase)) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs reg = some (b32 (l.sharedBase + delta)) := by
  have hc : kernel.code[defPc]? = some ⟨none,
      .int ⟨.add, .int .s 32, false, [some reg], [.reg 2535, .imm delta]⟩⟩ := by
    simp only [corrAddrAdds, List.mem_cons, List.not_mem_nil, or_false] at hDef
    rcases hDef with h | h | h | h | h <;> cases h
    · exact Flow.code_7750
    · exact Flow.code_7753
    · exact Flow.code_7937
    · exact Flow.code_7948
    · exact Flow.code_8768
  have hMax : delta ≤ 232 := by
    simp only [corrAddrAdds, List.mem_cons, List.not_mem_nil, or_false] at hDef
    rcases hDef with h | h | h | h | h <;> cases h <;> decide
  have hBound : l.sharedBase + delta < 2 ^ 32 := by have := hp.shared.2.1; omega
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    have hSites : s.pc ∉ Assumptions.swExp2Sites ∧
        s.pc ∉ Assumptions.tcLdDataflowSites ∧ s.pc ∉ Assumptions.delayedTmemSites := by
      rw [hPc]
      simp only [corrAddrAdds, List.mem_cons, List.not_mem_nil, or_false] at hDef
      rcases hDef with h | h | h | h | h <;> cases h <;> decide
    have hCore := Assumptions.out_all_eq_nil (L := l) (g := g)
      hSites.1 hSites.2.1 hSites.2.2 (hPc.symm ▸ hc) rfl
    rw [← hCore]
    exact ht
  have hu := Option.some.inj ((tauStep_iff.mpr ht').symm.trans
    (evalSharedAdd hPc hf hb hBound hc))
  subst u
  exact Function.update_self _ _ _

private theorem correctionMoveOne {l : Launch} {g : Nat} {s u : TState}
    {defPc reg delta : Nat} (hDef : (defPc, reg, delta) ∈ corrCreditCounts)
    (hPc : s.pc = defPc) (hf : s.fault = none) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs reg = some (correctionValue l defPc delta) := by
  let op := Op.move ⟨.scalar, .int .b 32, [some reg], [.imm 1]⟩
  have hc : kernel.code[s.pc]? = some ⟨none, op⟩ := by
    rw [hPc]
    simp only [corrCreditCounts, List.mem_cons, List.not_mem_nil, or_false] at hDef
    rcases hDef with h | h | h | h | h <;> cases h
    · exact Flow.code_7751
    · exact Flow.code_7986
    · exact Flow.code_8222
    · exact Flow.code_8441
    · exact Flow.code_8463
  have hs : s.pc ∉ Assumptions.swExp2Sites ∧ s.pc ∉ Assumptions.tcLdDataflowSites ∧
      s.pc ∉ Assumptions.delayedTmemSites := by
    rw [hPc]
    simp only [corrCreditCounts, List.mem_cons, List.not_mem_nil, or_false] at hDef
    rcases hDef with h | h | h | h | h <;> cases h <;> decide
  have hv : correctionValue l defPc delta = b32 1 := by
    simp only [corrCreditCounts, List.mem_cons, List.not_mem_nil, or_false] at hDef
    rcases hDef with h | h | h | h | h <;> cases h <;> rfl
  have hExec : execLocalA [] l g s op = .ok (next (setReg s reg (b32 1))) := by
    dsimp only [op]
    rw [execLocalA_nil, execLocal_move rfl]
    simp [execMove, readValue, readBits, Value.bytes, b32, bind, Except.bind, pure, Except.pure,
      DType.width, truncBits]
  unfold Tau at ht
  rw [Assumptions.out_all_eq_nil hs.1 hs.2.1 hs.2.2 hc rfl] at ht
  simp only [out, hf, hc, guardHolds, pure, Except.pure,
    show op.isLocal = true from rfl, ↓reduceIte, hExec, Out.tau.injEq] at ht
  subst u
  rw [hv]
  exact Function.update_self _ _ _

private theorem correctionDef (hp : Pre p l m) {g : Nat} {s u : TState} {defPc reg delta : Nat}
    (hDef : (defPc, reg, delta) ∈ corrDefinitions) (hPc : s.pc = defPc) (hf : s.fault = none)
    (hb : s.regs 2535 = some (b32 l.sharedBase)) (ht : Tau kernel Assumptions.all l g s u) :
    u.regs reg = some (correctionValue l defPc delta) := by
  rcases List.mem_append.mp hDef with h | h
  · have hValue : correctionValue l defPc delta = b32 (l.sharedBase + delta) := by
      simp only [corrAddrAdds, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h <;> cases h <;> rfl
    rw [hValue]
    exact corrAddrAdd hp h hPc hf hb ht
  · exact correctionMoveOne h hPc hf ht

private theorem corrAddrStep (hp : Pre p l m) {g : Nat} {s u : TState} {e : Option Event}
    (hLo : 7745 ≤ s.pc) (hHi : s.pc < 9205) (hFrame : corrAddrFrame l s)
    (hw : WStep kernel Assumptions.all l g s e u) :
    7745 ≤ u.pc ∧ u.pc ≤ 9205 ∧ corrAddrFrame l u := by
  have hBase := hFrame.2.1.1
  have hScoped {i : Instr} (hc : kernel.code[s.pc]? = some i) {d r off : Nat}
      (hDef : (d, r, off) ∈ corrDefinitions) :
      ((s.pc == d && i.guard.isNone || !(corrAddrWrites i.op).contains r) &&
        (if corrAddrScope d (s.pc + 1) then s.pc == d || decide (corrAddrScope d s.pc)
          else true)) = true := by
    have h := corrAddrCodeAt hLo hHi hc
    simp only [corrAddrCode, Bool.and_eq_true] at h
    exact List.all_eq_true.mp h.1.2 (d, r, off) hDef
  have hFall {i : Instr} (hc : kernel.code[s.pc]? = some i) {d r off : Nat}
      (hDef : (d, r, off) ∈ corrDefinitions) (hNext : u.pc = s.pc + 1)
      (hScope : corrAddrScope d u.pc) : s.pc = d ∨ corrAddrScope d s.pc := by
    rw [hNext] at hScope
    have h := hScoped hc hDef
    rw [Bool.and_eq_true] at h
    simpa [hScope] using h.2
  have hFixed {i : Instr} (hc : kernel.code[s.pc]? = some i) {r : Nat}
      (hr : r ∈ [2535, 1069, 6495, 6497, 2390]) :
      r ∉ corrAddrWrites i.op := by
    have h := corrAddrCodeAt hLo hHi hc
    simp only [corrAddrCode, Bool.and_eq_true] at h
    simpa using List.all_eq_true.mp h.1.1.2 r hr
  have finish {i : Instr} (hc : kernel.code[s.pc]? = some i)
      (hPc : 7745 ≤ u.pc ∧ u.pc ≤ 9205) (hSub : u.sub ≤ 3)
      (hKeep : ∀ r, r ∉ corrAddrWrites i.op → u.regs r = s.regs r)
      (hEntry : ∀ d r off, (d, r, off) ∈ corrDefinitions → corrAddrScope d u.pc →
        s.pc = d ∨ corrAddrScope d s.pc)
      (hNew : ∀ d r off, (d, r, off) ∈ corrDefinitions → s.pc = d →
        u.regs r = some (correctionValue l d off)) :
      7745 ≤ u.pc ∧ u.pc ≤ 9205 ∧ corrAddrFrame l u := by
    refine ⟨hPc.1, hPc.2, hSub, ?_, ?_⟩
    · apply holdsSchedulerFrame (regs := [2535, 1069, 6495, 6497, 2390]) hFrame.2.1
      · exact fun r hr => hKeep r (hFixed hc hr)
      · intro pair h
        simp only [fixedCorrections, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl <;> simp
    · intro d r off hDef hScope
      by_cases hEq : s.pc = d
      · exact hNew d r off hDef hEq
      · have hPrior := (hEntry d r off hDef hScope).resolve_left hEq
        have hReg : r ∉ corrAddrWrites i.op := by
          have h := hScoped hc hDef
          rw [Bool.and_eq_true] at h
          simpa [hEq] using h.1
        exact (hKeep r hReg).trans (hFrame.2.2 d r off hDef hPrior)
  rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
  · have hOff : s.pc ∉ Assumptions.swExp2Sites := by
      simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    obtain ⟨i, hc, hf, hStep⟩ := correctionTauFrame hOff ht
    have hNew := fun d r off hDef hPc => correctionDef hp (defPc := d) (reg := r)
      (delta := off) hDef hPc hf hBase ht
    rcases hStep with ⟨rfl, _⟩ | ⟨_, _, hFrame⟩
    · refine finish hc (by change 7745 ≤ s.pc + 1 ∧ s.pc + 1 ≤ 9205; omega)
        (Nat.zero_le _) (fun _ _ => rfl) (fun d r off hm hs => hFall hc hm rfl hs) hNew
    · have hPc := hFrame.pc
      have hCode := corrAddrCodeAt hLo hHi hc
      simp only [corrAddrCode, Bool.and_eq_true] at hCode
      refine finish hc ?_ (hFrame.sub.symm ▸ (show s.sub ≤ 3 from ‹corrAddrFrame l s›.1))
        (fun r hr => hFrame.regs r (fun hm => hr (List.mem_append_left _ hm))) ?_ hNew
      · cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra target uni =>
          simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hCode
          omega
        case brx => simp [ho] at hCode
        all_goals omega
      · intro d r off hm hs
        cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hPc
        case bra target uni =>
          have hBra := hCode.2
          simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at hBra
          have h := List.all_eq_true.mp hBra.2 (d, r, off) hm
          rw [hPc] at hs
          exact .inr (by simpa [hs] using h)
        case brx => simp [ho] at hCode
        all_goals exact hFall hc hm hPc hs
  · obtain ⟨i, hc, hLocal, _⟩ := estep_event_source he
    have hCode := corrAddrCodeAt hLo hHi hc
    simp only [corrAddrCode, Bool.and_eq_true, hLocal, Bool.false_or] at hCode
    have hProg := (correctionEventProgress (r := 2535) hc hCode.1.1.1 hFrame.1
      (fun h => hFixed hc (by decide) (List.mem_append_right _ h)) he).1
    have hPc : u.pc = s.pc ∨ u.pc = s.pc + 1 :=
      hProg.pc.elim (fun h => .inr h.1) (fun h => .inl h.1)
    refine finish hc (by omega) hProg.sub (fun r hr =>
      (correctionEventProgress hc hCode.1.1.1 hFrame.1
        (fun h => hr (List.mem_append_right _ h)) he).2) ?_ ?_
    · intro d r off hm hs
      rcases hPc with h | h
      · exact .inr (h ▸ hs)
      · exact hFall hc hm h hs
    · intro d r off hm hEq
      rw [hEq] at hc
      simp only [corrDefinitions, corrAddrAdds, corrCreditCounts, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h | h | h | h | h <;> cases h
      all_goals first
        | rw [Flow.code_7750] at hc
        | rw [Flow.code_7753] at hc
        | rw [Flow.code_7937] at hc
        | rw [Flow.code_7948] at hc
        | rw [Flow.code_8768] at hc
        | rw [Flow.code_7751] at hc
        | rw [Flow.code_7986] at hc
        | rw [Flow.code_8222] at hc
        | rw [Flow.code_8441] at hc
        | rw [Flow.code_8463] at hc
      all_goals obtain rfl := Option.some.inj hc.symm
      all_goals cases hLocal

/-- The terminal role instruction can only emit its final event. -/
theorem correctionReturnTail {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit} (hPc : s.pc = 9205)
    (hw : Walk kernel Assumptions.all l g s events visits)
    {e : Event} (hm : e ∈ events) : e.pc = 9205 := by
  obtain ⟨tm, ho, hDone⟩ : ∃ tm, out kernel Assumptions.all l g s = .ev tm ∧
      ∀ event u, ¬ Fires s.pc tm event (some u) := by
    cases hf : s.fault with
    | none =>
      refine ⟨.exit, ?_, fun event u h => nomatch h.2⟩
      rw [out_event hf (hPc.symm ▸ Flow.code_9205) rfl rfl]
      rfl
    | some f =>
      exact ⟨.ub f, by simp [out, hf], fun event u h => nomatch h.2⟩
  cases hw with
  | stop => cases hm
  | tau ht _ => exact (not_tau_of_stops ⟨_, ho⟩ ht).elim
  | ev he _ =>
    obtain ⟨tm', hm, hf⟩ := he
    obtain rfl := Out.ev.inj (hm.symm.trans ho)
    exact (hDone _ _ hf).elim
  | last he =>
    obtain rfl := List.mem_singleton.mp hm
    exact (estep_source_pc he).trans hPc

private theorem corrAddrWalk (hp : Pre p l m) {g : Nat} {s : TState} {events : List Event}
    {visits : List Visit} (hWalk : Walk kernel Assumptions.all l g s events visits)
    (hLo : 7745 ≤ s.pc) (hHi : s.pc ≤ 9205) (hF : corrAddrFrame l s) {Q : TState → Prop} (hQ : Q s)
    (hStep : ∀ {s u event}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 → Q s →
      WStep kernel Assumptions.all l g s event u → Q u) {e : Event} (hm : e ∈ events)
    (hEnd : e.pc < 9205) :
    ∃ t o, t.pc = e.pc ∧ corrAddrFrame l t ∧ Q t ∧
      EStep kernel Assumptions.all l g t e o := by
  induction hWalk with
  | stop => cases hm
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 9205
    · exact (Nat.ne_of_lt hEnd (correctionReturnTail hExit (.tau ht hw) hm)).elim
    obtain ⟨hl, hh, hF'⟩ := corrAddrStep hp hLo (by omega) hF (.inl ⟨rfl, ht⟩)
    exact ih hl hh hF' (hStep hLo (by omega) hF.1 hQ (.inl ⟨rfl, ht⟩)) hm
  | @ev s u ev events visits he hw ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨_, _, (estep_source_pc he).symm, hF, hQ, he⟩
    · by_cases hExit : s.pc = 9205
      · exact (Nat.ne_of_lt hEnd (correctionReturnTail hExit (.ev he hw)
          (List.mem_cons_of_mem _ hm))).elim
      obtain ⟨hl, hh, hF'⟩ := corrAddrStep hp hLo (by omega) hF (.inr ⟨_, rfl, he⟩)
      exact ih hl hh hF' (hStep hLo (by omega) hF.1 hQ (.inr ⟨_, rfl, he⟩)) hm
  | last he =>
    obtain rfl := List.mem_singleton.mp hm
    exact ⟨_, _, (estep_source_pc he).symm, hF, hQ, he⟩

private theorem correctionSourceWith {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) {e : Event} (he : X.get (g, index) = some e) (hLate : 173 < e.pc)
    (hEnd : e.pc < 9205) {Q : TState → Prop}
    (hInit : ∀ t, At t 7745 ((1072, b32 (g/l.block)) :: nonzeroBarrierFacts p l g) → Q t)
    (hStep : ∀ {s u event}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 → Q s →
      WStep kernel Assumptions.all l g s event u → Q u) :
    ∃ t o, t.pc = e.pc ∧ corrAddrFrame l t ∧ Q t ∧
      EStep kernel Assumptions.all l g t e o := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hWarp : 0 < warpIndex l g := by omega
  obtain ⟨_, _, hIndex, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hWarp he hLate
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, o, hs, hr⟩ := nonzeroRoleEntryPrefix hp hX (g := g) hg hWarp (by omega)
  have hPc : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hPc] at hs
  have hFrame : corrAddrFrame l s := by
    refine ⟨by rw [hs.2.1]; decide, ?_, ?_⟩
    · have hFacts := hs.2.2.2.2.2
      refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply holds_mem hFacts <;>
        simp [nonzeroBarrierFacts]
    · intro d r off hd hScope
      rw [hs.1] at hScope
      simp only [corrDefinitions, corrAddrAdds, corrCreditCounts, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with h | h | h | h | h | h | h | h | h | h <;> cases h <;> exfalso <;>
        exact (by decide : ¬ corrAddrScope _ 7745) hScope
  obtain ⟨_, hWalk⟩ := walkFromRun hr
  have hm : e ∈ (X.tr g).drop 5 := by
    apply List.mem_of_getElem? (i := index - 5)
    rw [List.getElem?_drop, Nat.add_sub_of_le hIndex]
    exact he
  exact corrAddrWalk hp hWalk (by rw [hs.1]) (by rw [hs.1]; decide) hFrame
    (hInit s hs) hStep hm hEnd

/-- A register invariant transported through the decoded correction role, from its actual
dispatch to any recorded role event. -/
theorem correctionRoleEventWith {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} (hLo : 8 ≤ warpIndex l g)
    (hHi : warpIndex l g < 12) {e : Event} (he : X.get (g,j) = some e) (hLate : 173 < e.pc)
    (hEnd : e.pc < 9205) {Q : TState → Prop}
    (hInit : ∀ t, At t 7745 ((1072, b32 (g/l.block)) :: nonzeroBarrierFacts p l g) → Q t)
    (hStep : ∀ {s u event}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 → Q s →
      WStep kernel Assumptions.all l g s event u → Q u) :
    ∃ t o, t.pc = e.pc ∧ t.sub ≤ 3 ∧ Q t ∧ EStep kernel Assumptions.all l g t e o := by
  obtain ⟨t, o, hp, hFrame, hQ, ht⟩ :=
    correctionSourceWith hp hX hLo hHi he hLate hEnd hInit hStep
  exact ⟨t, o, hp, hFrame.1, hQ, ht⟩

private theorem walkHasRun {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hw : Walk kernel Assumptions.all l g s events visits) :
    ∃ ending, Run kernel Assumptions.all l g s events ending := by
  induction hw with
  | stop => exact ⟨_,.nil _⟩
  | tau ht _ ih =>
    obtain ⟨ending,hr⟩ := ih
    cases hr with
    | nil => exact ⟨_,.nil _⟩
    | step hLocal hEvent hTail => exact ⟨ending,.step (.head ht hLocal) hEvent hTail⟩
    | last hLocal hEvent => exact ⟨none,.last (.head ht hLocal) hEvent⟩
  | ev he _ ih =>
    obtain ⟨ending,hr⟩ := ih
    exact ⟨ending,.step .refl he hr⟩
  | last he => exact ⟨none,.last .refl he⟩

private theorem corrAddrWalkAt (hp : Pre p l m) {X : Execution} {g : Nat} {s : TState}
    {events : List Event} {visits : List Visit}
    (hWalk : Walk kernel Assumptions.all l g s events visits) (hLo : 7745 ≤ s.pc)
    (hHi : s.pc ≤ 9205) (hF : corrAddrFrame l s) {Q : Nat → TState → Prop} {pos k : Nat}
    (hQ : Q pos s) (hTrace : events = (X.tr g).drop pos)
    (hStep : ∀ {s u ev position}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 →
      Q position s → WStep kernel Assumptions.all l g s ev u →
      (∀ e ∈ ev.toList, X.get (g,position) = some e) → Q (position + ev.toList.length) u)
    {target : Event} (he : events[k]? = some target) (hEnd : target.pc < 9205) :
    ∃ t o ending, t.pc = target.pc ∧ t.sub ≤ 3 ∧ Q (pos+k) t ∧
      EStep kernel Assumptions.all l g t target o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (pos+k)) ending := by
  have hEvent : ∀ (e : Event) (rest : List Event) (n : Nat),
      e :: rest = (X.tr g).drop n → X.get (g,n) = some e := by
    intro e rest n he
    change (X.tr g)[n]? = some e
    rw [show (X.tr g)[n]? = ((X.tr g).drop n)[0]? by simp, ← he]
    rfl
  induction hWalk generalizing pos k with
  | stop => simp at he
  | @tau s u events visits ht hw ih =>
    by_cases hExit : s.pc = 9205
    · exact (Nat.ne_of_lt hEnd (correctionReturnTail hExit (.tau ht hw)
        (List.mem_of_getElem? he))).elim
    have hTau : WStep kernel Assumptions.all l g s none u := .inl ⟨rfl,ht⟩
    obtain ⟨hl,hh,hF'⟩ := corrAddrStep hp hLo (by omega) hF hTau
    exact ih hl hh hF' (hStep hLo (by omega) hF.1 hQ hTau (by simp)) hTrace he
  | @ev s u ev events visits hevent hw ih =>
    cases k with
    | zero =>
      obtain rfl := Option.some.inj he
      obtain ⟨ending,hr⟩ := walkHasRun (.ev hevent hw)
      exact ⟨s,_,ending,(estep_source_pc hevent).symm,hF.1,hQ,hevent,hTrace ▸ hr⟩
    | succ k =>
      by_cases hExit : s.pc = 9205
      · exact (Nat.ne_of_lt hEnd (correctionReturnTail hExit (.ev hevent hw)
          (List.mem_of_getElem? he))).elim
      have hGo : WStep kernel Assumptions.all l g s (some ev) u := .inr ⟨_,rfl,hevent⟩
      obtain ⟨hl,hh,hF'⟩ := corrAddrStep hp hLo (by omega) hF hGo
      have hActual := hEvent _ _ _ hTrace
      have hSuffix : events = (X.tr g).drop (pos + 1) := by
        rw [← List.drop_drop, ← hTrace]
        rfl
      have hNext := hStep hLo (by omega) hF.1 hQ hGo (by
        intro e hm
        obtain rfl : e = ev := List.mem_singleton.mp hm
        exact hActual)
      have hLater : events[k]? = some target := by simpa using he
      obtain ⟨t,o,ending,hPc,hSub,hK,hE,hRun⟩ := ih hl hh hF' hNext hSuffix hLater
      have hIndex : pos+1+k = pos+(k+1) := by omega
      exact ⟨t,o,ending,hPc,hSub,hIndex ▸ hK,hE,hIndex ▸ hRun⟩
  | @last state observed hevent =>
    have hBound : k < [observed].length := (List.getElem?_eq_some_iff.mp he).1
    have hK : k = 0 := by simp only [List.length_singleton] at hBound; omega
    subst k
    obtain rfl := Option.some.inj he
    exact ⟨state,_,none,(estep_source_pc hevent).symm,hF.1,hQ,hevent,
      hTrace ▸ Run.last .refl hevent⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Replay the correction lane up to a specific actual event, retaining trace indices in the
invariant. A later visit to the same instruction cannot supply the observed state. -/
theorem correctionRoleEventAt {g index : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) {e : Event} (he : X.get (g,index) = some e) (hLate : 173 < e.pc)
    (hEnd : e.pc < 9205) {Q : Nat → TState → Prop}
    (hInit : ∀ t, At t 7745 ((1072, b32 (g/l.block)) :: nonzeroBarrierFacts p l g) → Q 5 t)
    (hStep : ∀ {s u ev position}, 7745 ≤ s.pc → s.pc < 9205 → s.sub ≤ 3 →
      Q position s → WStep kernel Assumptions.all l g s ev u →
      (∀ e ∈ ev.toList, X.get (g,position) = some e) → Q (position + ev.toList.length) u) :
    ∃ t o ending, t.pc = e.pc ∧ t.sub ≤ 3 ∧ Q index t ∧
      EStep kernel Assumptions.all l g t e o ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop index) ending := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hWarp : 0 < warpIndex l g := by omega
  obtain ⟨_, _, hIndex, _, _⟩ := nonzeroCommonPrefixOfLateEvent hp hX hg hWarp he hLate
  have hLen : index < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, o, hs, hr⟩ := nonzeroRoleEntryPrefix hp hX (g := g) hg hWarp (by omega)
  have hPc : dispatchParamPc ⟨warpIndex l g, warpIndex_lt hp g⟩ = 7745 := by
    simp only [dispatchParamPc]
    split_ifs <;> omega
  rw [hPc] at hs
  have hFrame : corrAddrFrame l s := by
    refine ⟨by rw [hs.2.1]; decide, ?_, ?_⟩
    · have hFacts := hs.2.2.2.2.2
      refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩ <;> apply holds_mem hFacts <;>
        simp [nonzeroBarrierFacts]
    · intro d r off hd hScope
      rw [hs.1] at hScope
      simp only [corrDefinitions, corrAddrAdds, corrCreditCounts, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with h | h | h | h | h | h | h | h | h | h <;> cases h <;> exfalso <;>
        exact (by decide : ¬ corrAddrScope _ 7745) hScope
  obtain ⟨_, hWalk⟩ := walkFromRun hr
  have hTarget : ((X.tr g).drop 5)[index-5]? = some e := by
    rw [List.getElem?_drop,Nat.add_sub_of_le hIndex]
    exact he
  obtain ⟨t,o,ending,hSite,hSub,hState,hFire,hRun⟩ := corrAddrWalkAt hp hWalk (by rw [hs.1])
    (by rw [hs.1]; decide) hFrame (hInit s hs) rfl hStep hTarget hEnd
  exact ⟨t,o,ending,hSite,hSub,Nat.add_sub_of_le hIndex ▸ hState,hFire,
    Nat.add_sub_of_le hIndex ▸ hRun⟩

private theorem correctionMbarSource {g index : Nat} (hWarpLo : 8 ≤ warpIndex l g)
    (hWarpHi : warpIndex l g < 12) {e : Event} (he : X.get (g, index) = some e) (hLate : 173 < e.pc)
    (hEnd : e.pc < 9205) :
    ∃ t o, t.pc = e.pc ∧ corrAddrFrame l t ∧ EStep kernel Assumptions.all l g t e o := by
  obtain ⟨t, o, hp, hF, _, ht⟩ :=
    correctionSourceWith hp hX hWarpLo hWarpHi he hLate hEnd (Q := fun _ => True)
      (by simp) (by simp)
  exact ⟨t, o, hp, hF, ht⟩

private theorem correctionIssuer {g index : Nat} {e : Event} (he : X.get (g, index) = some e)
    (hLo : 7752 ≤ e.pc) (hHi : e.pc < 9205) :
    8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
  have hHint : e.pc ∉ registerHintSites := by
    simp only [registerHintSites, List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain h | h := roleBodyPcOfEvent hp hX he (by omega) hHint
  · omega
  · split_ifs at h <;> omega

/-- The first actual correction output-acquire reads the MMA's stage-zero barrier. -/
theorem firstCorrectionWaitAddress {g index parity : Nat} {target : Loc} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨8473, .wait target parity ok acq scope⟩) :
    target = ⟨.shared, g / l.block, l.sharedBase + 144⟩ := by
  obtain ⟨hLo, hHi⟩ := correctionIssuer hp hX he
    (show 7752 ≤ 8473 by decide) (show 8473 < 9205 by decide)
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hLo hHi he
    (show 173 < 8473 by decide) (show 8473 < 9205 by decide)
  change t.pc = 8473 at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · exact Kind.noConfusion (congrArg Event.kind hFire.1)
  rw [ht, Flow.code_8473] at hc
  obtain rfl := Option.some.inj hc.symm
  have hb : t.regs 6495 = some (b32 (l.sharedBase + 144)) :=
    holds_mem hFrame.2.1 (by simp [fixedCorrections])
  exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

/-- The second output-acquire reads the MMA's stage-one barrier. -/
theorem secondCorrectionWaitAddress {g index parity : Nat} {target : Loc} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨8769, .wait target parity ok acq scope⟩) :
    target = ⟨.shared, g / l.block, l.sharedBase + 152⟩ := by
  obtain ⟨hLo, hHi⟩ := correctionIssuer hp hX he
    (show 7752 ≤ 8769 by decide) (show 8769 < 9205 by decide)
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hLo hHi he
    (show 173 < 8769 by decide) (show 8769 < 9205 by decide)
  change t.pc = 8769 at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · exact Kind.noConfusion (congrArg Event.kind hFire.1)
  rw [ht, Flow.code_8769] at hc
  obtain rfl := Option.some.inj hc.symm
  have hb := hFrame.2.2 8768 6499 152 (by decide) (by rw [ht]; decide)
  exact pollResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

omit hp hX in
/-- The correction wait's shared barrier offset. -/
def correctionWaitOffset : Nat → Nat
  | 8473 => 144
  | 8476 => 224
  | 8769 => 152
  | _ => 232

/-- The actual correction polls use the output stage completion and free objects. -/
theorem correctionWaitExactAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [8473, 8476, 8769, 8772, 9201]) :
    target = ⟨.shared, g / l.block, l.sharedBase + correctionWaitOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 173 < pc := by omega
  have hh : pc < 9205 := by omega
  obtain ⟨hWarpLo, hWarpHi⟩ := correctionIssuer hp hX he (show 7752 ≤ pc by omega) hh
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hWarpLo hWarpHi he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl
  · exact firstCorrectionWaitAddress hp hX he
  · rw [ht, Flow.code_8476] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 6497 = some (b32 (l.sharedBase + 224)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8769] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 8768 6499 152 (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8772] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7948 7131 232 (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_9201] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7948 7131 232 (by decide) (by rw [ht]; decide)
    exact pollResolvedMbarAddress hp hb
      (by unfold initializedMbarOffset; decide) hFire rfl

/-- The correction polls name initialized completion and free objects. -/
theorem correctionWaitAddress {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [8473, 8476, 8769, 8772, 9201]) :
    ∃ off ∈ [144, 152, 224, 232], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ :=
  ⟨_, (by decide : ∀ pc ∈ [8473, 8476, 8769, 8772, 9201],
    correctionWaitOffset pc ∈ [144, 152, 224, 232]) pc hSite,
    correctionWaitExactAddress hp hX he hSite⟩

/-- Every decoded correction poll uses an initialized CTA barrier. -/
theorem correctionWaitInitObject {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc ∈ [8473, 8476, 8769, 8772, 9201]) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  obtain ⟨off, hOff, rfl⟩ := correctionWaitAddress hp hX he hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  rcases hOff with rfl | rfl | rfl | rfl <;>
    apply initObjectOfOffset <;> unfold initializedMbarOffset <;> decide

omit hp hX in
/-- Byte offsets for the decoded releases on the correction branch. -/
def correctionArriveOffset (pc : Nat) : Nat :=
  if pc ∈ [7752, 8223, 8759] then 96
  else if pc ∈ [7754, 8442, 9055] then 104
  else if pc ∈ [7987, 8443, 8468] then 192
  else if pc ∈ [8224, 8464, 8764] then 200
  else if pc = 8760 then 208
  else 216

/-- Every decoded correction arrival uses the CTA barrier of its instruction. -/
theorem correctionArriveAddressExact {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [7752, 7754, 7987, 8223, 8224, 8442, 8443, 8464, 8468,
      8759, 8760, 8764, 9055, 9056]) :
    target = ⟨.shared, g / l.block, l.sharedBase + correctionArriveOffset pc⟩ := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 173 < pc := by omega
  have hh : pc < 9205 := by omega
  obtain ⟨hWarpLo, hWarpHi⟩ := correctionIssuer hp hX he (show 7752 ≤ pc by omega) hh
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hWarpLo hWarpHi he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_7752] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_7754] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_7987] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 1069 = some (b32 (l.sharedBase + 192)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8223] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7750 1614 96 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8224] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7937 1628 200 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8442] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7753 1615 104 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8443] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 1069 = some (b32 (l.sharedBase + 192)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8464] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7937 1628 200 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8468] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 1069 = some (b32 (l.sharedBase + 192)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8759] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7750 1614 96 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8760] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2390 = some (b32 (l.sharedBase + 208)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_8764] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7937 1628 200 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_9055] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb := hFrame.2.2 7753 1615 104 (by decide) (by rw [ht]; decide)
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl
  · rw [ht, Flow.code_9056] at hc
    obtain rfl := Option.some.inj hc.symm
    have hb : t.regs 2535 = some (b32 (l.sharedBase + 0)) :=
      holds_mem hFrame.2.1 (by simp [fixedCorrections])
    exact arriveResolvedMbarAddress hp hb (by unfold initializedMbarOffset; decide) hFire rfl

/-- Every decoded correction arrival uses an initialized CTA barrier. -/
theorem correctionArriveAddress {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [7752, 7754, 7987, 8223, 8224, 8442, 8443, 8464, 8468,
      8759, 8760, 8764, 9055, 9056]) :
    ∃ off ∈ [96, 104, 192, 200, 208, 216], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  refine ⟨correctionArriveOffset pc, ?_, correctionArriveAddressExact hp hX he hSite⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> decide

omit hp hX in
private theorem firesUnitCredit {l : Launch} {g pc base count : Nat} {t : TState}
    {off : Int} {dst : Option Nat} {e : Event} {o : Option TState}
    (hCount : t.regs count = some (b32 1))
    (hf : Fires pc (eventTmpl Assumptions.all l g t
      (.mbarArrive base off (.imm 0) (.reg count) false true .cta dst)) e o)
    {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (hk : e.kind = .arrive target tx n rel scope) : tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
  cases hm : mbarLoc l g t base off with
  | error f =>
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, bind, Except.bind,
      ofExec, widenMbarScope, ite_self, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok loc =>
    have hWord : readBits l g t 32 (.reg count) = .ok 1#64 :=
      readBits_b32 hCount (by decide)
    have hBytes : readBits l g t 32 (.imm 0) = .ok 0#64 := rfl
    have hScope : (Assumptions.all.any (·.clusterScopeMbar t.pc)) = false := rfl
    simp only [eventTmpl, tmaTmpl, Bool.false_eq_true, ↓reduceIte, hm, hBytes, hWord, bind,
      Except.bind, pure, Except.pure, ofExec, widenMbarScope, hScope, Fires] at hf
    rw [hf.1] at hk
    have hBoth := Kind.arrive.inj hk
    exact ⟨hBoth.2.1.symm, hBoth.2.2.1.symm, hBoth.2.2.2.1.symm, hBoth.2.2.2.2.symm⟩

/-- A correction output-ready arrival contributes one lane and zero transaction bytes. -/
theorem correctionReadyOperands {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc = 8760 ∨ pc = 9056) :
    tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta ∧
      8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
  have hl : 173 < pc := by omega
  have hh : pc < 9205 := by omega
  obtain ⟨hWarpLo, hWarpHi⟩ := correctionIssuer hp hX he (by change 7752 ≤ pc; omega) hh
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hWarpLo hWarpHi he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  have hOperands : tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
    rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
    · cases hFire.1
    rcases hSite with rfl | rfl
    · rw [ht, Flow.code_8760] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_9056] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
  exact ⟨hOperands.1, hOperands.2.1, hOperands.2.2.1, hOperands.2.2.2, hWarpLo, hWarpHi⟩

/-- The initial, rescale and final correction paths each send one unit credit
to the joint probability and rescale object of the corresponding stage. -/
theorem correctionProbabilityCredit {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [7752, 7754, 8223, 8442, 8759, 9055]) :
    tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta ∧
      8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hEnd : pc < 9205 := by omega
  obtain ⟨hWarpLo, hWarpHi⟩ := correctionIssuer hp hX he (show 7752 ≤ pc by omega) hEnd
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hWarpLo hWarpHi he
    (show 173 < pc by omega) hEnd
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  have operands : tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
    rcases out_ev hOut with ⟨_, rfl⟩ | ⟨ins, hc, rfl⟩
    · cases (congrArg Event.kind hFire.1)
    rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [ht, Flow.code_7752] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 7751 5868 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_7754] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 7751 5868 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_8223] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8222 6236 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_8442] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8441 6494 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_8759] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
    · rw [ht, Flow.code_9055] at hc
      obtain rfl := Option.some.inj hc.symm
      exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
  exact ⟨operands.1, operands.2.1, operands.2.2.1, operands.2.2.2, hWarpLo, hWarpHi⟩

/-- A correction statistics credit contributes one lane and no asynchronous bytes. -/
theorem correctionStatsCreditOperands {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [7987, 8224, 8443, 8464, 8468, 8764]) :
    tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hSite
  have hl : 173 < pc := by omega
  have hh : pc < 9205 := by omega
  obtain ⟨hWarpLo, hWarpHi⟩ := correctionIssuer hp hX he (show 7752 ≤ pc by omega) hh
  obtain ⟨t, o, ht, hFrame, hStep⟩ := correctionMbarSource hp hX hWarpLo hWarpHi he hl hh
  change t.pc = pc at ht
  obtain ⟨tm, hOut, hFire⟩ := hStep
  rcases out_ev hOut with ⟨f, rfl⟩ | ⟨ins, hc, rfl⟩
  · cases hFire.1
  rcases hSite with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ht, Flow.code_7987] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 7986 5978 0 (by decide) (by rw [ht]; decide)) hFire rfl
  · rw [ht, Flow.code_8224] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 8222 6236 0 (by decide) (by rw [ht]; decide)) hFire rfl
  · rw [ht, Flow.code_8443] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 8441 6494 0 (by decide) (by rw [ht]; decide)) hFire rfl
  · rw [ht, Flow.code_8464] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
  · rw [ht, Flow.code_8468] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl
  · rw [ht, Flow.code_8764] at hc
    obtain rfl := Option.some.inj hc.symm
    exact firesUnitCredit (hFrame.2.2 8463 6498 0 (by decide) (by rw [ht]; decide)) hFire rfl

/-- A correction statistics credit contributes one lane and no asynchronous bytes. -/
theorem correctionStatsCreditUnits {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool}
    {scope : MbarScope} (he : X.get (g,index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc ∈ [7987, 8224, 8443, 8464, 8468, 8764]) : tx = 0 ∧ n = 1 := by
  obtain ⟨hTx, hUnits, _, _⟩ := correctionStatsCreditOperands hp hX he hSite
  exact ⟨hTx, hUnits⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
