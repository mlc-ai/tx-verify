-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.LoaderRingFrame
public import Lemmas.Flow.Final
public import Lemmas.Flow.UbStop

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

private structure SizeSlot where
  reg : Nat
  definePc : Nat
  lastUse : Nat

private def sizeSlots : List SizeSlot :=
  (List.range 16).map (fun k => ⟨1098 + k, 549 + 8 * k + if 8 ≤ k then 1 else 0, 902⟩) ++
  (List.range 16).map (fun k =>
    ⟨1123 + k, 1011 + 8 * k + (if 0 < k then 1 else 0) + if 8 ≤ k then 1 else 0, 1340⟩) ++
  (List.range 16).map (fun k =>
    ⟨1154 + k, 1476 + 8 * k + (if 0 < k then 1 else 0) + if 8 ≤ k then 1 else 0, 1733⟩)

private def sizeKnown (slot : SizeSlot) (pc : Nat) : Bool :=
  slot.definePc < pc && pc ≤ slot.lastUse

private def sizeWord (s : TState) (r : Nat) : Prop :=
  s.regs r = some (b32 0) ∨ s.regs r = some (b32 16)

private def sizeValues (s : TState) : Prop :=
  ∀ slot ∈ sizeSlots, sizeKnown slot s.pc = true → sizeWord s slot.reg

private def sizeSelectOp (r p : Nat) : Op :=
  .int ⟨.selp, .int .b 32, false, [some r], [.imm 16, .imm 0, .reg p]⟩

private def isSizeSelect (r : Nat) (i : Instr) : Bool :=
  match i with
  | ⟨none, .int ⟨.selp, .int .b 32, false, [some d], [.imm 16, .imm 0, .reg _]⟩⟩ => r == d
  | _ => false

private theorem isSizeSelect_code {r : Nat} {i : Instr} (h : isSizeSelect r i = true) :
    ∃ p, i = ⟨none, sizeSelectOp r p⟩ := by
  unfold isSizeSelect at h
  split at h
  · rename_i d p
    obtain rfl : r = d := beq_iff_eq.mp h
    exact ⟨p, rfl⟩
  · cases h

private theorem sizeSelect_word {l : Launch} {g r p : Nat} {s u : TState}
    (hc : kernel.code[s.pc]? = some ⟨none, sizeSelectOp r p⟩)
    (ht : Tau kernel [] l g s u) : sizeWord u r := by
  have hf : s.fault = none := by
    cases h : s.fault
    · rfl
    · simp [Tau, out, h] at ht
  have hr : execLocal l g s (sizeSelectOp r p) = .ok u := by
    unfold Tau at ht
    simp only [out, hf, hc, guardHolds, pure, Except.pure, execLocalA_nil,
      show (sizeSelectOp r p).isLocal = true from rfl, ↓reduceIte] at ht
    change (match execLocal l g s (sizeSelectOp r p) with
      | .ok t => Out.tau t | .error f => .ev (.ub f)) = .tau u at ht
    split at ht <;> simp_all
  unfold sizeSelectOp at hr
  rw [execLocal_selp rfl] at hr
  simp only [execMove] at hr
  cases h : readReg s p with
  | error f => simp [h, bind, Except.bind] at hr
  | ok v =>
    cases v <;> try simp [h, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hr
    case pred pick =>
      cases pick <;>
        simp [bind, Except.bind, readValue, readBits, DType.width, Value.bytes,
          truncBits, pure, Except.pure] at hr
      all_goals subst u; simp [sizeWord, b32, next, setReg]

private def sizeCopySite (i : Instr) (pc : Nat) : Bool :=
  match i.op with
  | .cpAsync _ _ _ _ width (.size (.reg r)) _ =>
    width == 16 && sizeSlots.any (fun slot => slot.reg == r && sizeKnown slot pc)
  | op => !bulkOp op

private theorem sizeCopySiteAudit :
    (((kernel.code.drop 174).take (1901 - 174)).zipIdx 174).all
      (fun (ins, pc) => sizeCopySite ins pc) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private def sizeFrameInstr (i : Instr) (pc : Nat) : Bool :=
  let writes := loaderRingWrites i.op
  writes.all (fun r => !(sizeSlots.any (fun slot =>
    slot.reg == r && (sizeKnown slot pc || sizeKnown slot (pc + 1)))) || isSizeSelect r i) &&
  (match i.op with
   | .bra target _ => sizeSlots.all (fun slot => !(sizeKnown slot target) || sizeKnown slot pc)
   | .brx .. => false
   | _ => true)

private theorem sizeFrameAudit :
    (((kernel.code.drop 174).take (1901 - 174)).zipIdx 174).all
      (fun (ins, pc) => sizeFrameInstr ins pc) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem sizeDefineAudit :
    sizeSlots.all (fun slot =>
      (kernel.code[slot.definePc]?).any (isSizeSelect slot.reg)) = true := by
  set_option maxRecDepth 100000 in decide +kernel

private theorem sizeLookup {pc : Nat} {ins : Instr} (hLo : 174 ≤ pc) (hHi : pc < 1901)
    (hc : kernel.code[pc]? = some ins) :
    (ins, pc) ∈ ((kernel.code.drop 174).take (1901 - 174)).zipIdx 174 := by
  apply List.mem_of_getElem? (i := pc - 174)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo, hc]
  rfl

private theorem sizeStep {l : Launch} {g : Nat} {s u : TState} {ev : Option Event}
    (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901)
    (hw : WStep kernel Assumptions.all l g s ev u) (hs : sizeValues s) :
    sizeValues u := by
  have htCore (ht : Tau kernel Assumptions.all l g s u) : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← loaderOutCore hLo (by omega)]
  have heCore {e : Event} (he : EStep kernel Assumptions.all l g s e (some u)) :
      EStep kernel [] l g s e (some u) := by
    obtain ⟨m, hm, hf⟩ := he
    exact ⟨m, by rwa [← loaderOutCore hLo (by omega)], hf⟩
  have hSource : ∃ i, kernel.code[s.pc]? = some i ∧
      (u.pc = s.pc ∨ u.pc = s.pc + 1 ∨ ∃ uni, i.op = .bra u.pc uni) := by
    rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
    · obtain ⟨ins, hc⟩ := tau_core_has_code (htCore ht)
      refine ⟨ins, hc, ?_⟩
      have hAudit := List.all_eq_true.mp sizeFrameAudit _ (sizeLookup hLo hHi hc)
      have hBranch := (Bool.and_eq_true_iff.mp hAudit).2
      rcases tau_core_frame hc (htCore ht) with rfl | hFrame
      · exact .inr (.inl rfl)
      · rcases hFrame.pc with hp | hp
        · cases hi : ins.op <;> simp_all [nextPc]
        · cases hi : ins.op <;> simp_all [sizeFrameInstr, BrxTarget]
    · obtain ⟨ins, hc, _, _⟩ := estep_event_source (heCore he)
      exact ⟨ins, hc,
        ((estep_return_pc (heCore he) (fun _ _ _ h => execLocal_frame h)).2).imp_right Or.inl⟩
  obtain ⟨ins, hc, hPc⟩ := hSource
  have hAudit := List.all_eq_true.mp sizeFrameAudit _ (sizeLookup hLo hHi hc)
  have hParts := Bool.and_eq_true_iff.mp hAudit
  intro slot hMem hNew
  have hSelected (hSel : isSizeSelect slot.reg ins = true) : sizeWord u slot.reg := by
    obtain ⟨p, rfl⟩ := isSizeSelect_code hSel
    rcases hw with ⟨_, ht⟩ | ⟨_, _, he⟩
    · exact sizeSelect_word hc (htCore ht)
    · obtain ⟨other, hOther, hLocal, _⟩ := estep_event_source (heCore he)
      rw [hc] at hOther
      obtain rfl := Option.some.inj hOther
      cases hLocal
  have hKeep (hNow : sizeKnown slot s.pc = true)
      (hNo : slot.reg ∉ loaderRingWrites ins.op) : sizeWord u slot.reg := by
    have hr := loaderPipelineStepRegs hLo hHi (r := slot.reg)
      (fun other hC => by
        obtain rfl := Option.some.inj (hc.symm.trans hC)
        exact hNo) hw
    simpa only [sizeWord, hr] using hs slot hMem hNow
  have hKeepOrSelect (hNow : sizeKnown slot s.pc = true) : sizeWord u slot.reg := by
    by_cases hWrite : slot.reg ∈ loaderRingWrites ins.op
    · have hAny : (sizeSlots.any (fun sl =>
          sl.reg == slot.reg && (sizeKnown sl s.pc || sizeKnown sl (s.pc + 1)))) = true :=
        List.any_eq_true.mpr ⟨slot, hMem, by simp [hNow]⟩
      have hTest := List.all_eq_true.mp hParts.1 slot.reg hWrite
      change !_ || isSizeSelect slot.reg ins = true at hTest
      simp only [hAny, Bool.not_true, Bool.false_or] at hTest
      exact hSelected hTest
    · exact hKeep hNow hWrite
  rcases hPc with hSame | hNext | ⟨uni, hBr⟩
  · exact hKeepOrSelect (by simpa only [hSame] using hNew)
  · by_cases hNow : sizeKnown slot s.pc = true
    · exact hKeepOrSelect hNow
    · have hDefPc : s.pc = slot.definePc := by
        simp only [hNext, sizeKnown, Bool.and_eq_true, decide_eq_true_eq] at hNew
        simp only [sizeKnown, Bool.and_eq_true, decide_eq_true_eq] at hNow
        omega
      have hDef := List.all_eq_true.mp sizeDefineAudit slot hMem
      rw [← hDefPc, hc] at hDef
      exact hSelected hDef
  · have hAcross := hParts.2
    change (match ins.op with
      | .bra target _ => sizeSlots.all (fun sl => !(sizeKnown sl target) || sizeKnown sl s.pc)
      | .brx .. => false | _ => true) = true at hAcross
    rw [hBr] at hAcross
    have hOK := List.all_eq_true.mp hAcross slot hMem
    have hNow : sizeKnown slot s.pc = true := by simpa [hNew] using hOK
    exact hKeepOrSelect hNow

private theorem copySelectorResult {l : Launch} {g dst src r : Nat} {s : TState}
    {dOff sOff : Int} {policy : Option Opnd} {spec : AsyncCopy.Spec} {o : Option TState}
    (hr : sizeWord s r)
    (hf : Fires s.pc (cpAsyncTmpl l g s (.cpAsync dst dOff src sOff 16 (.size (.reg r)) policy))
      ⟨s.pc, .copy spec⟩ o) : spec.src.size = 0 ∨ spec.src.size = 16 := by
  have hSize :
      cpAsyncSourceSize l g s 16 (.size (.reg r)) = .ok 0 ∨
      cpAsyncSourceSize l g s 16 (.size (.reg r)) = .ok 16 := by
    rcases hr with h | h
    · left
      simp only [cpAsyncSourceSize, readBits_b32' h, bind, Except.bind]
      rfl
    · right
      simp only [cpAsyncSourceSize, readBits_b32' h, bind, Except.bind]
      rfl
  unfold cpAsyncTmpl at hf
  cases hd : effAddr l g s .shared dst dOff with
  | error f => simp [hd, bind, Except.bind, ofExec, Fires] at hf
  | ok d =>
    cases ha : effAddr l g s .global src sOff with
    | error f => simp [hd, ha, bind, Except.bind, ofExec, Fires] at hf
    | ok a =>
      by_cases hAlign : d.addr % 16 = 0 ∧ a.addr % 16 = 0
      · cases hp : bulkPolicy l g s policy with
        | error f =>
          rcases hSize with h | h <;> simp [hd, ha, hAlign, h, hp, bind, Except.bind,
            ofExec, Fires] at hf
        | ok _ =>
          rcases hSize with h | h <;>
            simp [hd, ha, hAlign, h, hp, bind, Except.bind, ofExec, Fires, pure, Except.pure] at hf
          all_goals obtain ⟨rfl, _⟩ := hf
          · exact .inl rfl
          · exact .inr rfl
      · simp [hd, ha, hAlign, bind, Except.bind, ofExec, Fires, throw, throwThe,
          MonadExceptOf.throw] at hf

private theorem actualSizeEvent {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {spec : AsyncCopy.Spec} (hLo : 174 ≤ s.pc) (hHi : s.pc < 1901) (hs : sizeValues s)
    (he : EStep kernel Assumptions.all l g s e (some u)) (hCopy : e.kind = .copy spec) :
    spec.src.size = 0 ∨ spec.src.size = 16 := by
  have he' : EStep kernel [] l g s e (some u) := by
    obtain ⟨m, hm, hf⟩ := he
    exact ⟨m, by rwa [← loaderOutCore hLo (by omega)], hf⟩
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he'
  have hOp := fires_bulk_op hf hCopy
  have hSite := List.all_eq_true.mp sizeCopySiteAudit _ (sizeLookup hLo hHi hc)
  have hLabel : e = ⟨s.pc, .copy spec⟩ := by
    have hp := estep_source_pc he'
    cases e with
    | mk pc kind =>
      change pc = s.pc at hp
      change kind = .copy spec at hCopy
      subst pc kind
      rfl
  rw [hLabel] at hf
  cases hi : ins.op <;> simp only [hi, bulkOp, Bool.false_eq_true] at hOp
  case cpAsync dst dOff src sOff n source policy =>
    cases source with
    | full | ignore => simp [sizeCopySite, hi, bulkOp] at hSite
    | size opnd =>
      cases opnd <;> try simp [sizeCopySite, hi, bulkOp] at hSite
      case reg r =>
        obtain ⟨rfl, slot, hMem, hReg, hKnown⟩ := hSite
        have hRaw := hs slot hMem hKnown
        rw [hReg] at hRaw
        rw [hi] at hf
        exact copySelectorResult hRaw hf
  case cpBulk => simp [sizeCopySite, hi, bulkOp] at hSite
  case asyncStore => simp [sizeCopySite, hi, bulkOp] at hSite

private def sizeLoaderVisit (v : Visit) : Bool := 174 ≤ v.pc && v.pc < 1901

private theorem loaderSizeFromState {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit}
    (hw : Walk kernel Assumptions.all l g s es vs) (hs : sizeValues s)
    {e : Event} {sp : AsyncCopy.Spec}
    (he : e ∈ ((vs.takeWhile sizeLoaderVisit).filterMap Visit.ev))
    (hCopy : e.kind = .copy sp) : sp.src.size = 0 ∨ sp.src.size = 16 := by
  induction hw with
  | stop => simp at he
  | @last s ev hStep =>
    obtain ⟨_, _, hFires⟩ := hStep
    have hEnd := fires_none_ends hFires
    by_cases hPC : 174 ≤ s.pc ∧ s.pc < 1901
    · have heq : e = ev := by simpa [sizeLoaderVisit, visit, hPC.1, hPC.2] using he
      simp [Ends, ← heq, hCopy] at hEnd
    · simp [sizeLoaderVisit, visit, hPC] at he
  | @tau s u es vs ht hw ih =>
    by_cases hPC : 174 ≤ s.pc ∧ s.pc < 1901
    · apply ih (sizeStep hPC.1 hPC.2 (.inl ⟨rfl, ht⟩) hs)
      simpa [sizeLoaderVisit, visit, hPC.1, hPC.2] using he
    · simp [sizeLoaderVisit, visit, hPC] at he
  | @ev s u e' es vs hStep hw ih =>
    by_cases hPC : 174 ≤ s.pc ∧ s.pc < 1901
    · simp [sizeLoaderVisit, visit, hPC.1, hPC.2] at he
      rcases he with rfl | hTail
      · exact actualSizeEvent hPC.1 hPC.2 hs hStep hCopy
      · exact ih (sizeStep hPC.1 hPC.2 (.inr ⟨_, rfl, hStep⟩) hs) (List.mem_filterMap.mpr hTail)
    · simp [sizeLoaderVisit, visit, hPC] at he

private theorem sizeDispatchAudit : sizeSlots.all (fun slot => !sizeKnown slot 174) = true :=
  by decide +kernel

/-- An actual loader prefix from the role split issues either a full BF16 vector
read or a zero-byte padding read, including every warm and steady ring packet. -/
theorem loaderCopyReadSize {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {vs : List Visit} (hw : Walk kernel Assumptions.all l g s es vs)
    (hPc : s.pc = 174) {e : Event} {sp : AsyncCopy.Spec}
    (he : e ∈ ((vs.takeWhile (fun v => 174 ≤ v.pc && v.pc < 1901)).filterMap Visit.ev))
    (hCopy : e.kind = .copy sp) : sp.src.size = 0 ∨ sp.src.size = 16 := by
  have hSize : sizeValues s := by
    intro slot hm hk
    have hMissing := List.all_eq_true.mp sizeDispatchAudit slot hm
    rw [hPc] at hk
    rw [hk] at hMissing
    cases hMissing
  exact loaderSizeFromState hw hSize he hCopy

end
end PTX.Kernels.TmlFa4Fwd.Loader
