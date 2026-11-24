-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaScanCounter
public import Lemmas.Flow.Vector
public import Lemmas.Flow.EventCont
public import Lemmas.Flow.TauFrame
public import Lemmas.Flow.WarpUniform

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame

noncomputable section

def scanFrame (site : ScanSite) : List Nat :=
  [site.base, site.batch, site.sentinel, site.cta]

private def scanShflOp : WarpInstr → Bool
  | ⟨.shfl _, _, [some _], [_, _, _], some _⟩ => true
  | _ => false

private def scanBodyOp (site : ScanSite) (pc : Nat) (ins : Instr) : Bool :=
  (scanFrame site).all (fun r => !(writesRegs ins.op).contains r) &&
    (match ins.op with
    | .bra dst _ => pc < dst && dst ≤ site.compare + 2
    | .brx .. => false
    | .warp w => scanShflOp w
    | .mem a => a.kind == .load && !a.nc && a.ext == .same && a.regs.length == 1
    | op => op.isLocal)

private theorem scanBodyCode (scan : GroupScan) {pc : Nat} {ins : Instr}
    (hLo : (scanSite scan).head + 5 ≤ pc) (hHi : pc < (scanSite scan).compare + 2)
    (hc : kernel.code[pc]? = some ins) : scanBodyOp (scanSite scan) pc ins = true := by
  let site := scanSite scan
  let lo := site.head + 5
  let hi := site.compare + 2
  have hall : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all
      (fun pair => scanBodyOp site pair.2 pair.1) = true := by
    cases scan <;> set_option maxRecDepth 100000 in kernel_rfl
  apply List.all_eq_true.mp hall (ins, pc)
  have hLo' : lo ≤ pc := hLo
  have hHi' : pc < hi := hHi
  apply List.mem_of_getElem? (i := pc - lo)
  rw [List.getElem?_zipIdx, List.getElem?_take_of_lt (by omega), List.getElem?_drop,
    Nat.add_sub_of_le hLo', hc]
  rfl

private theorem scanKeepsRegs (scan : GroupScan) {pc : Nat} {ins : Instr}
    (hLo : (scanSite scan).head + 5 ≤ pc) (hHi : pc < (scanSite scan).compare + 2)
    (hc : kernel.code[pc]? = some ins) {r : Nat} (hr : r ∈ scanFrame (scanSite scan)) :
    r ∉ writesRegs ins.op := by
  have hall := scanBodyCode scan hLo hHi hc
  simp only [scanBodyOp, Bool.and_eq_true] at hall
  have := List.all_eq_true.mp hall.1 r hr
  simpa using this

/-- The scan body has no backedge before its final CTA comparison and keeps its
batch index, batch size, sentinel and CTA id. -/
theorem scanBodyTau (scan : GroupScan) {l : Launch} {g : Nat} {s u : TState}
    (hLo : (scanSite scan).head + 5 ≤ s.pc) (hHi : s.pc < (scanSite scan).compare + 2)
    (hSub : s.sub = 0) (hAcc : s.acc = [])
    (ht : Tau kernel Assumptions.all l g s u) :
    s.pc < u.pc ∧ u.pc ≤ (scanSite scan).compare + 2 ∧
      u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault ∧
      ∀ r ∈ scanFrame (scanSite scan), u.regs r = s.regs r := by
  have ht' : Tau kernel [] l g s u := by
    unfold Tau at ht ⊢
    rwa [← groupScanOut scan (by omega) (by omega)]
  obtain ⟨ins, hc⟩ := tau_core_has_code ht'
  have hCode := scanBodyCode scan hLo hHi hc
  simp only [scanBodyOp, Bool.and_eq_true] at hCode
  rcases tau_core_frame hc ht' with rfl | h
  · exact ⟨by simp [skip], by simp [skip]; omega, hSub.symm, hAcc.symm, rfl, fun _ _ => rfl⟩
  · have hPC := h.pc
    have hStep : s.pc < u.pc ∧ u.pc ≤ (scanSite scan).compare + 2 := by
      cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hPC
      case bra dst uni =>
        have hTarget : s.pc < dst ∧ dst ≤ (scanSite scan).compare + 2 := by
          simpa [hop] using hCode.2
        omega
      case brx => simp [hop] at hCode
      all_goals omega
    exact ⟨hStep.1, hStep.2, h.sub, h.acc, h.fault,
      fun r hr => h.regs r (scanKeepsRegs scan hLo hHi hc hr)⟩

private theorem scanBodyShfl {l : Launch} {g : Nat} {s u : TState} {e : Event}
    {w : WarpInstr} {regs : List Nat}
    (hShape : scanShflOp w = true)
    (hRegs : ∀ r ∈ regs, r ∉ writesRegs (.warp w))
    (hf : Fires s.pc (eventTmpl Assumptions.all l g s (.warp w)) e (some u)) :
    u.pc = s.pc + 1 ∧ u.sub = s.sub ∧ u.acc = s.acc ∧ u.fault = s.fault ∧
      ∀ r ∈ regs, u.regs r = s.regs r := by
  unfold scanShflOp at hShape
  split at hShape
  · rename_i _ mode ty dst a b c mask
    obtain ⟨_, _, _, _, _, _, rfl⟩ := fires_shfl (p := none) hf
    refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_⟩
    have hne : r ≠ dst := by simpa [writesRegs] using hRegs r hr
    exact Function.update_of_ne hne _ _
  · cases hShape

/-- Each returning body event advances, or leaves a pending memory fault.
All the loop-carried counters survive either outcome. -/
theorem scanBodyEvent (scan : GroupScan) {l : Launch} {g : Nat} {s u : TState} {e : Event}
    (hLo : (scanSite scan).head + 5 ≤ s.pc) (hHi : s.pc < (scanSite scan).compare + 2)
    (hSub : s.sub = 0) (hAcc : s.acc = [])
    (he : EStep kernel Assumptions.all l g s e (some u)) :
    (u.pc = s.pc + 1 ∧ u.fault = s.fault ∨ u.pc = s.pc ∧ u.fault.isSome) ∧
      u.sub = 0 ∧ u.acc = [] ∧ ∀ r ∈ scanFrame (scanSite scan), u.regs r = s.regs r := by
  obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
  have hCode := scanBodyCode scan hLo hHi hc
  have hRegs := fun r hr => scanKeepsRegs scan hLo hHi hc (r := r) hr
  generalize hop : i.op = op at hCode hLocal hf hRegs
  simp only [scanBodyOp, Bool.and_eq_true, hop] at hCode
  cases op <;> (try simp only [hLocal, Bool.false_eq_true] at hCode)
  case mem a =>
    have hMem : a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs.length = 1 := by
      simpa [and_assoc] using hCode.2
    obtain ⟨_, bs, _, rfl⟩ := fires_load hMem.1 hMem.2.1 hf hMem.2.2.1
    cases hRead : rebuild 3 bs with
    | error f =>
      exact ⟨.inr ⟨by simp [afterLoad, hRead], by simp [afterLoad, hRead]⟩,
        by simp [afterLoad, hRead, hSub], by simp [afterLoad, hRead, hAcc],
        by simp [afterLoad, hRead]⟩
    | ok v =>
      rw [afterLoad_last hRead (by omega)]
      have hRegsFrame := setRegs_skel s a.regs (s.acc ++ [v])
      exact ⟨.inl ⟨rfl, hRegsFrame.2.2.2⟩, rfl, rfl,
        fun r hr => setRegs_other _ _ _ _ (hRegs r hr)⟩
  case warp =>
    obtain ⟨hPc, hs, ha, hF, hR⟩ := scanBodyShfl hCode.2 hRegs hf
    exact ⟨.inl ⟨hPc, hF⟩, hs.trans hSub, ha.trans hAcc, hR⟩
  all_goals simp_all [Op.isLocal]

/-- Events counted before the scan reaches its final branch. -/
def scanBodyCount (stop : Nat) (visits : List Visit) : Nat :=
  ((visits.takeWhile (fun v => v.pc < stop)).filterMap Visit.ev).countP Event.counts

/-- A pending fault can only produce a terminal undefined-behavior event. -/
theorem countFaultedScan {l : Launch} {g : Nat} {s : TState} {es : List Event}
    {visits : List Visit} {stop : Nat} (hf : s.fault.isSome)
    (hw : Walk kernel Assumptions.all l g s es visits) : scanBodyCount stop visits ≤ 1 := by
  have ho : ∃ f, out kernel Assumptions.all l g s = .ev (.ub f) := by
    cases h : s.fault with
    | none => simp [h] at hf
    | some f => exact ⟨f, by simp [out, h]⟩
  obtain ⟨f, hOut⟩ := ho
  cases hw with
  | stop => simp [scanBodyCount]
  | tau ht _ => exact (not_tau_of_stops ⟨_, hOut⟩ ht).elim
  | ev he _ =>
    obtain ⟨m, hm, hFire⟩ := he
    have hTmpl : m = .ub f := Out.ev.inj (hm.symm.trans hOut)
    subst m
    cases hFire.2
  | @last s e he =>
    by_cases hPc : s.pc < stop
    · simpa [scanBodyCount, hPc, visit_pc, visit_ev] using
        (List.countP_le_length (p := Event.counts) (l := [e]))
    · simp [scanBodyCount, hPc, visit_pc]

end
end PTX.Kernels.TmlFa4Fwd.Mma
