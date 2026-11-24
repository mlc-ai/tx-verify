-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorProjection
public import Kernels.TmlFa4Fwd.Proof.MmaValueDescriptorWord
import Kernels.TmlFa4Fwd.Proof.MmaInitialValueCursor
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Flow PTX.Proof PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

private def valueReadyWindow (steady : Bool) : ReadyInterval :=
  let prepare := (valueDescriptorSite steady).prepare
  ⟨prepare - 3, prepare, [prepare], [2535, 7207, 7208]⟩

set_option maxRecDepth 100000 in
private theorem valueReadyWindowCode (steady : Bool) {pc : Nat} {ins : Instr}
    (hPc : (valueReadyWindow steady).inside pc) (hc : kernel.code[pc]? = some ins) :
    (valueReadyWindow steady).code pc ins = true := by
  cases steady
  · obtain ⟨hLo, hHi⟩ : 2548 ≤ pc ∧ pc < 2551 := hPc
    interval_cases pc <;>
      simp only [Flow.code_2548, Flow.code_2549, Flow.code_2550, Option.some.injEq] at hc
    all_goals subst ins; decide
  · obtain ⟨hLo, hHi⟩ : 2297 ≤ pc ∧ pc < 2300 := hPc
    interval_cases pc <;>
      simp only [Flow.code_2297, Flow.code_2298, Flow.code_2299, Option.some.injEq] at hc
    all_goals subst ins; decide

def valueSelect (e : Event) : Bool := e.pc == 2308 || e.pc == 2559

def valueReadyMark := descriptorProjection valueSelect

private theorem valueWindowErases (steady : Bool) (e : Event)
    (hi : (valueReadyWindow steady).inside e.pc) : valueReadyMark e = none := by
  have hPc : valueSelect e = false := by
    have h := hi
    cases steady
    · change 2548 ≤ e.pc ∧ e.pc < 2551 at h
      unfold valueSelect
      simp [show e.pc ≠ 2308 by omega, show e.pc ≠ 2559 by omega]
    · change 2297 ≤ e.pc ∧ e.pc < 2300 at h
      unfold valueSelect
      simp [show e.pc ≠ 2308 by omega, show e.pc ≠ 2559 by omega]
  have hNo : (List.finRange 4).any (fun i => readyHead i == e.pc) = false := by
    apply List.any_eq_false.mpr
    intro i _ h
    have he := beq_iff_eq.mp h
    rw [← he] at hi
    cases steady <;> fin_cases i <;> exact (by decide : ¬ (valueReadyWindow _).inside _ ) hi
  unfold valueReadyMark
  have hr : readyEvent e = none := by
    obtain ⟨pc, kind⟩ := e
    cases kind <;> try rfl
    case wait _ _ success _ _ =>
      cases success
      · rfl
      · simp [readyEvent, hNo]
  simp [descriptorProjection, hPc, hr]

/-- A value-ready return carries its live slot through the separate probability
wait and the fixed probability-column shuffle to the first V descriptor broadcast. -/
theorem firstValueDescriptorOfReadyWindow {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (steady : Bool) {g use : Nat} {s : TState}
    {es : List Event} {visits : List Visit}
    (hs : At s ((valueDescriptorSite steady).prepare - 3) (ringFrame l 7207 7208 use))
    (hw : Walk kernel Assumptions.all l g s es visits)
    (hFound : es.filterMap (valueReadyMark) ≠ []) :
    ∃ pre tail, ∃ recv ok,
      es = pre ++ ⟨(valueDescriptorSite steady).prepare + 8,
        .shfl .idx (b32 (valueDescriptorLow l use)) 0 31 recv ok⟩ :: tail ∧
      pre.filterMap valueReadyMark = [] ∧
      (tail = [] ∨ ∃ (u : TState) (post : List Visit),
        At u ((valueDescriptorSite steady).prepare + 9) (ringFrame l 7207 7208 use) ∧
        post.length < visits.length ∧ Walk kernel Assumptions.all l g u tail post) := by
  let r := valueReadyWindow steady
  let site := valueDescriptorSite steady
  have hBounds : 1907 ≤ r.lo ∧ r.hi ≤ 2768 := by cases steady <;> decide
  have hPc : r.inside s.pc := by
    rw [hs.1]
    cases steady <;> decide
  have hShape : RoleShape s := ⟨hs.2.1.symm ▸ Nat.zero_le _, hs.2.2.1, fun _ => hs.2.1⟩
  have hRole := holds_lookup hs.2.2.2.2 (r := 1062) (v := b32 12) rfl
  have hKeep : ∀ reg ∈ (ringFrame l 7207 7208 use).map Prod.fst, reg = 1062 ∨ reg ∈ r.keep := by
    simp [ringFrame, readyFrame, r, valueReadyWindow]
  rcases certifiedIntervalCut (valueReadyMark) r hBounds
    (valueReadyWindowCode steady) (valueWindowErases steady) hw hPc
    ⟨hShape, hRole⟩ hs.2.2.2.2 hKeep with hNil |
      ⟨t, pre, tail, steps, hSplit, hQuiet, hLength, hpₜ, hf, hFrame, hRegs, hTail⟩
  · exact (hFound hNil).elim
  have hPrep : t.pc = site.prepare := by simpa [r, site, valueReadyWindow] using hpₜ
  have hPort : At t site.prepare
      [(7207, b32 (kvSlot use)), (2535, b32 l.sharedBase), (1062, b32 12)] :=
    ⟨hPrep, hFrame.1.2.2 (by rw [hPrep]; cases steady <;> decide),
      hFrame.1.2.1, hf, hRegs.1, hRegs.2.2.1, hFrame.2, trivial⟩
  obtain ⟨v, hRun, hv⟩ := valueDescriptorLocalWithProbability hp g steady use t hPort
  have hStraight : ((kernel.code.drop site.prepare).take 6).all (fun i =>
      Epilogue.schedulerFallsThrough i.op) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hWrites : ((kernel.code.drop site.prepare).take 7).all
      (fun ins => ([7207, 7208, 2535, 1062] : List Nat).all
        (fun reg => !(writesRegs ins.op).contains reg)) = true := by
    cases steady <;> set_option maxRecDepth 100000 in kernel_rfl
  have hHeld : Holds v.regs (ringFrame l 7207 7208 use) := by
    have keep {reg : Nat} (hr : reg ∈ ([7207, 7208, 2535, 1062] : List Nat)) :
        v.regs reg = t.regs reg :=
      Epilogue.schedulerLocalFrame hWrites hStraight hRun (by omega) (by omega) hr
    exact ⟨(keep (by simp)).trans hRegs.1, (keep (by simp)).trans hRegs.2.1,
      (keep (by simp)).trans hRegs.2.2.1, (keep (by simp)).trans hRegs.2.2.2.1, trivial⟩
  have hLocal := localRun
    (show 1904 ≤ site.prepare by cases steady <;> decide)
    (show site.prepare + 7 ≤ 2768 by cases steady <;> decide)
    hPrep hStraight hRun
  have hNonempty : tail.filterMap (valueReadyMark) ≠ [] := by
    simpa [hSplit, hQuiet] using hFound
  rcases advanceWalkLocals hLocal hTail with rfl | ⟨post, hShort, _, hvWalk⟩
  · exact (hNonempty rfl).elim
  have hOut := valueProbabilityShuffle hp steady (g := g)
    (hv.mono ⟨hv.2.2.2.2.1, trivial⟩)
  cases hvWalk with
  | stop => exact (hNonempty rfl).elim
  | tau h _ => simp [Tau, hOut] at h
  | last he =>
    obtain ⟨tmpl, hT, hFire⟩ := he
    obtain rfl := Out.ev.inj (hT.symm.trans hOut)
    obtain ⟨_, _, _, hBad⟩ := hFire
    cases hBad
  | @ev v w ep es vs he hWalk =>
    have hSource := estep_source_pc he
    obtain ⟨tmpl, hT, hFire⟩ := he
    obtain rfl := Out.ev.inj (hT.symm.trans hOut)
    obtain ⟨recv, _, hEvent, hW⟩ := hFire
    obtain rfl := Option.some.inj hW
    have hProb : readyEvent ep = none := by rw [hEvent]; rfl
    have hNoMark : valueReadyMark ep = none := by
      have hPc' : ep.pc = site.prepare + 7 := hSource.trans hv.1
      cases steady <;>
        simp [valueReadyMark, descriptorProjection, valueSelect, hPc', hProb, site,
          valueDescriptorSite]
    have hLater : es.filterMap (valueReadyMark) ≠ [] := by
      simpa [hNoMark] using hNonempty
    have hPreserve : ∀ pair ∈ [(site.input, b32 (valueDescriptorLow l use))],
        pair.1 ≠ (valueProbabilityRegs steady).2 := by
      cases steady <;> simp [site, valueDescriptorSite, valueProbabilityRegs]
    have hOnly : At v (site.prepare+7) [(site.input, b32 (valueDescriptorLow l use))] :=
      hv.mono ⟨hv.2.2.2.2.2.1, trivial⟩
    have hSaved := hOnly.set (v := recv) hPreserve
    have hw : At (next (setReg v (valueProbabilityRegs steady).2 recv)) (site.prepare+8)
        [(site.input, b32 (valueDescriptorLow l use))] :=
      hSaved.mono hSaved.2.2.2.2.2
    have hDesc := valueDescriptorShuffle hp steady use (g := g) hw
    have hFrameV : At v (site.prepare + 7) (ringFrame l 7207 7208 use) := hv.mono hHeld
    have hSetV := At.set (r := (valueProbabilityRegs steady).2) (v := recv) hFrameV (by
      cases steady <;> simp [ringFrame, readyFrame, valueProbabilityRegs])
    have hFrameW : At (next (setReg v (valueProbabilityRegs steady).2 recv)) (site.prepare + 8)
        (ringFrame l 7207 7208 use) := hSetV.mono hSetV.2.2.2.2.2
    have hPrefix : (pre ++ [ep]).filterMap valueReadyMark = [] := by simp [hQuiet, hNoMark]
    cases hWalk with
    | stop => exact (hLater rfl).elim
    | tau ht _ => simp [Tau, hDesc] at ht
    | last hf =>
      obtain ⟨tm, hT, hFires⟩ := hf
      obtain rfl := Out.ev.inj (hT.symm.trans hDesc)
      obtain ⟨_, _, _, hBad⟩ := hFires
      cases hBad
    | @ev _ u e rest steps hv hWalk =>
      obtain ⟨tm, hT, hFires⟩ := hv
      obtain rfl := Out.ev.inj (hT.symm.trans hDesc)
      obtain ⟨reply, ok, hE, hU⟩ := hFires
      obtain rfl := Option.some.inj hU
      rw [hFrameW.1] at hE
      have hSet := At.set (r := site.output) (v := reply) hFrameW (by
        cases steady <;> simp [site, valueDescriptorSite, ringFrame, readyFrame])
      have hFrameNext := hSet.mono hSet.2.2.2.2.2
      refine ⟨pre ++ [ep], rest, reply, ok, ?_, hPrefix,
        .inr ⟨_, steps, hFrameNext, ?_, hWalk⟩⟩
      · simp [hSplit, hE, List.append_assoc, site]
      · simp at hShort
        omega

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
