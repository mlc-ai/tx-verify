-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAddressReplay
import Kernels.TmlFa4Fwd.Flow.Code.Part088

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Thread.Scores

def biasedStatsWritten : List Nat := [637,4566,4567,4568,4569,4570,4571]

private theorem biasedStatsAddressFrame {l : Launch} {g n first : Nat} {t u : TState}
    (hFirst : 5675 ≤ first) (ht : t.pc = first) (hEnd : first+n ≤ 5682)
    (hRun : run kernel Assumptions.all l g n t = some u) :
    ∀ r, r ∉ biasedStatsWritten ∨ (5675 < first ∧ r = 637) → u.regs r = t.regs r := by
  refine fixedFrame (first := first) (stop := 5682) ?_ ?_ (by omega) (by omega) hRun
  · intro pc hLo hHi
    have hMin : 5675 ≤ pc := by omega
    interval_cases pc
    · refine ⟨_,Flow.code_5675,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · omega
    · refine ⟨_,Flow.code_5676,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
    · refine ⟨_,Flow.code_5677,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
    · refine ⟨_,Flow.code_5678,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
    · refine ⟨_,Flow.code_5679,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
    · refine ⟨_,Flow.code_5680,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
    · refine ⟨_,Flow.code_5681,rfl,rfl,fun _ => nofun,?_⟩
      rintro r (hr | ⟨hStart,rfl⟩) hm
      · exact hr (by simp_all [biasedStatsWritten,writesRegs])
      · simp [writesRegs] at hm
  · intro pc hLo hHi hm
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

private theorem biasedStatsStage {l : Launch} {g : Nat} {t u : TState} (warp : Fin 8)
    (ht : At t 5675 [(1062,b32 warp.val)])
    (hRun : run kernel Assumptions.all l g 7 t = some u) :
    u.regs 637 = some (.pred ((stageOf warp).val = 1)) := by
  have hSegment : Seg kernel Assumptions.all l g 1 5675 [(1062,b32 warp.val)]
      5676 [(637,.pred ((stageOf warp).val = 1))] := by
    fin_cases warp <;> intro t ht <;> seg_fp ht using rfl
  obtain ⟨s,hLocal,hs⟩ := hSegment.apply ht
  have hRest := hRun
  change run kernel Assumptions.all l g (1+6) t = some u at hRest
  rw [run_add,hLocal,Option.bind_some] at hRest
  exact (biasedStatsAddressFrame (by decide) hs.1 (by decide) hRest 637
    (.inr ⟨by decide,rfl⟩)).trans hs.2.2.2.2.1

/-- The real statistics events carry the biased round's rescale coefficient and preserve
the chosen reference and affine inputs for the following exponentiation. -/
theorem biasedRescalePublicationPathInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {scale : ℝ} {old candidate : Option ℝ} {ending : Option TState}
    (ht : At t 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord scale old candidate)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, At u 5684 [] ∧
      X.get (g,j) = some ⟨5682,.wr (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨5683,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending ∧
      u.regs 637 = some (.pred ((stageOf warp).val = 1)) ∧
      (∀ r ∉ biasedStatsWritten, u.regs r = t.regs r) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) u := by
  have hAddr : Seg kernel Assumptions.all l g 7 5675
      [(1062,b32 warp.val),(2535,b32 l.sharedBase)] 5682
      [(4571,b32 (statsBase l g warp))] :=
    StatisticsAddressWindow.replay hp g warp hw .biased
  obtain ⟨v,hLocal,hV⟩ := hAddr.apply (ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,trivial⟩)
  have hFrame (r : Nat) (hr : r ∉ biasedStatsWritten) : v.regs r = t.regs r :=
    biasedStatsAddressFrame (by decide) ht.1 (by decide) hLocal r (.inl hr)
  have hStage := biasedStatsStage warp (ht.mono ⟨ht.2.2.2.2.1,trivial⟩) hLocal
  have hv : At v 5682 [(4571,b32 (statsBase l g warp)),
      (1362,alphaWord scale old candidate),(5127,b32 (3+warp.val))] :=
    hV.mono ⟨hV.2.2.2.2.1,(hFrame _ (by decide)).trans ht.2.2.2.2.2.2.2.1,
      (hFrame _ (by decide)).trans ht.2.2.2.2.2.2.1,trivial⟩
  have hBytes : (alphaWord scale old candidate).bytes = 4 := by
    unfold alphaWord
    split <;> rfl
  have hMore := recordedProbabilitySuffixNonempty hRun (hAvail.imp_right (by intro h; omega))
  obtain ⟨hStore,hBar,hAfter,hPath⟩ :=
    rescaleStatsPathInPrefix hp warp true hBytes hv
      (hRun.after_local_nonempty (run_rtg hLocal) hMore) hAvail
  refine ⟨next (next v),?_,hStore,hBar,hAfter,hStage,hFrame,(TraceReach.of_local (run_rtg
    hLocal)).append hPath⟩
  exact (hv.next.next).mono trivial

theorem biasedRescalePublicationInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {scale : ℝ} {old candidate : Option ℝ} {ending : Option TState}
    (ht : At t 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord scale old candidate)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, At u 5684 [] ∧
      X.get (g,j) = some ⟨5682,.wr (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨5683,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending ∧
      u.regs 637 = some (.pred ((stageOf warp).val = 1)) ∧
      ∀ r ∉ biasedStatsWritten, u.regs r = t.regs r := by
  obtain ⟨u,hu,hStore,hBar,hTail,hStage,hKeep,_⟩ := biasedRescalePublicationPathInPrefix hp warp hw
    ht hRun hAvail
  exact ⟨u,hu,hStore,hBar,hTail,hStage,hKeep⟩

variable {p : Params} {l : Launch} {m : Mem0}

private theorem biasedPackSame {l : Launch} {g pc dst src : Nat} {t : TState} {word : Value}
    (hCode : kernel.code[pc]? = some ⟨none, .move
      ⟨.pack, .int .b 64, [some dst], [.reg src,.reg src]⟩⟩)
    (hOff : pc ∉ Assumptions.swExp2Sites) (ht : At t pc [])
    (hSrc : t.regs src = some word) (hSize : word.bytes = 4) :
    run kernel Assumptions.all l g 1 t = some (next (setReg t dst (joinValue word word))) := by
  apply run_local hCode rfl ht
  rw [Assumptions.execLocalA_all_eq_numeric,Assumptions.execLocalA_eq_nil (ht.1 ▸ hOff) rfl]
  simpa only [hSize,true_and,ite_true] using
    exec_pack (A := []) (L := l) (g := g) (d := dst) (by simp [NoPack]) hSrc hSrc SegFreePc.nil

/-- The three local instructions after the biased statistics notification prepare the
paired ABI scale and reference offset, with an explicit register frame. -/
theorem biasedShiftScaleLocal (hp : Pre p l m) {g : Nat} {t : TState} (reference : Option ℝ)
    (ht : At t 5684 []) (hReference : t.regs 4565 = some (finiteRefValue reference))
    (hNegative : t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)))
    (hScale : t.regs 7132 = some (b32 p.scaleLog2Bits)) :
    let scale := abiFloat p.scaleLog2Bits
    ∃ u, At u (shiftStart 1) [] ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      readERealPair l g u (.reg 8445) = some (.ok ((scale : EReal),(scale : EReal))) ∧
      readERealPair l g u (.reg 8444) =
        some (.ok (((- (scale*reference.getD 0) : ℝ) : EReal),
          ((- (scale*reference.getD 0) : ℝ) : EReal))) ∧
      ∀ r ∉ [4572,8444,8445], u.regs r = t.regs r := by
  let scale := abiFloat p.scaleLog2Bits
  let offset := fl (-(scale*reference.getD 0))
  let word := b32 p.scaleLog2Bits
  let v := next (setReg t 4572 offset)
  let w := next (setReg v 8444 (joinValue offset offset))
  let u := next (setReg w 8445 (joinValue word word))
  have hFinite : valFloat .f32 (finiteRefValue reference) = .ok (reference.getD 0) := by
    cases reference with
    | none =>
      change valFloat .f32 (b32 0) = .ok (0 : ℝ)
      simpa using valFloat_b32 (by decide) (by decide : f32Value 0 = some 0)
    | some x => rfl
  have hV : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local Flow.code_5684 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric]
    have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1 ▸ (by decide)
    have hModel : IdealAt Assumptions.numeric (.mul .f32) l g t :=
      idealAt_head (by decide) (Assumptions.numeric_segSites.pc hOff).tail
    unfold v offset scale
    rw [show -(abiFloat p.scaleLog2Bits*reference.getD 0) =
      reference.getD 0*(-abiFloat p.scaleLog2Bits) by ring]
    exact exec_fmul (d := 4572) hModel hReference hNegative hFinite rfl
  have hv : At v 5685 [] := (ht.set (r := 4572) (v := offset) (by simp)).mono trivial
  have hw : At w 5686 [] :=
    (hv.set (r := 8444) (v := joinValue offset offset) (by simp)).mono trivial
  have hW : run kernel Assumptions.all l g 1 v = some w :=
    biasedPackSame Flow.code_5685 (by decide) hv (by simp [v,next,setReg]) rfl
  have hU : run kernel Assumptions.all l g 1 w = some u :=
    biasedPackSame Flow.code_5686 (by decide) hw (by
      simpa only [w,v,next,setReg,Function.update_of_ne (by decide : 7132 ≠ 8444),
        Function.update_of_ne (by decide : 7132 ≠ 4572)] using hScale) rfl
  have hu : At u (shiftStart 1) [] :=
    (hw.set (r := 8445) (v := joinValue word word) (by simp)).mono trivial
  have hBits : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits) (by
    simp [Params.scalarWords])).1
  obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
  have hScaleValue : valFloat .f32 word = .ok scale := by
    simpa only [word,scale,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  have hSplit : splitValue 64 (joinValue word word) = (word,word) :=
    split_join_bits (by rw [toNat_ofNat_lt (by omega)]; exact hBits)
  have hRegScale : u.regs 8445 = some (joinValue word word) := by simp [u,next,setReg]
  have hRegOffset : u.regs 8444 = some (joinValue offset offset) := by simp [u,w,next,setReg]
  refine ⟨u,hu,run_rtg (run_comp (run_comp hV hW) hU),
    readERealPair_reg hRegScale (by rw [hSplit]; exact hScaleValue)
      (by rw [hSplit]; exact hScaleValue),
    readERealPair_reg hRegOffset rfl rfl,?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [u,w,v,next,setReg,Function.update_of_ne hr.1,
    Function.update_of_ne hr.2.1,Function.update_of_ne hr.2.2]

theorem biasedShiftScaleTraceInPrefix (hp : Pre p l m) {g : Nat} {t : TState} {events : List Event}
    {ending : Option TState} (reference : Option ℝ) (ht : At t 5684 [])
    (hReference : t.regs 4565 = some (finiteRefValue reference))
    (hNegative : t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits)))
    (hScale : t.regs 7132 = some (b32 p.scaleLog2Bits))
    (hRun : Run kernel Assumptions.all l g t events ending) (hMore : events ≠ []) :
    let scale := abiFloat p.scaleLog2Bits
    ∃ u, At u (shiftStart 1) [] ∧ Run kernel Assumptions.all l g u events ending ∧
      readERealPair l g u (.reg 8445) = some (.ok ((scale : EReal),(scale : EReal))) ∧
      readERealPair l g u (.reg 8444) =
        some (.ok (((- (scale*reference.getD 0) : ℝ) : EReal),
          ((- (scale*reference.getD 0) : ℝ) : EReal))) ∧
      ∀ r ∉ [4572,8444,8445], u.regs r = t.regs r := by
  obtain ⟨u,hu,hPath,hScalePair,hOffset,hKeep⟩ := biasedShiftScaleLocal hp (g := g) reference ht
    hReference hNegative hScale
  exact ⟨u,hu,hRun.after_local_nonempty hPath hMore,hScalePair,hOffset,hKeep⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
