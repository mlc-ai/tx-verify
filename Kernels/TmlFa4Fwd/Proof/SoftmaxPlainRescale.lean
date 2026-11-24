-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainMaximum
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAddressReplay
import Kernels.TmlFa4Fwd.Flow.Code.Part107
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Thread.Scores

def plainStatsWritten : List Nat := [5515,5516,5517,5518]

private theorem plainStatsFrame {l : Launch} {g : Nat} {t u : TState}
    (ht : t.pc = 6886) (hRun : run kernel Assumptions.all l g 4 t = some u) :
    ∀ r ∉ plainStatsWritten, u.regs r = t.regs r := by
  refine fixedFrame (first := 6886) (stop := 6890) ?_ ?_ (by omega) (by omega) hRun
  · intro pc hLo hHi
    interval_cases pc
    · refine ⟨_,Flow.code_6886,rfl,rfl,fun _ => nofun,?_⟩
      intro r hr hm
      exact hr (by simp_all [plainStatsWritten,writesRegs])
    · refine ⟨_,Flow.code_6887,rfl,rfl,fun _ => nofun,?_⟩
      intro r hr hm
      exact hr (by simp_all [plainStatsWritten,writesRegs])
    · refine ⟨_,Flow.code_6888,rfl,rfl,fun _ => nofun,?_⟩
      intro r hr hm
      exact hr (by simp_all [plainStatsWritten,writesRegs])
    · refine ⟨_,Flow.code_6889,rfl,rfl,fun _ => nofun,?_⟩
      intro r hr hm
      exact hr (by simp_all [plainStatsWritten,writesRegs])
  · intro pc hLo hHi hm
    simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
    omega

/-- The actual plain statistics store publishes the reference's correction word. -/
theorem plainRescalePublicationPathInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {scale : ℝ} {old candidate : Option ℝ} {ending : Option TState}
    (ht : At t 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),(1492,alphaWord scale old candidate)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, At u 6892 [] ∧
      X.get (g,j) = some ⟨6890,.wr (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨6891,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending ∧
      (∀ r ∉ plainStatsWritten, u.regs r = t.regs r) ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) u := by
  have hAddr : Seg kernel Assumptions.all l g 4 6886
      [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),(2535,b32 l.sharedBase)] 6890
      [(5518,b32 (statsBase l g warp))] :=
    StatisticsAddressWindow.replay hp g warp hw .plain
  obtain ⟨a,b,c,d,e,_⟩ := ht.2.2.2.2
  obtain ⟨v,hLocal,hV⟩ := hAddr.apply (ht.mono ⟨a,b,c,trivial⟩)
  have hFrame := plainStatsFrame ht.1 hLocal
  have hv : At v 6890 [(5518,b32 (statsBase l g warp)),
      (1492,alphaWord scale old candidate),(5127,b32 (3+warp.val))] :=
    hV.mono ⟨hV.2.2.2.2.1,(hFrame _ (by decide)).trans e,(hFrame _ (by decide)).trans d,trivial⟩
  have hBytes : (alphaWord scale old candidate).bytes = 4 := by
    unfold alphaWord
    split <;> rfl
  have hMore := recordedProbabilitySuffixNonempty hRun (hAvail.imp_right (by intro h; omega))
  obtain ⟨hStore,hBar,hAfter,hPath⟩ :=
    rescaleStatsPathInPrefix hp warp false hBytes hv
      (hRun.after_local_nonempty (run_rtg hLocal) hMore) hAvail
  exact ⟨next (next v),(hv.next.next).mono trivial,hStore,hBar,hAfter,hFrame,(TraceReach.of_local
    (run_rtg hLocal)).append hPath⟩

theorem plainRescalePublicationInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j : Nat} (hw : warp.val = warpIndex l g)
    {t : TState} {scale : ℝ} {old candidate : Option ℝ} {ending : Option TState}
    (ht : At t 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),(1492,alphaWord scale old candidate)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hAvail : ending = none ∨ j+1 < (X.tr g).length) :
    ∃ u, At u 6892 [] ∧
      X.get (g,j) = some ⟨6890,.wr (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨6891,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j+2)) ending ∧
      ∀ r ∉ plainStatsWritten, u.regs r = t.regs r := by
  obtain ⟨u,hu,hStore,hBar,hTail,hKeep,_⟩ := plainRescalePublicationPathInPrefix hp warp hw ht
    hRun hAvail
  exact ⟨u,hu,hStore,hBar,hTail,hKeep⟩

/-- The two instructions after the plain statistics notice supply the paired offset. -/
theorem plainShiftOffsetLocal {l : Launch} {g : Nat} {t : TState}
    (reference : Option ℝ) (scale : ℝ) (ht : At t 6892 [])
    (hReference : t.regs 5514 = some (finiteRefValue reference))
    (hNegative : t.regs 1230 = some (fl (-scale))) :
    ∃ u, At u (shiftStart 2) [] ∧ Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      readERealPair l g u (.reg 8691) =
        some (.ok (((-(scale*reference.getD 0) : ℝ) : EReal),
          ((-(scale*reference.getD 0) : ℝ) : EReal))) ∧
      ∀ r ∉ [5519,8691], u.regs r = t.regs r := by
  let offset := fl (-(scale*reference.getD 0))
  let v := next (setReg t 5519 offset)
  let u := next (setReg v 8691 (joinValue offset offset))
  have hFinite : valFloat .f32 (finiteRefValue reference) = .ok (reference.getD 0) := by
    cases reference with
    | none =>
      change valFloat .f32 (b32 0) = .ok (0 : ℝ)
      simpa using valFloat_b32 (by decide) (by decide : f32Value 0 = some 0)
    | some x => rfl
  have hV : run kernel Assumptions.all l g 1 t = some v := by
    apply run_local Flow.code_6892 rfl ht
    rw [Assumptions.execLocalA_all_eq_numeric]
    have hOff : t.pc ∉ Assumptions.swExp2Sites := ht.1 ▸ (by decide)
    have hModel : IdealAt Assumptions.numeric (.mul .f32) l g t :=
      idealAt_head (by decide) (Assumptions.numeric_segSites.pc hOff).tail
    unfold v offset
    rw [show -(scale*reference.getD 0) = reference.getD 0*(-scale) by ring]
    exact exec_fmul (d := 5519) hModel hReference hNegative hFinite rfl
  have hv : At v 6893 [] := (ht.set (r := 5519) (v := offset) (by simp)).mono trivial
  have hU : run kernel Assumptions.all l g 1 v = some u := by
    apply run_local Flow.code_6893 rfl hv
    rw [Assumptions.execLocalA_all_eq_numeric,
      Assumptions.execLocalA_eq_nil (hv.1 ▸ (by decide : 6893 ∉ Assumptions.swExp2Sites)) rfl]
    have hOffReg : v.regs 5519 = some offset := by simp [v,next,setReg]
    exact exec_pack (A := []) (L := l) (g := g) (d := 8691) (by simp [NoPack])
      hOffReg hOffReg SegFreePc.nil
  have hu : At u (shiftStart 2) [] :=
    (hv.set (r := 8691) (v := joinValue offset offset) (by simp)).mono trivial
  have hReg : u.regs 8691 = some (joinValue offset offset) := by simp [u,next,setReg]
  refine ⟨u,hu,run_rtg (run_comp hV hU),
   readERealPair_reg hReg rfl rfl,?_⟩
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
  simp only [u,v,next,setReg,Function.update_of_ne hr.1,Function.update_of_ne hr.2]

theorem plainShiftOffsetTraceInPrefix {l : Launch} {g : Nat} {t : TState} {events : List Event}
    {ending : Option TState}
    (reference : Option ℝ) (scale : ℝ) (ht : At t 6892 [])
    (hReference : t.regs 5514 = some (finiteRefValue reference))
    (hNegative : t.regs 1230 = some (fl (-scale)))
    (hRun : Run kernel Assumptions.all l g t events ending) (hMore : events ≠ []) :
    ∃ u, At u (shiftStart 2) [] ∧ Run kernel Assumptions.all l g u events ending ∧
      readERealPair l g u (.reg 8691) =
        some (.ok (((-(scale*reference.getD 0) : ℝ) : EReal),
          ((-(scale*reference.getD 0) : ℝ) : EReal))) ∧
      ∀ r ∉ [5519,8691], u.regs r = t.regs r := by
  obtain ⟨u,hu,hPath,hOffset,hKeep⟩ := plainShiftOffsetLocal (l := l) (g := g) reference scale ht
    hReference hNegative
  exact ⟨u,hu,hRun.after_local_nonempty hPath hMore,hOffset,hKeep⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
