-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionNamedBarrierIds
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNamedBarrierIds
public import Kernels.TmlFa4Fwd.Proof.NamedBarrierSites
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption Prologue

private def lowerStatsPc (site : Fin 3) : Nat :=
  match site with | 0 => 4398 | 1 => 7986 | _ => 7989

private def statsForward (lower : Nat) (op : Op) : Bool :=
  match op with | .bra dst _ => decide (lower ≤ dst) | .brx .. => false | _ => true

private theorem statsForwardCode (site : Fin 3) :
    (kernel.code.drop (lowerStatsPc site)).all (fun i => statsForward (lowerStatsPc site) i.op) =
      true := by
  fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem statsForwardSegments (site : Fin 3) :
    Assumptions.swExp2Sites.all (fun pc =>
      !decide (lowerStatsPc site ≤ pc) || match cuteExp2.matchAt kernel pc with
        | none => false
        | some m => decide (lowerStatsPc site ≤ m.stop)) = true := by
  fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem returnCode :
    kernel.code.all (fun i => i.op.isLocal || Epilogue.ordinaryEvent i.op) = true := by
  decide +kernel

private theorem staysAboveStats {l : Launch} {g : Nat} {s u : TState} (site : Fin 3)
    (hs : lowerStatsPc site ≤ s.pc) (ht : Tau kernel Assumptions.all l g s u) :
    lowerStatsPc site ≤ u.pc := by
  obtain ⟨i, hc, _, hStep⟩ := Softmax.tauScoreSource ht
  have hAt : (kernel.code.drop (lowerStatsPc site))[s.pc-lowerStatsPc site]? = some i := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hs]
    exact hc
  have hCode := List.all_eq_true.mp (statsForwardCode site) _ (List.mem_of_getElem? hAt)
  rcases hStep with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
  · change lowerStatsPc site ≤ s.pc+1
    omega
  · rcases Softmax.scoreExecLocal hExec with hLocal | ⟨m, hSite, hm, hRun⟩
    · have hNext := hLocal.pc
      cases ho : i.op <;> simp only [ho, nextPc, BrxTarget, or_false] at hNext
      all_goals try omega
      case bra target flag =>
        have hTarget : lowerStatsPc site ≤ target := by
          simpa only [ho, statsForward, decide_eq_true_eq] using hCode
        omega
      case brx => simp [ho, statsForward] at hCode
    · have hStop := List.all_eq_true.mp (statsForwardSegments site) _ hSite
      rw [hm] at hStop
      simp only [hs, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hStop
      rw [(Softmax.scoreSegmentFrame hRun).1]
      exact hStop

private theorem runAboveStats {l : Launch} {g : Nat} {s : TState}
    {es : List Event} {o : Option TState} (site : Fin 3) (hs : lowerStatsPc site ≤ s.pc)
    (hr : Run kernel Assumptions.all l g s es o) : ∀ e ∈ es, lowerStatsPc site ≤ e.pc := by
  have localPath {t u : TState} (ht : lowerStatsPc site ≤ t.pc)
      (hp : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
      lowerStatsPc site ≤ u.pc := by
    induction hp with
    | refl => exact ht
    | tail _ hStep ih => exact staysAboveStats site ih hStep
  induction hr with
  | nil => simp
  | step hl he _ ih =>
    have hLocal := localPath hs hl
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hMem
    · rwa [estep_source_pc he]
    · apply ih _ e hMem
      obtain ⟨i, hc, hLocal, hf⟩ := estep_event_source he
      have hOp := List.all_eq_true.mp returnCode _ (List.mem_of_getElem? hc)
      rcases callbackFrame_fires
        (Epilogue.ordinaryEventFrame (by simpa only [hLocal, Bool.false_or] using hOp)) hf
        with h | h <;> omega
  | last hl he =>
    intro e hm
    obtain rfl := List.mem_singleton.mp hm
    rw [estep_source_pc he]
    exact localPath hs hl

private theorem fromBarNext {l : Launch} {g pc id : Nat} {s u : TState}
    {count : Option Nat} {mode : BarMode}
    (he : EStep kernel Assumptions.all l g s ⟨pc, .bar id count mode⟩ (some u)) :
    u.pc = pc+1 := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  have h := fires_bar_op hf rfl
  have hPc := estep_source_pc he
  cases ho : ins.op <;> simp only [ho, barOp, Bool.false_eq_true] at h
  all_goals
    simp only [ho, eventTmpl] at hf
    unfold barTmpl at hf
    repeat' split at hf
    all_goals
      first
      | exact (congrArg TState.pc (Option.some.inj hf.2)).trans (congrArg (·+1) hPc.symm)
      | cases hf.2

private theorem laterStatsPc {l : Launch} {g : Nat} {s : TState}
    {events : List Event} {o : Option TState} (site : Fin 3)
    (hr : Run kernel Assumptions.all l g s events o) :
    ∀ (i j pc id : Nat) (cnt : Option Nat) (mode : BarMode) (e : Event),
      i < j → lowerStatsPc site ≤ pc+1 → events[i]? = some ⟨pc, .bar id cnt mode⟩ →
      events[j]? = some e → lowerStatsPc site ≤ e.pc := by
  induction hr with
  | nil => simp
  | step _ he hTail ih =>
    intro i j pc id cnt mode e hLt hFloor hi hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [hi] at he
        exact runAboveStats site ((fromBarNext he).symm ▸ hFloor) hTail
          e (List.mem_of_getElem? hj)
      | succ i =>
        simp only [List.getElem?_cons_succ] at hi
        exact ih i j pc id cnt mode e (by omega) hFloor hi hj
  | last _ _ =>
    intro i j pc id cnt mode e hLt hFloor hi hj
    have hLen := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_cons, List.length_nil] at hLen
    omega

private theorem noPriorOrdinal {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j id : Nat} {e : Event}
    (hg : g < l.threads) (he : X.get (g,j) = some e) (site : Fin 3)
    (hPc : e.pc < lowerStatsPc site)
    (hMin : ∀ i pc cnt mode, X.get (g,i) = some ⟨pc, .bar id cnt mode⟩ →
      lowerStatsPc site ≤ pc+1) :
    ((X.tr g).take j).countP (Execution.isBarId id) = 0 := by
  apply List.countP_eq_zero.mpr
  intro f hf hId
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
  have hLen := (List.getElem?_eq_some_iff.mp hi).1
  simp only [List.length_take] at hLen
  have hLt : i < j := by omega
  rw [List.getElem?_take_of_lt hLt] at hi
  obtain ⟨pc, kind⟩ := f
  cases kind <;> simp [Execution.isBarId] at hId
  case bar actual cnt mode =>
    subst actual
    obtain ⟨_, hr⟩ := hX.thr g hg
    have hAfter := laterStatsPc site hr i j pc id cnt mode e hLt (hMin i pc cnt mode hi) hi he
    omega

theorem count64StatsSites {pc : Nat} (h : pc ∈ namedBarrierSites)
    (hc : namedBarrierCount pc = some 64) :
    pc ∈ Softmax.softmaxStatsSites ∨
      ∃ stage : Fin 2, pc ∈ Correction.correctionStatsSites stage := by
  have hAll : namedBarrierSites.all (fun pc => decide (namedBarrierCount pc = some 64 →
      pc ∈ Softmax.softmaxStatsSites ∨
        ∃ stage : Fin 2, pc ∈ Correction.correctionStatsSites stage)) =
        true := by decide
  exact (of_decide_eq_true (List.all_eq_true.mp hAll pc h)) hc

theorem namedStatsRole {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i pc id : Nat} {count : Option Nat} {mode : BarMode}
    (he : X.get (g,i) = some ⟨pc, .bar id count mode⟩)
    (hSite : pc ∈ Softmax.softmaxStatsSites ∨
      ∃ stage : Fin 2, pc ∈ Correction.correctionStatsSites stage) :
    roleBodyPc (warpIndex l g) pc := by
  have hPc : 173 < pc ∧ pc ∉ registerHintSites := by
    rcases hSite with h | ⟨stage,h⟩
    · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> decide
    · fin_cases stage <;> simp [Correction.correctionStatsSites] at h <;>
        rcases h with rfl | rfl | rfl <;> decide
  exact roleBodyPcOfEvent hp hX (g := g) he hPc.1 hPc.2

/-- The first softmax statistics notification is the first event of its named barrier.
Count classification can be shared with the other statistics proofs. -/
theorem firstSoftmaxStatsOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {members : Finset Nat}
    (he : X.get (g,j) = some ⟨4397, .bar (3+warpIndex l g) (some 64) .arrive⟩)
    (hSources : NamedBar.Sources l X (some 64) members (3+warpIndex l g)) :
    ((X.tr g).take j).countP (Execution.isBarId (3+warpIndex l g)) = 0 := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hW := namedStatsRole hp hX he (.inl (by decide))
  have hw : warpIndex l g < 8 := by
    rcases hW with h | h
    · omega
    · split_ifs at h <;> omega
  refine noPriorOrdinal hX hg he 0 (by change 4397 < 4398; decide) ?_
  intro i pc cnt mode hi
  have hC := (hSources (g,i) pc cnt ⟨mode, hi⟩ hg).2
  obtain ⟨hSite, hCount, _⟩ := actualNamedBarrier hp hX hi
  have hWhich := count64StatsSites hSite (hCount.symm.trans hC)
  have hRole := namedStatsRole hp hX hi hWhich
  rcases hWhich with h | ⟨stage,h⟩
  · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
    change 4398 ≤ pc+1
    omega
  · fin_cases stage <;> simp [Correction.correctionStatsSites] at h <;>
      rcases hRole with hR | hR
    all_goals first | omega | (split_ifs at hR <;> omega)

/-- The two initial correction waits are the first events of their respective barrier IDs.
The other stage uses a disjoint identifier. -/
theorem firstCorrectionStatsOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {members : Finset Nat} (stage : Fin 2)
    (he : X.get (g,j) = some ⟨if stage.val=0 then 7985 else 7988,
      .bar (Correction.statsBarrierId l g stage) (some 64) .sync⟩)
    (hSources : NamedBar.Sources l X (some 64) members (Correction.statsBarrierId l g stage)) :
    ((X.tr g).take j).countP (Execution.isBarId (Correction.statsBarrierId l g stage)) = 0 := by
  have hg := Step.CtaBar.thread_lt_of_get hX he
  have hMembership : (if stage.val=0 then 7985 else 7988) ∈
      Correction.correctionStatsSites stage := by fin_cases stage <;> decide
  have hW := namedStatsRole hp hX he (.inr ⟨stage,hMembership⟩)
  have hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12 := by
    fin_cases stage <;>
      rcases hW with h | h <;>
      first | omega | (split_ifs at h <;> omega)
  let floor : Fin 3 := if stage.val=0 then 1 else 2
  have hFloor : (if stage.val=0 then 7985 else 7988) < lowerStatsPc floor := by
    fin_cases stage <;> decide
  refine noPriorOrdinal hX hg he floor hFloor ?_
  intro i pc cnt mode hi
  have hC := (hSources (g,i) pc cnt ⟨mode, hi⟩ hg).2
  obtain ⟨hSite, hCount, _⟩ := actualNamedBarrier hp hX hi
  have hWhich := count64StatsSites hSite (hCount.symm.trans hC)
  have hRole := namedStatsRole hp hX hi hWhich
  rcases hWhich with h | ⟨other,h⟩
  · simp only [Softmax.softmaxStatsSites, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases hRole with hR | hR
    · omega
    · split_ifs at hR <;> omega
  · have hId := Correction.actualCorrectionStatsBarrierId hp hX other h hi
    have hEq : stage = other := Fin.ext (by simp only [Correction.statsBarrierId] at hId; omega)
    subst other
    fin_cases stage <;> simp [Correction.correctionStatsSites] at h <;>
      simp [floor, lowerStatsPc] <;> omega

end PTX.Kernels.TmlFa4Fwd
