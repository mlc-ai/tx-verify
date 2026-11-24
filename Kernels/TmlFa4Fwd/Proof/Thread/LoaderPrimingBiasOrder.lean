-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingBiasWarp
import Lemmas.Flow.ElectActor
public import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Loader

private theorem firstBiasIssueReturns {l : Launch} {g : Nat} {s u : TState}
    {addr : Nat} {spec : TensorCopy.Spec} (stage half : Fin 2)
    (he : EStep kernel Assumptions.all l g s
      ⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue addr spec⟩ (some u)) :
    u = next s := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  have hp := (estep_source_pc he).symm
  rw [hp, inputSiteCode] at hc
  obtain rfl := Option.some.inj hc.symm
  have hCopy := fires_cpTensor_copy hf rfl
  let site := inputSite (firstBiasIssueSite stage half)
  change Fires s.pc (tensorTmpl l g s (.cpTensor false false 2535 site.sharedOffset
    (.reg site.mapReg) [.reg site.colReg, .reg site.rowReg, .reg 7169]
    site.barrierReg site.barrierOffset none .tile (some (.reg site.policyReg)))) _ _ at hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf
  cases hp : cachePolicyRead l g s (some (.reg site.policyReg)) with
  | error f =>
    simp only [hp, Fires] at hf
    cases congrArg Event.kind hf.1
  | ok valid =>
    rw [hp, hCopy] at hf
    dsimp only at hf
    split_ifs at hf
    · exact Option.some.inj hf.2
    · cases congrArg Event.kind hf.1

private theorem biasLocalPastFloor {l : Launch} {g floor : Nat} {s u : TState}
    (hCode : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true)
    (hFloor : floor ≤ s.pc)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u) : floor ≤ u.pc := by
  induction hLocal with
  | refl => exact hFloor
  | @tail t v _ hTau ih =>
    obtain ⟨ins, hAt, _, hExec⟩ := Softmax.tauScoreSource hTau
    rcases hExec with ⟨rfl, _⟩ | ⟨_, _, hExec⟩
    · exact ih.trans (Nat.le_succ _)
    · rcases Softmax.scoreExecLocal hExec with hFrame | ⟨seg, hSite, hMatch, hRun⟩
      · have hMem : ins ∈ kernel.code.drop floor := by
          apply List.mem_of_getElem? (i := t.pc - floor)
          rwa [List.getElem?_drop, Nat.add_sub_of_le ih]
        have hAudit := List.all_eq_true.mp hCode ins hMem
        have hNext := hFrame.pc
        cases hop : ins.op <;> simp only [hop, nextPc, BrxTarget, or_false] at hNext
        case bra => simpa only [staysPastEvent, hop, decide_eq_true_eq, hNext] using hAudit
        case brx => simp [hop, staysPastEvent] at hAudit
        all_goals omega
      · have hAudit := List.all_eq_true.mp hSegments _ hSite
        rw [hMatch] at hAudit
        exact (Softmax.scoreSegmentFrame hRun).1.symm ▸ of_decide_eq_true hAudit

/-- An issuing loader lane passes each of its priming Bias sites at most once. -/
theorem primingBiasIssueOnceInLane {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage half : Fin 2)
    {g i j a b : Nat} {s q : TensorCopy.Spec}
    (hi : X.get (g, i) = some
      ⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue a s⟩)
    (hj : X.get (g, j) = some
      ⟨(inputSite (firstBiasIssueSite stage half)).pc, .tensorIssue b q⟩) : i = j := by
  let site := inputSite (firstBiasIssueSite stage half)
  let floor := site.pc + 1
  have hAudit : (kernel.code.drop floor).all (fun i => staysPastEvent floor i.op) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hSegments : Assumptions.swExp2Sites.all (fun atPc =>
      match cuteExp2.matchAt kernel atPc with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true := by
    fin_cases stage <;> fin_cases half <;> (set_option maxRecDepth 100000 in kernel_rfl)
  have hCannot {i j a b : Nat} {s q : TensorCopy.Spec}
      (hi : X.get (g, i) = some ⟨site.pc, .tensorIssue a s⟩)
      (hj : X.get (g, j) = some ⟨site.pc, .tensorIssue b q⟩) (hLt : i < j) : False := by
    have hg := Step.CtaBar.thread_lt_of_get hX hi
    obtain ⟨_, hRun⟩ := hX.thr g hg
    have hLen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
    obtain ⟨u, v, he, hTail⟩ := hRun.after_event hi (by omega)
    have hv := firstBiasIssueReturns stage half he
    have hFloor : floor ≤ v.pc := by
      rw [hv]
      change floor ≤ u.pc + 1
      rw [← estep_source_pc he]
    have hNextLen : i + 1 < (X.tr g).length := by omega
    let e := (X.tr g)[i + 1]
    have hNext : X.get (g, i + 1) = some e := List.getElem?_eq_getElem hNextLen
    have hHead : ((X.tr g).drop (i + 1))[0]? = some e := by
      rw [List.getElem?_drop, Nat.add_zero]
      exact hNext
    have hPc : floor ≤ e.pc := by
      generalize hEvents : (X.tr g).drop (i + 1) = es at hHead hTail
      cases hTail with
      | nil => simp at hHead
      | step hLoc hEvent _ | last hLoc hEvent =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hHead
        rw [← hHead, estep_source_pc hEvent]
        exact biasLocalPastFloor hAudit hSegments hFloor hLoc
    have hBetween := traceOrderOfPcFloor hX hAudit hSegments hj hNext
      (show site.pc < floor from Nat.lt_succ_self _) hPc
    omega
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (hCannot hi hj h).elim
  · exact h
  · exact (hCannot hj hi h).elim

/-- Distinct priming notifications from one issuing lane belong to different halves. -/
theorem primingBiasHalfDistinctOfSameIssuer {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2)
    {i j : EvId} {halfI halfJ : Fin 2} {a b : Nat} {s q : TensorCopy.Spec}
    (hSame : i.1 = j.1) (hDistinct : i ≠ j)
    (hi : X.get i = some ⟨(inputSite (firstBiasIssueSite stage halfI)).pc, .tensorIssue a s⟩)
    (hj : X.get j = some ⟨(inputSite (firstBiasIssueSite stage halfJ)).pc, .tensorIssue b q⟩) :
    halfI ≠ halfJ := by
  intro hHalf
  subst halfJ
  obtain ⟨g, i⟩ := i
  obtain ⟨h, j⟩ := j
  change g = h at hSame
  subst h
  have hPos := primingBiasIssueOnceInLane hX stage halfI hi hj
  exact hDistinct (Prod.ext rfl hPos)

/-- Before the first V packet, a Bias issue's shared half fixes its priming site. -/
theorem primingBiasSubboxPc {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {stage half : Fin 2} {pc : Nat} {spec : TensorCopy.Spec}
    (hBox : BiasSubbox p l X i stage half spec) (hPriming : pc < 780)
    (he : X.get i = some ⟨pc, .tensorIssue p.biasMapAddress spec⟩) :
    pc = (inputSite (firstBiasIssueSite stage half)).pc := by
  obtain ⟨site, rfl⟩ := actualInputIssuePc hX he
  obtain ⟨_, _, _, hDest, _, _⟩ := actualInputBoxAt hp hX site he
  have hAddress := congrArg Loc.addr (hDest.symm.trans hBox.2.2.1)
  change l.sharedBase + (inputSite site).sharedOffset =
    l.sharedBase + (166912 + 32768 * stage.val + 16384 * half.val) at hAddress
  have hOffset := Nat.add_left_cancel hAddress
  fin_cases stage <;> fin_cases half <;> fin_cases site <;>
    simp [inputSite, firstBiasIssueSite] at hPriming hOffset ⊢

/-- The two distinct priming Bias issues for a CTA and stage use different physical halves. -/
theorem primingBiasSubboxHalvesDistinct {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {stage halfI halfJ : Fin 2} {pcI pcJ : Nat} {s t : TensorCopy.Spec}
    (hCta : i.1 / l.block = j.1 / l.block) (hDistinct : i ≠ j)
    (hBoxI : BiasSubbox p l X i stage halfI s) (hBoxJ : BiasSubbox p l X j stage halfJ t)
    (hPrimingI : pcI < 780) (hPrimingJ : pcJ < 780)
    (hi : X.get i = some ⟨pcI, .tensorIssue p.biasMapAddress s⟩)
    (hj : X.get j = some ⟨pcJ, .tensorIssue p.biasMapAddress t⟩) :
    halfI ≠ halfJ := by
  obtain ⟨g, i⟩ := i
  obtain ⟨h, j⟩ := j
  have hPcI := primingBiasSubboxPc hp hX hBoxI hPrimingI hi
  have hPcJ := primingBiasSubboxPc hp hX hBoxJ hPrimingJ hj
  rw [hPcI] at hi
  rw [hPcJ] at hj
  have hLo (half : Fin 2) : 677 ≤ (inputSite (firstBiasIssueSite stage half)).pc := by
    fin_cases stage <;> fin_cases half <;> decide
  have hWarpI := primingBiasIssuerWarp hp hX (hLo halfI) (hPcI ▸ hPrimingI) hi
  have hWarpJ := primingBiasIssuerWarp hp hX (hLo halfJ) (hPcJ ▸ hPrimingJ) hj
  obtain ⟨x, instI, hElectI⟩ := primingBiasElectedIssuer hp hX stage halfI hi
  obtain ⟨y, instJ, hElectJ⟩ := primingBiasElectedIssuer hp hX stage halfJ hj
  have hSame : SameWarp l g h := ⟨⟨Step.CtaBar.thread_lt_of_get hX hi,
    Step.CtaBar.thread_lt_of_get hX hj, hCta⟩, hWarpI.trans hWarpJ.symm⟩
  have hIssuer := selected_elect_thread_unique (e := (g, x)) (f := (h, y))
    hX.elect hElectI hElectJ hSame rfl rfl
  exact primingBiasHalfDistinctOfSameIssuer hX stage (i := (g, i)) (j := (h, j))
    hIssuer hDistinct hi hj

open Protocol.Bias Thread.Scores in
/-- The successful first Bias acquire selects an observed issue for each half when its
completed generation is the loader's priming packet. -/
theorem firstBiasAcquiredPrimingHalves {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait phase : Nat} {stage : Fin 2}
    (hWait : FirstBiasAcquire l X g wait stage)
    (hPhase : FirstBiasAcquirePhase l X g wait stage phase)
    (hPriming : ∀ tensor, BiasNotifyPhase l X g stage phase tensor →
      ∃ e, X.get tensor = some e ∧ e.pc < 780) :
    ∃ tensor : Fin 2 → EvId, ∃ spec : Fin 2 → TensorCopy.Observation,
      ∀ half, BiasNotifyPhase l X g stage phase (tensor half) ∧
        AcquiredBiasBox p l X stage g wait (tensor half) half (spec half) := by
  obtain ⟨a, b, hNe, hANotify, hBNotify, ⟨halfA, oA, hA⟩, halfB, oB, hB⟩ :=
    firstBiasAcquiredPair hp hX hWait hPhase
  obtain ⟨pcA, ha⟩ := hA.issue
  obtain ⟨pcB, hb⟩ := hB.issue
  have hPC {e : EvId} {pc : Nat} {spec : TensorCopy.Spec}
      (hNot : BiasNotifyPhase l X g stage phase e)
      (hGet : X.get e = some ⟨pc, .tensorIssue p.biasMapAddress spec⟩) : pc < 780 := by
    obtain ⟨event, hE, hLt⟩ := hPriming e hNot
    rw [Option.some.inj (hE.symm.trans hGet)] at hLt
    exact hLt
  have hDiff := primingBiasSubboxHalvesDistinct hp hX (hA.owner.trans hB.owner.symm) hNe
    hA.subbox hB.subbox (hPC hANotify ha) (hPC hBNotify hb) ha hb
  refine ⟨fun half => if half = halfA then a else b,
    fun half => if half = halfA then oA else oB, ?_⟩
  intro half
  have hCover : half = halfA ∨ half = halfB := by
    fin_cases half <;> fin_cases halfA <;> fin_cases halfB <;> simp_all
  rcases hCover with rfl | rfl
  · simpa only [ite_true] using And.intro hANotify hA
  · simpa only [ite_eq_right hDiff.symm] using And.intro hBNotify hB

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
