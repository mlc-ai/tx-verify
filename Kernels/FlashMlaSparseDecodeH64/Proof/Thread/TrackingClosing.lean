-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxBarriers
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreReleaseTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0OutputVisits
import Lemmas.Step.CtaBarNamed
import Lemmas.Flow.NotClc
import Lemmas.Flow.NotBulk

@[expose] public section

/-! # Actual closing arrivals and exits -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private def closeSites : List Nat := [1835, 2160, 2330, 2585, 2604, 3610]

private theorem closing_site_pc {d : Machine.ThreadD} (hSite : ScoreClosingGate.ClosingSite d) :
    (Machine.code P L g).pc d ∈ closeSites := by
  cases d <;> simp only [ScoreClosingGate.ClosingSite] at hSite
  case idle s =>
    change s.pc ∈ closeSites
    rw [hSite]
    decide
  all_goals
    rename_i d
    change d.site.pc ∈ closeSites
    rw [hSite]
    decide

private theorem actual_gate_site {i tag : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar 12 count mode⟩) :
    tag ∈ closeSites ∧ count = none ∧ mode = .sync := by
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨rfl, h⟩ := dismissed_softmax_closing hpre hX hs he hDismiss
    exact ⟨by decide, h⟩
  · have hg := Frame.lt_of_get hX he
    obtain ⟨d, _, hd, hf⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
    obtain ⟨hSite, h⟩ := ScoreClosingGate.closing_fired hpre hf rfl
    have hp := Frame.event_pc hs hX he hd
    change tag = (Machine.code P L g).pc d at hp
    exact ⟨hp ▸ closing_site_pc hSite, h⟩

/-- Any actual arrival at the closing ID is the full-CTA sync. -/
theorem actual_gate_fields {i tag : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar 12 count mode⟩) :
    count = none ∧ mode = .sync :=
  (actual_gate_site hpre hX hs he).2

private def afterGate (pc : Nat) : Prop :=
  (1836 ≤ pc ∧ pc ≤ 1841) ∨ pc = 2161 ∨ pc = 2331 ∨ pc = 2586 ∨ pc = 2605 ∨ 3611 ≤ pc

private instance (pc : Nat) : Decidable (afterGate pc) :=
  by unfold afterGate; infer_instance

set_option maxRecDepth 100000 in
private theorem after_closed : controlRegionClosed afterGate = true := by decide +kernel

private theorem bar_callback {t u : TState} {e : Event} {id : Nat} {count : Option Nat}
    {mode : BarMode}
    (he : EStep kernel Assumptions.all L g t e (some u)) (hk : e.kind = .bar id count mode) :
    u = PTX.next t := by
  obtain ⟨ins, _, _, hf⟩ := estep_event_source he
  have ho := fires_bar_op hf hk
  cases hop : ins.op <;> simp only [hop, barOp, Bool.false_eq_true] at ho
  all_goals
    rw [hop] at hf
    simp only [eventTmpl, barTmpl] at hf
    repeat' split at hf
    all_goals first
      | exact Option.some.inj hf.2
      | (have hNone : some u = none := hf.2; cases hNone)

private theorem gate_suffix {t : TState} {seen tail : List Event} {early late : Event}
    {o : Option TState}
    (hGate : early.pc ∈ closeSites) (hKind : early.kind = .bar 12 none .sync)
    (hRun : Run kernel Assumptions.all L g t (seen ++ early :: tail) o) (hLate : late ∈ tail) :
    afterGate late.pc := by
  induction seen generalizing t with
  | nil =>
    cases hRun with
    | @step _ v _ _ _ _ _ hStep hTail =>
      have hp := estep_source_pc hStep
      have hNext := bar_callback hStep hKind
      have hRegion : afterGate ((PTX.next v).pc) := by
        change afterGate (_ + 1)
        rw [← hp]
        simp only [closeSites, List.mem_cons, List.not_mem_nil, or_false] at hGate
        rcases hGate with h | h | h | h | h | h <;> rw [h] <;> decide
      rw [hNext] at hTail
      exact run_in_control_region after_closed hRegion hTail late hLate
    | last _ _ => simp at hLate
  | cons f seen ih =>
    generalize hList : (f :: seen) ++ early :: tail = all at hRun
    cases hRun with
    | nil => simp at hList
    | step _ _ hTail =>
      obtain ⟨_, rfl⟩ := List.cons.inj hList
      exact ih hTail
    | last _ _ => simp at hList

private theorem after_actual_gate {i j tag : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hClose : X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩)
    (he : X.get (g, j) = some e) (hBefore : i < j) :
    afterGate e.pc := by
  have hg := Frame.lt_of_get hX hClose
  have hSplit := List.take_append_drop i (X.tr g)
  rw [List.drop_eq_getElem_cons (PTX.len_of_get hClose),
    (List.getElem?_eq_some_iff.mp hClose).2] at hSplit
  obtain ⟨o, hRun⟩ := hX.thr g hg
  rw [← hSplit] at hRun
  have hMem : e ∈ (X.tr g).drop (i + 1) := by
    apply List.mem_of_getElem? (i := j - (i + 1))
    simpa only [List.getElem?_drop, Nat.add_sub_of_le (Nat.succ_le_of_lt hBefore)] using
      (show (X.tr g)[j]? = some e from he)
  exact gate_suffix (actual_gate_site hpre hX hs hClose).1 rfl hRun hMem

/-- An actual closing barrier is the first use of the closing ID by that lane. -/
theorem actual_gate_ordinal {i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar 12 none .sync⟩) :
    ((X.tr g).take i).countP (Execution.isBarId 12) = 0 := by
  apply List.countP_eq_zero.mpr
  intro f hf
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hf
  have hLt := (List.getElem?_eq_some_iff.mp hj).1
  simp only [List.length_take] at hLt
  have hBefore : j < i := by omega
  rw [List.getElem?_take_of_lt hBefore] at hj
  obtain ⟨fp, fk⟩ := f
  cases fk <;> simp only [Execution.isBarId, Bool.false_eq_true, not_false_eq_true]
  case bar id count mode =>
    by_cases hId : id = 12
    · subst id
      obtain ⟨rfl, rfl⟩ := actual_gate_fields hpre hX hs hj
      have hRegion := after_actual_gate hpre hX hs hj he hBefore
      have hSite := (actual_gate_site hpre hX hs he).1
      simp only [closeSites, List.mem_cons, List.not_mem_nil, or_false] at hSite
      change afterGate tag at hRegion
      unfold afterGate at hRegion
      omega
    · simp [hId]

/-- A followed softmax wait in the loop or epilogue precedes any closing arrival of its lane. -/
theorem softmax_event_before_actual_gate {w j tag : Nat} {e : Event} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hClose : X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩) (he : X.get (g, w) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hSite : d.site.pc < 1835) : w < j := by
  have hp := Frame.event_pc hs hX he hState
  change e.pc = d.site.pc at hp
  by_contra! hLe
  rcases Nat.eq_or_lt_of_le hLe with rfl | hLt
  · obtain rfl := Option.some.inj (he.symm.trans hClose)
    have h := (actual_gate_site hpre hX hs hClose).1
    simp only [closeSites, List.mem_cons, List.not_mem_nil, or_false] at h
    change tag = d.site.pc at hp
    omega
  · have h := after_actual_gate hpre hX hs hClose he hLt
    change afterGate e.pc at h
    unfold afterGate at h
    omega

set_option maxRecDepth 100000 in
private theorem before_gate_window : stableRegisterWindow 2991 253 1835 = true := by
  decide +kernel

private theorem gate_before_softmax_tail {j start : Nat} {e : Event} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g start = some (some (.wg0 d)))
    (hLo : 253 ≤ d.site.pc) (hHi : d.site.pc < 1835)
    (he : X.get (g, j) = some e) (hTag : 1835 < e.pc) (hBefore : start ≤ j) :
    ∃ i < j, start ≤ i ∧ X.get (g, i) = some ⟨1835, .bar 12 none .sync⟩ := by
  let events := (X.tr g).drop start
  let k := j - start
  have hGet : events[k]? = some e := by
    change ((X.tr g).drop start)[j - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
    exact he
  have hMem := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hState
    (List.ne_nil_of_mem hMem)
  have hAt : (Wg0.code P L g).AtD d t := hGood.1
  have ht : t.pc = d.site.pc := hAt.1
  have hCut : events = events.take k ++ e :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hGet).1
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hCut] at hRun
  by_contra! hNone
  have hPrefix (f : Event) (hf : f ∈ events.take k) : f.pc ≠ 1835 := by
    intro hTag
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hf
    have hN : n < k :=
      lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hn).1 (by simp)
    rw [List.getElem?_take_of_lt hN] at hn
    have hEvent : X.get (g, start + n) = some f := by
      change (X.tr g)[start + n]? = some f
      simpa only [events, List.getElem?_drop] using hn
    have hLt : start + n < j := by dsimp [k] at hN; omega
    have hLen : j < (X.tr g).length := PTX.len_of_get he
    have hKind := softmax_gate_at_site hpre hX hEvent hTag (by omega)
    obtain ⟨fp, fk⟩ := f
    change fp = 1835 at hTag
    change fk = .bar 12 none .sync at hKind
    subst fp
    subst fk
    exact hNone _ hLt (Nat.le_add_right _ _) hEvent
  obtain ⟨_, _, _, hFirst, hLast, _, hLocal, hStep⟩ :=
    register_at_event_in_window before_gate_window Flow.code_1834 rfl
      (ht.symm ▸ hLo) (ht.symm ▸ hHi) hPrefix hRun
  have hRegion := local_path_in_register_window before_gate_window ⟨hFirst, hLast.le⟩ hLocal
  rw [← estep_source_pc hStep] at hRegion
  exact (not_le_of_gt hTag hRegion.2)

set_option maxRecDepth 100000 in
private theorem exit_sites : OpPcsFast kernel.code (fun op => match op with
    | .ret | .exit => true
    | _ => false) [3611] = true := by decide +kernel

theorem actual_exit_tag {j tag : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, j) = some ⟨tag, .exit⟩) : tag = 3611 := by
  rcases get_source hX he with ⟨why, hBad⟩ | ⟨t, ins, o, _, hc, hf⟩
  · cases hBad
  · have hOp : (match ins.op with | .ret | .exit => true | _ => false) = true := by
      rcases fires_exit_op hf rfl with h | h <;> rw [h]
    have hp := OpPcsFast.mem exit_sites hc hOp
    exact List.mem_singleton.mp hp

/-- Any concrete exit of a softmax lane has the first block's mask acquire in its prefix. -/
theorem first_mask_of_softmax_exit {i tag : Nat}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound) (hwg : wgOf L g = 0)
    (he : X.get (g, i) = some ⟨tag, .exit⟩) :
    ∃ start ≤ i, FirstMaskAnchor P L X g start := by
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨start, hLe, d, hSite, hBlock, hState⟩ :=
      mask_anchor_after_dismissal hpre hX hs he hDismiss
    exact ⟨start, hLe, d, hSite, hBlock, hState⟩
  · have hDone := Wg0OutputVisits.doneAtFollowedExit hX (hs g hg).machine hDismiss hwg he rfl
    obtain ⟨j, hJ, d, e, hd, hSite, hj, _⟩ :=
      Wg0OutputVisits.barrierBeforeDone hpre hX hg (hs g hg).machine hwg hDone 0
    obtain ⟨start, hLe, hAnchor⟩ :=
      first_mask_of_followed_tile_bar (PTX.len_of_get hj).le hd hSite
    exact ⟨start, hLe.trans hJ.le, hAnchor⟩

/-- The score, rescale, and output Tensor Memory load-wait sites. -/
def SoftmaxLoadWaitSite : Wg0.Site → Bool
  | .scoreWait | .rescaleWait _ | .oWait _ => true
  | _ => false

private theorem softmax_load_wait_window {site : Wg0.Site}
    (h : SoftmaxLoadWaitSite site = true) : 253 ≤ site.pc ∧ site.pc < 1835 := by
  cases site <;> simp only [SoftmaxLoadWaitSite, Bool.false_eq_true] at h
  case scoreWait => decide
  case rescaleWait t => revert t; decide
  case oWait t => revert t; decide

/-- A tracked Tensor Memory load wait precedes any actual closing arrival on its lane. -/
theorem softmax_load_wait_before_gate {w j tag wt : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hClose : X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩)
    (hw : X.get (g, w) = some ⟨wt, .tc .waitLd⟩)
    (hState : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hSite : SoftmaxLoadWaitSite d.site = true) : w < j :=
  softmax_event_before_actual_gate hpre hX hs hClose hw hState
    (softmax_load_wait_window hSite).2

/-- A lane that returns after a tracked load wait has passed the actual closing gate. -/
theorem softmax_load_wait_exit_has_gate {w j tag wt : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g w = some (some (.wg0 d)))
    (hSite : SoftmaxLoadWaitSite d.site = true)
    (hw : X.get (g, w) = some ⟨wt, .tc .waitLd⟩)
    (he : X.get (g, j) = some ⟨tag, .exit⟩) :
    ∃ i < j, X.get (g, i) = some ⟨1835, .bar 12 none .sync⟩ := by
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX hw)
  have hj := Flow.Run.end_last hRun he (Or.inr rfl)
  have hwlen : w < (X.tr g).length := PTX.len_of_get hw
  have hTag := actual_exit_tag hX he
  obtain ⟨hLo, hHi⟩ := softmax_load_wait_window hSite
  obtain ⟨p, hp, _, hGate⟩ := gate_before_softmax_tail hpre hX hs hState hLo
    hHi he (by change 1835 < tag; omega) (by omega)
  exact ⟨p, hp, hGate⟩

/-- The deallocating lane has passed its softmax closing gate and reached its first mask. -/
theorem actual_softmax_before_dealloc {i tag base n : Nat} {group : CtaGroup}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ j < i, X.get (g, j) = some ⟨1835, .bar 12 none .sync⟩ ∧
      ∃ start ≤ j, FirstMaskAnchor P L X g start := by
  have hTag := (ScoreReleaseTrace.resource_source hX he).2 base n rfl
  by_cases hd : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨start, hLe, d, hSite, hZero, hState⟩ := mask_anchor_after_dismissal hpre hX hs he hd
    obtain ⟨j, hj, hStart, hGate⟩ := gate_before_softmax_tail hpre hX hs hState
      (by rw [hSite]; decide) (by rw [hSite]; decide) he (by change 1835 < tag; omega) hLe
    exact ⟨j, hj, hGate, start, hStart, d, hSite, hZero, hState⟩
  · obtain ⟨j, bt, d, hj, hGate, hState, hSite⟩ :=
      ScoreReleaseTrace.barrier_before_dealloc_at_followed hpre hX hs hd he
    have hPc := Frame.event_pc hs hX hGate hState
    change bt = d.site.pc at hPc
    rw [hSite] at hPc
    change bt = 1835 at hPc
    subst bt
    exact ⟨j, by omega, hGate,
      first_mask_of_followed_closing (PTX.len_of_get hGate).le hState hSite⟩

/-- Any actual deallocation is behind a returned full-CTA sync. -/
theorem actual_gate_before_dealloc {i tag base n : Nat} {group : CtaGroup}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .tc (.resource group none (.dealloc base n))⟩) :
    ∃ j tag, j < i ∧ X.get (g, j) = some ⟨tag, .bar 12 none .sync⟩ := by
  obtain ⟨j, hj, hg, _⟩ := actual_softmax_before_dealloc hpre hX hs he
  exact ⟨j, 1835, hj, hg⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
