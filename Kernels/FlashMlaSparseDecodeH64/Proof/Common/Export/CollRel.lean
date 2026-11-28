-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollKey
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.WfAppend
public import Lemmas.Quiet.Progress.Released
public import Lemmas.Kernel.Progress.WarpNoBallotOp
public import Lemmas.Kernel.Progress.NextEv
public import Lemmas.Kernel.Progress.FaultExtension
public import Lemmas.Flow.NotWarpColl
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAtView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Quiet
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollClsOf
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.CollElectAt
import Lemmas.Kernel.Progress.WarpCollPairV

@[expose] public section

/-! # A released lane at a warp collective steps

`coll_quiet_steps`: a pending released lane whose next event is at a warp instruction with a
static part (`CollIns`: a shuffle with immediate lane operands, an election, a warp barrier)
steps, given the kernel's warp-collective facts `CollRel` (one `Sched.WarpCollRel` of the glued
thread machine, keyed by the warp) and that every lane has drained its selected stores. The code
has no ballot (`kernel_noBallot`; its mode vote at pc 578 is no warp collective of the count), so
the library's `Sched.warpColl_steps_relK` applies. Cancellation and undefined behaviour are
handled here: no lane is canceled, and a fault of a released lane is a step. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {e : Event}

/-- The code has no ballot instruction. -/
theorem kernel_noBallot : kernel.code.all (fun ins => !Sched.ballotOp ins.op) = true := by
  decide +kernel

/-- **The kernel's warp-collective facts** for one execution. -/
@[no_expose] def CollRel (P : Params) (L : Launch) (m : Mem0) (X : Execution) : Prop :=
  Sched.WarpCollRel m ⟨thread P L, time P L⟩ X (warpKey L) (CollAt P L)

/-- **A released pending lane at a warp collective steps**, given the kernel's collective facts
and that every lane has drained its selected stores. -/
theorem coll_steps_pend (hc : Descent.NextEnvQ L kernel Assumptions.all m X) (hp : Pre P L m)
    (hs : SafeGoal kernel Assumptions.all L m) (hFw : Follow P L X)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : CollRel P L m X)
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g) (hat : PendAtColl P L X g) :
    Sched.Steps (timed P L) m X (.thread g) := by
  have hX := hc.max.1
  obtain ⟨σ, hσ, hAt⟩ := pendAtColl_iff.1 hat
  have hlaunch := launched_all hX
  have hcl := noCanceled hX
  have hF := follow_iff.mp hFw
  have ht : Frame.Tracked (thread P L) X := fun h k hh => (hF h hh k).1
  rw [timed_eq]
  exact Sched.warpColl_steps_relK kernel_noBallot (fun hsw => warpKey_eq hsw)
    (fun _ _ => thread_sound hp) hs ht hW (by rw [hp.block]) hlaunch hcl
    (wf_appendLanes hX hd) (Sched.fault_extension hX hlaunch hc) hc.max hpd hσ hAt hrel

/-- **A released pending lane whose next event is a warp collective steps.** -/
theorem coll_quiet_steps (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hs : SafeGoal kernel Assumptions.all L m) (hFw : Follow P L X)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : CollRel P L m X)
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    (hn : Sched.NextEv L kernel Assumptions.all m X g e) (hub : ∀ f, e.kind ≠ .ub f)
    (hk : ∀ ins, kernel.code[e.pc]? = some ins → CollIns ins) :
    Sched.Steps (timed P L) m X (.thread g) := by
  obtain ⟨σ, hσ, -, -, -, hpc⟩ := next_state hp hFw hn hub
  obtain ⟨ins, hins⟩ : ∃ ins, kernel.code[e.pc]? = some ins := by
    obtain ⟨ins, h, -⟩ := next_site hp hFw hn hub
    exact ⟨ins, h⟩
  exact coll_steps_pend hc hp hs hFw hd hW hpd hrel
    (pendAtColl_iff.2 ⟨σ, hσ, ins, hpc ▸ hins, hk ins hins⟩)


/-! ## The relation itself

`coll_rel`: `CollRel` for every consistent execution that follows the role tables, by
`Sched.warpCollRel_of_pairsV`. The facts of two lanes of a warp come from the warp's
classification (`cls_of`, `warpPair_of_cls`); the static part of a collective is the
instruction's: its immediate operands for a shuffle, the full-mask election for the eight
elections (`elect_tmpl_at`). Every barrier has its participant group (`hgrp`, `bar_group`). -/

/-- The code's elections are at the eight election pcs. -/
private theorem elect_ck : kernel.code.zipIdx.all (fun x =>
    !electOp x.1.op || decide (x.2 ∈ ([16, 31, 1350, 1507, 1664, 1822, 1853, 2165] : List Nat))) =
      true := by
  decide +kernel

/-- The code's immediate static parts are full. -/
private theorem full_ck : kernel.code.all (fun ins => (opShape ins.op).all fun s =>
    match s with
    | .shfl .. => true
    | .elect mk | .warpBar mk | .vote mk => mk == 4294967295) = true := by
  decide +kernel

private theorem elect_pc {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins)
    (he : electOp ins.op = true) : ElectPc pc := by
  have hz : (ins, pc) ∈ kernel.code.zipIdx := by
    rw [List.mem_iff_getElem?]
    exact ⟨pc, by simp [List.getElem?_zipIdx, h]⟩
  have := List.all_eq_true.mp elect_ck _ hz
  simp only [he, Bool.not_true, Bool.false_or, decide_eq_true_eq, List.mem_cons,
    List.not_mem_nil, or_false] at this
  exact this

private theorem pcShape_full {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins) :
    (pcShape pc).Full := by
  have hs : pcShape pc = (opShape ins.op).getD (.elect 4294967295) := by simp [pcShape, h]
  rw [hs]
  have hi : ins ∈ kernel.code := List.mem_of_getElem? h
  have := List.all_eq_true.mp full_ck _ hi
  cases ho : opShape ins.op with
  | none => exact rfl
  | some s =>
    simp only [ho, Option.all_some] at this
    cases s <;> simp_all [Sched.CollShape.Full]

private theorem collIns_warp {ins : Instr} (h : CollIns ins) : ∃ w, ins.op = .warp w := by
  rcases h with h | h
  · cases hop : ins.op <;> simp_all [opShape]
  · cases hop : ins.op <;> simp_all [electOp]

/-- **The template of a state at a collective** is undefined behaviour or has the static part of
the state's pc. -/
private theorem tmpl_collS {σ : (thread P L g).D} (hJ : (table P L).J g σ)
    (hi : (thread P L g).inv σ) {t : TState} {ins : Instr} (hat : (thread P L g).AtD σ t)
    (hc : kernel.code[(thread P L g).pc σ]? = some ins) (hci : CollIns ins) :
    (∃ f, eventTmpl Assumptions.all L g t ins.op = .ub f) ∨
      Sched.tmplShape (eventTmpl Assumptions.all L g t ins.op) = some (collS P L g σ) := by
  cases ho : opShape ins.op with
  | some s =>
    have hS : collS P L g σ = s := by simp [collS, pcShape, hc, ho]
    rw [hS]
    exact Sched.warpOp_tmpl ho
  | none =>
    right
    have he : electOp ins.op = true := by
      rcases hci with h | h
      · simp [ho] at h
      · exact h
    have hS : collS P L g σ = .elect 4294967295 := by simp [collS, pcShape, hc, ho]
    rw [hS]
    exact elect_tmpl_at hJ hi hat hc (elect_pc hc he)

/-- **The warp collectives of the kernel**, given every barrier's participant group. -/
theorem coll_rel (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X)
    (hgrp : ∀ {g i pc id : Nat} {cnt : Option Nat} {md : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt md⟩ →
      ∃ q : Finset Nat, NamedBar.Shape L cnt q id ∧ NamedBar.Sources L X cnt q id) :
    CollRel P L m X := by
  have hF := follow_iff.mp hFw
  -- a collective event is fired from a state at a collective
  have hP : ∀ {g k : Nat} {σ : (thread P L g).D} {e : Event}, g < L.threads →
      Frame.stateAt (thread P L) X g k = some (some σ) → X.get (g, k) = some e →
      Sched.isWarpColl e = true → CollAt P L g σ := by
    intro g k σ e hg hσ he hc
    obtain ⟨A, ⟨C⟩, hAg, -⟩ := cls_of hp hX hFw hub hg
    exact C.isP hAg hσ he hc
  unfold CollRel
  refine Sched.warpCollRel_of_pairsV (M := ⟨thread P L, time P L⟩) (S := collS P L)
    (fun {g h} hg hh hk => ?_) (fun {g k d} hg hpos => ?_) (fun {g k e d} hg hσ he hc => ?_)
    (fun {g d} hg hσ hat t ins hAt hinv hins => ?_)
    (fun {g h} hs => ?_)
  · exact ⟨⟨hg, hh, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩
  · have hAt : CollAt P L g d := by
      rcases hpos.2 with ⟨e, he, hc⟩ | ⟨-, hat⟩
      · exact hP hg hpos.1 he hc
      · exact hat
    obtain ⟨ins, hins, -⟩ := hAt
    exact pcShape_full hins
  · have hAt := hP hg hσ he hc
    obtain ⟨ins, hins, hci⟩ := hAt
    have hub' : ∀ f, e.kind ≠ .ub f := fun f hf => by
      obtain ⟨pc, kd⟩ := e
      simp only at hf
      subst hf
      simp [Sched.isWarpColl] at hc
    obtain ⟨t, ins', o, hat, hi, hc', hf⟩ :=
      Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub'
    obtain rfl : ins' = ins := Option.some.inj (hc'.symm.trans hins)
    obtain ⟨s, hs1, hs2⟩ := Sched.fires_shape hf hc
    rcases tmpl_collS ((hF g hg k).2 d hσ) hi hat hins hci with ⟨f, hf'⟩ | hsh
    · rw [hf'] at hf
      simp only [Fires] at hf
      exact absurd (by rw [hf.1]) (hub' f)
    · rw [hs1] at hsh
      rw [hs2, Option.some.inj hsh]
  · obtain ⟨ins', hins', hci⟩ := hat
    obtain rfl : ins' = ins := Option.some.inj (hins'.symm.trans hins)
    obtain ⟨w, hw⟩ := collIns_warp hci
    refine ⟨by rw [hw]; rfl, ?_⟩
    have hFg := (hF g hg (X.tr g).length).2 d hσ
    exact tmpl_collS hFg hinv hAt hins hci
  · obtain ⟨A, ⟨C⟩, hAg, hall⟩ := cls_of hp hX hFw hub hs.1.1
    exact warpPair_of_cls hp hX hFw hub hgrp C hs hAg (hall _ hs)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
