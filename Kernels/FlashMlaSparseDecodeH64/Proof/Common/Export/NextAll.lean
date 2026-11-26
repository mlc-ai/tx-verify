-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.CollRel
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.VoteRel
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarInit
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Quiet.Progress.Released
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RestAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.PendAtView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.NextLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.StepPlumb
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CollPcs
import Lemmas.Quiet.Kernel.NextInOrder
import Lemmas.Quiet.Kernel.FrameTrackedU

@[expose] public section

/-! # A released lane steps, or has a next event

`next_all`: a pending released lane of a maximal execution of a safe launch steps, or its trace
extends consistently by an event that is no undefined behaviour (`Sched.NextEv`). The lane's
machine state is taken privately from `Follow` (`Frame.Tracked`); by the class of its instruction:

* outside `Descent.NextKind.Rest`, a register request, the allocation, a non-coherent load or a
  Tensor Memory store: the library's step (`ordinary_at`, `reg_at`, `alloc_at`, `other_at`);
* a warp collective or the vote of warpgroup 0 (pc 578): the step of the kernel's warp facts
  (`coll_steps_pend`, `vote_steps_pend`), a collective needing its warp's other lanes;
* an mbarrier poll (the code's sixteen waits): it polls an object of the lane's CTA
  (`<role>_loc`) with a final state, which the caller gives once the lane has passed barrier 0;
  a ready poll is a step (`Step.poll_counted_extension`) and a failed poll is the next event;
* undefined behaviour of the instruction's template: a step, the fault is performed. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MBarrier AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- `trap`, whose template is undefined behaviour. -/
private def isTrap : Op → Bool
  | .trap => true
  | _ => false

/-- A check of the whole code, as a statement about each pc. -/
private theorem at_all {F : Nat → Instr → Bool}
    (hall : kernel.code.zipIdx.all (fun x => F x.2 x.1) = true) {pc : Nat} {ins : Instr}
    (h : kernel.code[pc]? = some ins) : F pc ins = true := by
  have hm : (ins, pc) ∈ kernel.code.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using h
  exact List.all_eq_true.mp hall _ hm

/-- A warp instruction is a collective with a static part or the vote. -/
private def warpOk (pc : Nat) (ins : Instr) : Bool :=
  Descent.opKind ins.op != .warp || collInsB ins || pc == 578

/-- An instruction of the kind `other` is local, `trap`, or has a library step. -/
private def otherOk (_pc : Nat) (ins : Instr) : Bool :=
  Descent.opKind ins.op != .other || ins.op.isLocal || isTrap ins.op || Descent.otherOp ins.op ||
    Sched.tcStoreOp ins.op

/-- A register request, an allocation, a wait: of the library's shape. -/
private def restOk (pc : Nat) (ins : Instr) : Bool :=
  (Descent.opKind ins.op != .reg || Sched.regOp ins.op) &&
  (Descent.opKind ins.op != .alloc || Sched.allocOp ins.op) &&
  (Descent.opKind ins.op != .wait || (Sched.waitOp ins.op &&
    [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534, 2644, 2677,
      2684].contains pc))

private theorem warpOk_all : kernel.code.zipIdx.all (fun x => warpOk x.2 x.1) = true := by
  decide +kernel

private theorem otherOk_all : kernel.code.zipIdx.all (fun x => otherOk x.2 x.1) = true := by
  decide +kernel

private theorem restOk_all : kernel.code.zipIdx.all (fun x => restOk x.2 x.1) = true := by
  decide +kernel

private theorem kinds_warp {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins)
    (hk : Descent.opKind ins.op = .warp) : CollIns ins ∨ pc = 578 := by
  have := at_all warpOk_all h
  simp only [warpOk, hk, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with h1 | h1
  · exact .inl (by simpa [collInsB, CollIns] using h1)
  · exact .inr h1

private theorem kinds_other {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins)
    (hk : Descent.opKind ins.op = .other) (hl : ins.op.isLocal = false) :
    isTrap ins.op = true ∨ (Descent.otherOp ins.op || Sched.tcStoreOp ins.op) = true := by
  have := at_all otherOk_all h
  simp only [otherOk, hk, hl, bne_self_eq_false, Bool.false_or, Bool.or_eq_true] at this
  rcases this with (h1 | h1) | h1
  · exact .inl h1
  · exact .inr (by simp [h1])
  · exact .inr (by simp [h1])

private theorem kinds_reg {pc : Nat} {ins : Instr} (h : kernel.code[pc]? = some ins)
    (hk : Descent.opKind ins.op = .reg) : Sched.regOp ins.op = true := by
  have := (at_all restOk_all h)
  simp only [restOk, hk, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at this
  simpa [hk] using this

/-- The waits of the code are at the pcs of the roles' polls. -/
private theorem site_roles {pc : Nat}
    (h : pc ∈ [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234, 2245, 2446, 2534, 2644,
      2677, 2684]) :
    (103 ≤ pc ∧ pc < 1842) ∨ (1853 ≤ pc ∧ pc ≤ 2160) ∨ (2162 ≤ pc ∧ pc < 2332) ∨
      (2332 ≤ pc ∧ pc < 2587) ∨ (2606 ≤ pc ∧ pc ≤ 3610) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

/-- A lane past pc 97 has passed barrier 0. -/
private theorem pend_bar0
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hJ : (table P L).J g σ) (hi : (thread P L g).inv σ)
    (hpc : 97 < (thread P L g).pc σ) : 0 < (X.tr g).countP isBar0 := by
  obtain ⟨s, n⟩ := σ
  have hb : n .bar0 = ((X.tr g).take (X.tr g).length).countP isBar0 := state_count hσ .bar0
  have h := state_role hJ hi
  rw [List.take_length] at hb
  rcases s with d | ⟨i | r, d'⟩
  · cases h
    omega
  · have hJ' : 1 ≤ n .bar0 := by cases i <;> exact hJ.1
    omega
  · exact hJ.elim

/-- **A released pending lane at a poll steps, or its next event is the failed poll.** -/
private theorem poll_at
    (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hfin : ∀ f : MbarFam, 0 < (X.tr g).countP isBar0 →
      ∃ st, MBarrier.stateBefore (X.objects (MbarRow.loc L g f))
        (X.objects (MbarRow.loc L g f)).length = some st)
    (hJ : (table P L).J g σ) {t t1 : TState} {ins : Instr}
    (hrun : Run kernel Assumptions.all L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t t1)
    (hat : (thread P L g).AtD σ t1) (hi : (thread P L g).inv σ)
    (hins : kernel.code[(thread P L g).pc σ]? = some ins)
    (hout : out kernel Assumptions.all L g t1 = .ev (eventTmpl Assumptions.all L g t1 ins.op))
    (hw : Sched.waitOp ins.op = true)
    (hsite : (thread P L g).pc σ ∈ [264, 272, 1184, 1931, 1983, 2012, 2107, 2205, 2209, 2234,
      2245, 2446, 2534, 2644, 2677, 2684]) :
    Sched.Steps (timed P L) m X (.thread g) ∨
      ∃ e, Sched.NextEv L kernel Assumptions.all m X g e ∧ ∀ f, e.kind ≠ .ub f := by
  have hX := hc.max.1
  have hne : X.tr g ≠ [] := ne_nil hσ (Q := fun i => Sched.waitOp i.op = true)
    (fun i hi' hq => by
      have : kernel.code[6]?.map (fun i => Sched.waitOp i.op) = some false := by decide +kernel
      rw [hi'] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this] at hq
      cases hq)
    (fun i hi' => by rw [hins] at hi'; cases hi'; exact hw)
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [Sched.waitOp, Bool.false_eq_true] at hw
  rename_i pr b off par acq sc0
  subst hw
  have hpc : t1.pc = (thread P L g).pc σ := hat.1
  rcases eventTmpl_mbarWait_cases (A := Assumptions.all) (L := L) (g := g) (t := t1) (p := pr)
    (b := b) (off := off) (par := par) (acq := true) (sc := sc0) with
    ⟨f, hf⟩ | ⟨l, q, k, sc, hq2, htm⟩
  · rw [hf] at hout
    exact .inl (.inl (Sched.fault_extension hX (launched_all hX) hc hpd.1 hrel hrun hl hout))
  have hfire : ∀ ok, Fires ((thread P L g).pc σ)
      (eventTmpl Assumptions.all L g t1 (.mbarWait pr b off par true sc0))
      ⟨(thread P L g).pc σ, .wait l q ok true sc⟩ (some (k ok)) := fun ok => by
    rw [htm]; exact ⟨ok, rfl, rfl⟩
  have hev : (table P L).Ev g σ ⟨(thread P L g).pc σ, .wait l q true true sc⟩ :=
    (shapeOk hp (fun _ => True)).shape g trivial σ t1 _ _ _ hJ hat hi hins (hfire true)
  have hnu := hc.noUb
  obtain ⟨f, rfl⟩ : ∃ f, l = MbarRow.loc L g f := by
    rcases site_roles hsite with h | h | h | h | h
    · exact wg0_loc hp hX hFw hnu hσ hJ hi hev rfl h rfl
    · exact mma_loc hp hnu hσ hJ hi hev rfl h rfl
    · exact tma_loc hp hnu hσ hJ hi hev rfl h rfl
    · exact index_loc hp hJ hi hev rfl h rfl
    · exact dequant_loc hp hJ hi hev rfl h rfl
  have h97 : 97 < (thread P L g).pc σ := by
    rcases site_roles hsite with h | h | h | h | h <;> omega
  obtain ⟨before, hstate⟩ := hfin f (pend_bar0 hσ hJ hi h97)
  have hasm : ∀ (ok : Bool) {sc' : MbarScope}, ∀ a ∈ Assumptions.all, ∀ {rec : Record Ref},
      rec.id = .thread (g, (X.tr g).length) →
      a.wf L m (X.snocObject g ⟨(thread P L g).pc σ, .wait (MbarRow.loc L g f) q ok true sc'⟩
        (fun _ => none) (MbarRow.loc L g f) rec) :=
    fun _ _ a ha _ _ => hc.wf.quiet hX (Execution.le_trans le_snoc
      (Execution.le_appendObject ..)) rfl ((Execution.quietExt_snoc (r := fun _ => none) rfl).trans
        (Execution.quietExt_of_tr rfl)) a ha
  have he : ∀ ok, EStep kernel Assumptions.all L g t1
      ⟨(thread P L g).pc σ, .wait (MbarRow.loc L g f) q ok true sc⟩ (some (k ok)) :=
    fun ok => ⟨_, hout, by rw [hpc]; exact hfire ok⟩
  by_cases hready : before.phase % 2 ≠ q % 2
  · exact .inl (.inl (Step.poll_counted_extension hX hpd.1 hne hrel (hasm true) hrun hl (he true)
      hstate hready))
  · push Not at hready
    have hYmax := Step.failed_poll_maximal hc.max hpd.1 hne hrel (hasm false) hrun hl (he false)
      hstate
    refine .inr ⟨⟨(thread P L g).pc σ, .wait (MbarRow.loc L g f) q false true sc⟩,
      ⟨_, hYmax.1, ?_, ?_⟩, fun _ h => by cases h⟩
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc]
    · simp [Step.failedPoll, Execution.snocObject, Execution.appendObject, Execution.snoc,
        Execution.get]

/-- **A released pending lane at a state of the thread machine steps, or has a next event.** -/
private theorem next_at
    (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hpd : Frame.Pending L X g) (hrel : Step.Released L X g)
    {σ : (thread P L g).D}
    (hσ : Frame.stateAt (thread P L) X g (X.tr g).length = some (some σ))
    (hs : SafeGoal kernel Assumptions.all L m)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : CollRel P L m X) (hV : VoteRel P L m X)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0)
    (hfin : ∀ f : MbarFam, 0 < (X.tr g).countP isBar0 →
      ∃ st, MBarrier.stateBefore (X.objects (MbarRow.loc L g f))
        (X.objects (MbarRow.loc L g f)).length = some st)
    (hJ : (table P L).J g σ) :
    Sched.Steps (timed P L) m X (.thread g) ∨
      ∃ e, Sched.NextEv L kernel Assumptions.all m X g e ∧ ∀ f, e.kind ≠ .ub f := by
  have hX := hc.max.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hc.noUb hpd
  rcases Frame.end_atU (fun _ _ => thread_sound hp) hpd.1 hrun hσ with
    ⟨t1, ins, hl, hat, hi, hins, hout⟩ | ⟨u, f, hl, hout⟩
  swap
  · exact .inl (.inl (Sched.fault_extension hX (launched_all hX) hc hpd.1 hrel hrun hl hout))
  have hloc : ins.op.isLocal = false := by
    obtain ⟨i2, h2, hl2, -⟩ := ((thread_sound hp).steps σ).site hi
    rw [hins] at h2
    cases h2
    exact hl2
  have hone : ∀ i, kernel.code[(thread P L g).pc σ]? = some i → i = ins := fun i h =>
    Option.some.inj (h.symm.trans hins)
  have hrest : ∀ k, Descent.opKind ins.op = k → ∀ i, kernel.code[(thread P L g).pc σ]? = some i →
      Descent.opKind i.op = k := fun k hk i h => by rw [hone i h]; exact hk
  have hord : (Descent.opKind ins.op).Rest = false → Sched.Steps (timed P L) m X (.thread g) :=
    fun hr => ordinary_at hp hc hFw hpd hrel hσ (fun i h => by rw [hone i h]; exact hr)
      fun _ _ _ => hd g
  have hrs := at_all restOk_all hins
  cases hkd : Descent.opKind ins.op
  case wait =>
    simp only [restOk, hkd, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at hrs
    exact poll_at hp hc hFw hpd hrel hσ hfin hJ hrun hl hat hi hins hout hrs.2.1
      (by simpa using hrs.2.2)
  case warp =>
    rcases kinds_warp hins hkd with h | h
    · exact .inl (coll_steps_pend hc hp hs hFw hd hW hpd hrel
      (pendAtColl_iff.2 ⟨σ, hσ, ins, hins, h⟩))
    · exact .inl (vote_steps_pend hp hc hs hFw hd hV hpd (pendAtPc_iff.2 ⟨σ, hσ, hi, h⟩))
  case reg =>
    exact .inl (reg_at hp hc hFw hpd hrel hσ (J := hJ) (hi := hi)
      (fun i h => by rw [hone i h]; exact kinds_reg hins hkd) ⟨ins, hins⟩)
  case alloc =>
    simp only [restOk, hkd, Bool.and_eq_true, bne_self_eq_false, Bool.false_or] at hrs
    exact .inl (alloc_at hp hc hpd hrel hσ (fun i h => by rw [hone i h]; exact hrs.1.2) hzero)
  case other =>
    rcases kinds_other hins hkd hloc with h | h
    · obtain ⟨gd, op⟩ := ins
      cases op <;> simp only [isTrap, Bool.false_eq_true] at h
      have hf : eventTmpl Assumptions.all L g t1 .trap = .ub .trap := rfl
      rw [hf] at hout
      exact .inl (.inl (Sched.fault_extension hX (launched_all hX) hc hpd.1 hrel hrun hl hout))
    · exact .inl (other_at hp hc hpd hrel hσ (fun i hh => by rw [hone i hh]; exact h))
  all_goals exact .inl (hord (by rw [hkd]; rfl))

/-- **A pending released lane of a maximal execution steps, or its trace extends consistently by
an event that is no undefined behaviour.** The lane's polls are of objects of its CTA, whose
state is final once it has passed barrier 0 (`hfin`); its warp's other lanes are the
collective's (`CollRel`, `VoteRel`). -/
theorem next_all {g : Nat} (hp : Pre P L m) (hc : Descent.NextEnvQ L kernel Assumptions.all m X)
    (hs : SafeGoal kernel Assumptions.all L m) (hFw : Follow P L X)
    (hd : ∀ h, TensorStore.Drained drainSel X h) (hW : CollRel P L m X) (hV : VoteRel P L m X)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0)
    (hfin : ∀ f : MbarFam, 0 < (X.tr g).countP isBar0 →
      ∃ st, MBarrier.stateBefore (X.objects (MbarRow.loc L g f))
        (X.objects (MbarRow.loc L g f)).length = some st)
    (hpd : Frame.Pending L X g) (hrel : Step.Released L X g) :
    Sched.Steps (timed P L) m X (.thread g) ∨
      ∃ e, Sched.NextEv L kernel Assumptions.all m X g e ∧ ∀ f, e.kind ≠ .ub f := by
  have hG := (follow_iff.mp hFw) g hpd.1 (X.tr g).length
  cases h : Frame.stateAt (thread P L) X g (X.tr g).length with
  | none =>
    exact .inl (Descent.dead_steps_inOrderUQ hc.wf hc.max hc.noUb
      (fun _ _ => thread_sound hp) hpd h hrel)
  | some o =>
    cases o with
    | none => exact absurd h hG.1
    | some σ => exact next_at hp hc hFw hpd hrel h hs hd hW hV hzero hfin (hG.2 σ h)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
