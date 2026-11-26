-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.IssueU
public import Lemmas.Quiet.Base
public import Lemmas.Quiet.Kernel.NextReads

@[expose] public section

/-! # Issue steps of an unrolled machine under quiet extensions

`Lemmas/Kernel/Progress/IssueU.lean` under `Assumption.WfQuiet`. -/

namespace PTX.Sched
open PTX PTX.Descent PTX.Flow
noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- **A released pending thread at its first register request steps.** -/
theorem reg_next_stepsUQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).SoundU)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → regOp ins.op = true)
    (hno : ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) :
    Steps M mem0 X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hs | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hs
  have hop := hk ins hins
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  · generalize ins.op = op at hop hm hout
    cases op <;> simp [regOp] at hop
    obtain ⟨inc, n, u, hm⟩ := hm
    rw [hm] at hout
    exact .inl (Step.reg_issue_counted_extension_of_started (inst := 0) hmax.1 hp.1 hne hrel.ready
      (fun j pc' inc' n' inst' => hno j pc' inc' n' inst') hrun hl (o := some u)
      ⟨_, hout, 0, rfl, rfl⟩
      (hA.quiet hmax.1 le_snoc rfl (Execution.quietExt_snoc rfl)))

/-- **A released pending thread at a `cp.async` operation steps.** -/
theorem cpAsync_next_stepsUQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).SoundU)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → cpAsyncOp ins.op = true) :
    Steps M mem0 X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hs | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hs
  rcases cpAsync_tmpl (A := A) (L := L) (g := g) (t := t1) (hk ins hins) with
    ⟨f, hf⟩ | ⟨k, u, hf, he, hr⟩
  · rw [hf] at hout
    exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  · exact .inl (Step.cp_async_issue_counted_extension hmax.1 hp.1 hne hrel hrun hl
      ⟨_, hout, hf⟩ he (hA.quiet hmax.1 le_snoc rfl (Execution.quietExt_snoc hr (by
        rcases he with ⟨_, h, -⟩ | h | ⟨_, h⟩ <;> simp only at h <;> rw [h] <;> rfl))))

/-- **A released pending thread at a Tensor Memory allocation steps**: it makes the request, or
lane 0 stores the allocation's column, when every recorded allocation is at column 0. -/
theorem alloc_next_stepsUQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).SoundU)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → allocOp ins.op = true)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hs | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hs
  have hop := hk ins hins
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrderQ hA hX hp.1 hne hrel hrun hl hout
  · generalize ins.op = op at hop hm hout
    cases op <;> simp [allocOp] at hop
    rcases hm with ⟨grp, dst, n, u, hm⟩ | ⟨dst, u, hm⟩
    · rw [hm] at hout
      exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
        ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
        (hX.tcRead_snoc_tc fun _ _ _ h => by cases h)
        (hA.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl)))
    · rw [hm] at hout
      let e : Event := ⟨t1.pc, .wr { loc := dst, size := 4 }
        (Value.bits 32 (BitVec.ofNat 64 0)).toBytes⟩
      have hres : Tmem.Pair.ResultOk L (X.snoc g e (fun _ => none)) := by
        apply hX.tmemPairResult.snoc
        intro pc a bs he _ pc' grp dst' n hget key x base hx hwi hwa
        simp only [e, Event.mk.injEq, Kind.wr.injEq] at he
        obtain ⟨-, -, rfl⟩ := he
        rw [hzero hx n base hwa]
      exact .inl (Step.plain_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
        (e := e) ⟨_, hout, 0, by decide, rfl, rfl⟩ rfl (by simp [e, Kind.isTma])
        (fun _ _ _ _ _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
        rfl hres (hA.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl)))

/-- **A released pending thread at a Tensor Memory store or a store wait steps.** -/
theorem tcStore_next_stepsUQ (hA : Assumption.WfQuiet (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).SoundU)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → tcStoreOp ins.op = true) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  rcases Frame.end_atU hC hp.1 hrun hσ with hs | ⟨u, f, hl, hout⟩
  case inr => exact ub_steps_inOrderQ hA hmax.1 hp.1 hne hrel hrun hl hout
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := hs
  rcases tcStore_tmpl (A := A) (L := L) (g := g) (t := t1) (hk ins hins) with
    ⟨f, hf⟩ | ⟨k, u, hf, hkk⟩
  · rw [hf] at hout
    exact ub_steps_inOrderQ hA hX hp.1 hne hrel hrun hl hout
  · rw [hf] at hout
    have hcoll : isTcColl ⟨t1.pc, .tc k⟩ = true := by
      rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> rfl
    refine .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
      ⟨_, hout, rfl, rfl⟩ hcoll (hX.tmemPairResult.snoc_not_wr ?_) (hX.tcRead_snoc_tc ?_)
      (hA.quiet hX le_snoc rfl (Execution.quietExt_snoc rfl)))
    · rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> nofun
    · rcases hkk with rfl | rfl | ⟨_, _, _, rfl⟩ <;> nofun

end

end PTX.Sched
