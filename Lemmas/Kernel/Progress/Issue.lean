-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Rank
public import Lemmas.Kernel.Progress.Released
public import Lemmas.Step.CpAsyncIssueProgress
public import Lemmas.Step.RegIssue

@[expose] public section

/-! # Progress at a register request and at a `cp.async` operation

A proof tool, generic over the kernel, beside `Lemmas/Kernel/Progress/Released.lean`: a released
pending thread whose next instruction is its first `setmaxnreg` (`reg_next_steps`) or an issue, a
commit or a no-increment arrival of asynchronous copies (`cpAsync_next_steps`) performs it. -/

namespace PTX.Sched

open PTX PTX.Descent PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

/-- An issue, a commit or a no-increment arrival of `cp.async` copies. -/
def cpAsyncOp : Op → Bool
  | .cpAsync .. | .cpAsyncCommit | .cpAsyncArrive true .. => true
  | _ => false

/-- A `setmaxnreg`. -/
def regOp : Op → Bool
  | .setMaxReg .. => true
  | _ => false

/-- The template of a `cp.async` operation: undefined behaviour or an issue event. -/
theorem cpAsync_tmpl {g : Nat} {t : TState} {op : Op} (h : cpAsyncOp op = true) :
    (∃ f, eventTmpl A L g t op = .ub f) ∨
      ∃ k u, Fires t.pc (eventTmpl A L g t op) ⟨t.pc, k⟩ (some u) ∧
        Step.CpAsyncIssueEvent ⟨t.pc, k⟩ ∧ k.readsMem = false := by
  have key : ∀ r : Exec Tmpl, (∃ f, ofExec r = .ub f) ∨ ∃ m, r = .ok m ∧ ofExec r = m := by
    intro r
    cases r with
    | error f => exact .inl ⟨f, rfl⟩
    | ok m => exact .inr ⟨m, rfl, rfl⟩
  cases op <;> simp only [cpAsyncOp, Bool.false_eq_true] at h
  case cpAsyncCommit => exact .inr ⟨_, _, ⟨rfl, rfl⟩, .inr (.inl rfl), rfl⟩
  case cpAsync db doff sb soff size source policy =>
    simp only [eventTmpl, cpAsyncTmpl]
    rcases key _ with hf | ⟨m, hm, he⟩
    · exact .inl hf
    · right
      rw [he]
      simp only [bind, Except.bind, pure, Except.pure] at hm
      repeat' split at hm
      all_goals first
        | (cases hm; done)
        | (cases hm; exact ⟨_, _, ⟨rfl, rfl⟩, .inl ⟨_, rfl, rfl⟩, rfl⟩)
  case cpAsyncArrive ni base off gen =>
    cases ni <;> simp only [Bool.false_eq_true] at h
    simp only [eventTmpl, cpAsyncTmpl]
    rcases key _ with hf | ⟨m, hm, he⟩
    · exact .inl hf
    · right
      rw [he]
      simp only [bind, Except.bind, pure, Except.pure] at hm
      repeat' split at hm
      all_goals first
        | (cases hm; done)
        | (cases hm; exact ⟨_, _, ⟨rfl, rfl⟩, .inr (.inr ⟨_, rfl⟩), rfl⟩)

/-- **A released pending thread at its first register request steps.** -/
theorem reg_next_steps (hA : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → regOp ins.op = true)
    (hno : ∀ j pc inc n inst, X.get (g, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) :
    Steps M mem0 X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  have hop := hk ins hins
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrder hA hmax.1 hp.1 hne hrel hrun hl hout
  · generalize ins.op = op at hop hm hout
    cases op <;> simp [regOp] at hop
    obtain ⟨inc, n, u, hm⟩ := hm
    rw [hm] at hout
    exact .inl (Step.reg_issue_counted_extension_of_started (inst := 0) hmax.1 hp.1 hne hrel.ready
      (fun j pc' inc' n' inst' => hno j pc' inc' n' inst') hrun hl (o := some u)
      ⟨_, hout, 0, rfl, rfl⟩
      (hA.quiet hmax.1 le_snoc rfl (Execution.noNewRead_snoc rfl)))

/-- **A released pending thread at a `cp.async` operation steps.** -/
theorem cpAsync_next_steps (hA : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → cpAsyncOp ins.op = true) :
    Steps M mem0 X (.thread g) := by
  obtain ⟨t, hrun⟩ := Frame.run_some hmax.1 hub hp
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  rcases cpAsync_tmpl (A := A) (L := L) (g := g) (t := t1) (hk ins hins) with
    ⟨f, hf⟩ | ⟨k, u, hf, he, hr⟩
  · rw [hf] at hout
    exact ub_steps_inOrder hA hmax.1 hp.1 hne hrel hrun hl hout
  · exact .inl (Step.cp_async_issue_counted_extension hmax.1 hp.1 hne hrel hrun hl
      ⟨_, hout, hf⟩ he (hA.quiet hmax.1 le_snoc rfl (Execution.noNewRead_snoc hr)))

/-- A Tensor Memory allocation. -/
def allocOp : Op → Bool
  | .tcAlloc .. => true
  | _ => false

/-- **A released pending thread at a Tensor Memory allocation steps**: it makes the request, or
lane 0 stores the allocation's column, when every recorded allocation is at column 0. -/
theorem alloc_next_steps (hA : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hmax : Maximal L K A mem0 X) (hub : ¬ HasUb X) (hC : ∀ g < L.threads, (M.code g).Sound)
    {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hne : X.tr g ≠ [])
    (hrel : Step.Released L X g)
    (hk : ∀ ins, K.code[(M.code g).pc d]? = some ins → allocOp ins.op = true)
    (hzero : ∀ {cta : Nat} {r : Tmem.Pair.Requests}, r ∈ X.tmemHistory cta →
      ∀ n col, r.action = .alloc n col → col = 0) :
    Steps M mem0 X (.thread g) := by
  have hX := hmax.1
  obtain ⟨t, hrun⟩ := Frame.run_some hX hub hp
  obtain ⟨t1, ins, hl, -, -, hins, hout⟩ := Frame.end_at hC hp.1 hrun hσ
  have hop := hk ins hins
  rcases eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t1) ins.op with ⟨f, hf⟩ | hm
  · rw [hf] at hout
    exact ub_steps_inOrder hA hX hp.1 hne hrel hrun hl hout
  · generalize ins.op = op at hop hm hout
    cases op <;> simp [allocOp] at hop
    rcases hm with ⟨grp, dst, n, u, hm⟩ | ⟨dst, u, hm⟩
    · rw [hm] at hout
      exact .inl (Step.tccoll_counted_extension hX hp.1 (.inl hne) hrel hrun hl (o := some u)
        ⟨_, hout, rfl, rfl⟩ rfl (hX.tmemPairResult.snoc_not_wr nofun)
        (hX.tcRead_snoc_tc fun _ _ _ h => by cases h)
        (hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)))
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
        rfl hres (hA.quiet hX le_snoc rfl (Execution.noNewRead_snoc rfl)))

end
end PTX.Sched
