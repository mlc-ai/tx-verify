-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.StaticSafety
public import Lemmas.Execution.NoTcCp
public import Lemmas.Flow.NotTcShift

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow

private def defaultCommitTarget : Op → Bool
  | .tcCommit _ _ _ mask => mask.isNone
  | _ => true

private theorem defaultCommitTargetCode :
    kernel.code.all (fun ins => defaultCommitTarget ins.op) = true := by
  decide +kernel

/-- Every actual commit notifies exactly rank zero in the issuing CTA's cluster. -/
theorem commitTargetSingle {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {s : TcCommit.Spec} (hi : X.Commit i s) :
    ∃ loc, ∀ rank, TcCommit.target s rank = if rank.val = 0 then some loc else none := by
  obtain ⟨site, he⟩ := hi
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨t, ins, _, _, hCode, hf⟩
  · cases hBad
  have hCommit : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf s rfl).elim
    · rfl
  have hDefault := List.all_eq_true.mp defaultCommitTargetCode ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, commitOp, Bool.false_eq_true] at hCommit
  rename_i group base offset mask
  have hMask : mask = none := by cases mask <;> simp_all [defaultCommitTarget]
  rw [hOp, hMask] at hf
  change Fires site (tcCommitTmpl l i.1 t (.tcCommit group base offset none))
    ⟨site, .tc (.commit s)⟩ _ at hf
  have hg := PTX.Proof.event_thread_lt hX he
  simp only [tcCommitTmpl, hg, ↓reduceIte, bind, Except.bind, pure, Except.pure] at hf
  cases hBar : mbarClusterLoc l i.1 t base offset with
  | error fault => simp [hBar, ofExec, Fires] at hf
  | ok bar =>
    have hRank : l.rankOfCta bar.cta = 0 := by
      rw [Launch.oneDim_rankOfCta hp.cluster.2.2, hp.cluster.1, Nat.mod_one]
    simp only [hBar, hRank, pow_zero] at hf
    cases hResolve : TcCommit.resolve l group (i.1 / l.block) bar (BitVec.ofNat 16 1) with
    | none => simp [hResolve, ofExec, Fires, throw, throwThe, MonadExceptOf.throw] at hf
    | some spec =>
      simp only [hResolve, ofExec, Fires, Event.mk.injEq, Kind.tc.injEq, TcKind.commit.injEq] at hf
      obtain rfl := hf.1.2
      unfold TcCommit.resolve at hResolve
      split at hResolve
      · cases hResolve
        rw [Launch.oneDim_clusterSizeOf hp.cluster.2.2, hp.cluster.1]
        refine ⟨⟨.shared, l.clusterStart (l.clusterOfCta (i.1 / l.block)), bar.addr⟩, ?_⟩
        intro rank
        by_cases hr : rank.val = 0
        · simp [TcCommit.target, hr]
        · have hNot : ¬ rank.val < 1 := by omega
          simp [TcCommit.target, hr, hNot]
      · cases hResolve

private theorem noTcCopy : kernel.NoTcCp = true := by decide +kernel

private theorem noTcShift :
    kernel.code.all (fun ins => !tcShiftOp ins.op) = true := by
  decide +kernel

/-- Every actual asynchronous Tensor Core operation is an MMA. -/
theorem tcAsyncIsMma {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} (hi : X.TcAsync i) :
    ∃ d s acc mask, X.MmaIssue i d s acc mask := by
  rcases hi with hMma | ⟨cp, hCopy⟩ | ⟨shift, _, hShift⟩
  · exact hMma
  · exact (noCp_of_consistent noTcCopy hX i cp hCopy).elim
  · exact (no_kind_of_code hX tcShiftOp (fun k => ∃ s, k = .tc (.shift s))
      (fun _ ⟨_, h⟩ => by cases h) (fun hf ⟨_, hk⟩ => fires_tcShift_op hf hk)
      noTcShift hShift ⟨shift, rfl⟩).elim

end PTX.Kernels.TmlFa4Fwd.Thread
