-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.CommitTarget
import Lemmas.Flow.NotBulk
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A commit notifies the barrier it names

Every `tcgen05.commit` of the code is unmasked, and the launch has clusters of one CTA, so a commit
targets its barrier (`commit_self`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

private def unmasked : Op → Bool
  | .tcCommit _ _ _ mask => mask.isNone
  | _ => true

private theorem unmasked_code : kernel.code.all (fun i => unmasked i.op) = true := by
  decide +kernel

private theorem unmasked_tmpl {A : List Assumption} {g : Nat} {t : TState} {group : CtaGroup}
    {base : Nat} {off : Int} {pc : Nat} {e : Event} {o : Option TState} {s : TcCommit.Spec}
    (hf : Fires pc (eventTmpl A L g t (.tcCommit group base off none)) e o)
    (hk : e.kind = .tc (.commit s)) :
    ∃ mb, TcCommit.resolve L group (g / L.block) mb
      (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) = some s := by
  simp only [eventTmpl, tcCommitTmpl, bind, Except.bind, pure, Except.pure] at hf
  split_ifs at hf
  · cases hm : mbarClusterLoc L g t base off with
    | error f =>
      simp only [hm, ofExec, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | ok mb =>
      simp only [hm] at hf
      cases hs : TcCommit.resolve L group (g / L.block) mb
          (BitVec.ofNat 16 (2 ^ L.rankOfCta mb.cta)) with
      | none =>
        simp only [hs, ofExec, throw, throwThe, MonadExceptOf.throw, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | some s' =>
        simp only [hs, ofExec, Fires] at hf
        rw [hf.1] at hk
        cases hk
        exact ⟨mb, hs⟩
  · simp only [throw, throwThe, MonadExceptOf.throw, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk

/-- A commit's cluster is one CTA, and its first rank is the barrier it names. -/
theorem commit_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {pc : Nat} {s : TcCommit.Spec} (he : X.get i = some ⟨pc, .tc (.commit s)⟩) :
    s.clusterSize = 1 ∧ TcCommit.target s 0 = some s.mbar := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hCode, hf⟩
  · cases hf
  have hCommit : commitOp ins.op = true := by
    cases h : commitOp ins.op
    · exact (fires_notCommit (eventTmpl_notCommit (commitOp_ne h)) hf s rfl).elim
    · rfl
  have hu := List.all_eq_true.mp unmasked_code ins (List.mem_of_getElem? hCode)
  cases hOp : ins.op <;> simp only [hOp, commitOp, Bool.false_eq_true] at hCommit
  rename_i group base off mask
  simp only [hOp, unmasked, Option.isNone_iff_eq_none] at hu
  subst hu
  rw [hOp] at hf
  obtain ⟨mb, hr⟩ := unmasked_tmpl hf rfl
  have hOne := hp.cluster.2.2
  have h1 := hp.cluster.1
  unfold TcCommit.resolve at hr
  split_ifs at hr with hc
  obtain ⟨-, -, hsp, -, hcl, -⟩ := hc
  cases hr
  refine ⟨by simp only [Launch.oneDim_clusterSizeOf hOne, h1], ?_⟩
  simp only [Launch.oneDim_clusterOfCta hOne, h1, Nat.div_one] at hcl
  simp only [TcCommit.target, Launch.oneDim_clusterSizeOf hOne, Launch.oneDim_rankOfCta hOne,
    Launch.oneDim_clusterStart hOne, Launch.oneDim_clusterOfCta hOne, h1]
  obtain ⟨sp, cta, addr⟩ := mb
  simp only at hsp hcl
  subst hsp hcl
  simp [Nat.mod_one]

/-- **A commit targets the barrier it names.** -/
theorem commit_self (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {pc : Nat} {s : TcCommit.Spec} (he : X.get i = some ⟨pc, .tc (.commit s)⟩) :
    ∃ rank, TcCommit.target s rank = some s.mbar := ⟨0, (commit_zero hp hX he).2⟩

/-- A commit's target is its first rank. -/
theorem commit_rank_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {i : EvId}
    {pc : Nat} {s : TcCommit.Spec} {rank : Fin 16} {l : Loc}
    (he : X.get i = some ⟨pc, .tc (.commit s)⟩) (ht : TcCommit.target s rank = some l) :
    rank = 0 := by
  have hc := (commit_zero hp hX he).1
  unfold TcCommit.target at ht
  split_ifs at ht with h
  have := h.1
  exact Fin.ext (by simp only [Fin.val_zero]; omega)

end PTX.Kernels.TmlFa4Fwd.Proof
