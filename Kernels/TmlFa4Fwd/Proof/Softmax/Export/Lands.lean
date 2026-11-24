-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Flow.PollLands
public import Lemmas.Flow.WarpUniform
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Softmax.GenRules
import Lemmas.Flow.PollGuardsPass

@[expose] public section

/-! # The kernel's uniform branches: the static facts of ERR-NONUNIFORM-GUARD

Every lane-compared instruction is the branch of a wait loop (`pollGuards`), every such branch is
selected by `pollAgree` (`pollBranch_sel`), and every local step lands at the next position or off
those branches (`localLands`): the software exponentiation segments end off them. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Assumption

private theorem pass : pollPass Assumptions.pollAgreeSites 0 none kernel.code = true := by
  decide +kernel

theorem pollGuards : kernel.pollGuardsOk = true := pollPass_ok pass

theorem pollBranch_sel {site : Nat} (h : kernel.pollBranch site = true) :
    Assumptions.all.any (·.uniPoll site) = true := by
  rw [Assumptions.all_uniPoll]
  simpa using pollPass_branch pass h

/-- The software exponentiation segments end off the poll branches. -/
private theorem segStops :
    Assumptions.swExp2Sites.all (fun pc => cuteExp2.shapes.all fun sh =>
      !Assumptions.pollAgreeSites.contains (pc + sh.body.length)) = true := by decide +kernel

private theorem execSwExp2_pc {m : SegMatch CuteSlot} {t t' : TState}
    (h : Assumptions.execSwExp2 m t = .ok t') : t'.pc = m.stop := by
  unfold Assumptions.execSwExp2 at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | cases h; rfl
    | simp_all

private theorem segLands : SegLandsAll kernel Assumptions.all := by
  intro a ha L g t t' ht
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inl =>
    right
    simp only [Assumptions.swExp2] at ht
    split_ifs at ht with hs
    obtain ⟨m, hm, hex⟩ := Option.map_eq_some_iff.mp ht
    have h := List.all_eq_true.mp segStops _ (by simpa using hs.1 : t.pc ∈ Assumptions.swExp2Sites)
    unfold SegTemplate.matchAt at hm
    obtain ⟨sh, hsh, hm'⟩ := List.exists_of_findSome?_eq_some hm
    obtain ⟨asg, -, rfl⟩ := Option.map_eq_some_iff.mp hm'
    have h := List.all_eq_true.mp h sh hsh
    rw [execSwExp2_pc hex]
    by_contra hb
    have := pollPass_branch pass (by simpa using hb)
    simp [this] at h
  all_goals exact absurd ht (by intro h; cases h)

theorem localLands {L : Launch} : LocalLands kernel Assumptions.all L :=
  LocalLands.of_rules Softmax.Gen.rulesFrame segLands

end PTX.Kernels.TmlFa4Fwd.Proof
