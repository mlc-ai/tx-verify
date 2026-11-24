-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Defs
public import Kernels.TmlFa4Fwd.Proof.Top.Prog.Entry
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Loader.Export.TimeLag
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The register requests in the time table

A lane without a register request is at or before `scanBase` (`reg_before`: it is in the startup or
at its role's entry); after its request a lane is later (`reg_after`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A role's entry is at `scanBase`. -/
theorem entry_time {g : Nat} {i : Role} {d : (frag p L g i).D} {n : Cls → Nat} (hE : IsEntry i d) :
    Progress.time p L g (.inr ⟨i, d⟩, n) = Progress.scanBase := by
  cases i <;> simp only [IsEntry] at hE
  case mma => subst hE; rfl
  all_goals simp [Progress.time, Progress.roleTime, Progress.Out.time, Progress.Cr.time,
    Progress.Sm.time, Progress.Ld.time, hE, Progress.Cr.part, Progress.Cr.endOff,
    Progress.Sm.place, Progress.Sm.pre, Progress.Sm.endOff, Softmax.Control.D.scheduler,
      Correction.Control.D.scheduler]

/-- **A lane without a register request is at or before `scanBase`.** -/
theorem reg_before (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) {h : Nat} (hh : h < L.threads)
    (hno : ∀ j pc inc n inst, X.get (h, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) :
    Sched.threadTime (Progress.timed p L) X h ≤ Progress.scanBase := by
  have key : ∀ k σ, k ≤ (X.tr h).length → Frame.stateAt (thread p L) X h k = some (some σ) →
      (Progress.time p L h σ < Progress.scanBase) ∨
        (k = (X.tr h).length ∧ Progress.time p L h σ = Progress.scanBase) := by
    intro k σ hk hσ
    obtain ⟨σ, n⟩ := σ
    rcases σ with s | r
    · refine .inl (Progress.startTime_lt fun r he => ?_)
      exact jr_start_site ((goodR' hp hX hh k).2 _ hσ) r he
    · obtain ⟨j, hj, i, n', hσ'⟩ := first_role k r n hσ
      have hE : IsEntry i (frag p L h i).init := by cases i <;> first | rfl | trivial
      have hJ := (goodR' hp hX hh j).2 _ hσ'
      have hlen : (X.tr h).length ≤ j := by
        by_contra hlt
        obtain ⟨e, he⟩ : ∃ e, X.get (h, j) = some e :=
          ⟨_, List.getElem?_eq_getElem (by omega : j < (X.tr h).length)⟩
        obtain ⟨inc, nn, inst, hke⟩ := entry_fires hp hX hσ' hE hJ he (by
          obtain ⟨pc,kind⟩ := e; rintro f rfl; exact hub ⟨_,pc,f,he⟩)
        obtain ⟨pc, kd⟩ := e
        simp only at hke
        subst hke
        exact hno _ _ _ _ _ he
      obtain rfl : k = j := by omega
      rw [hσ] at hσ'
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at hσ'
      obtain ⟨rfl, -⟩ := hσ'
      exact .inr ⟨by omega, entry_time hE⟩
  unfold Sched.threadTime
  split
  · rename_i d hd
    rcases key _ d le_rfl hd with h1 | ⟨-, h1⟩
    · exact h1.le
    · exact h1.le
  · exact Nat.zero_le _
  · split
    · rename_i hn _ d hd
      rcases key _ d (by omega) hd with h1 | ⟨h2, -⟩
      · exact h1
      · exfalso
        rw [← h2, hd] at hn
        cases hn
    · exact Nat.zero_le _

/-- A state of a scheduler pass after three collectives is after `scanBase`. -/
theorem pass_after {late coll : Bool} {c : Nat} (hc : 3 ≤ c) :
    Progress.scanBase <
      Progress.passTime (if late then Progress.endBase p else Progress.scanBase) c coll := by
  have := Progress.scanBase_le_endBase p
  unfold Progress.passTime
  split_ifs <;> omega

/-- **After its register request a lane is later than `scanBase`.** -/
theorem reg_after (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc n inst : Nat} {inc : Bool} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩) :
    ∃ d, Frame.stateAt (thread p L) X g (k + 1) = some (some d) ∧
      Progress.scanBase < Progress.time p L g d := by
  obtain ⟨-, i, d, n0, hσ, hE⟩ := req_at hp hX (launchFollow hp hX) he
  have hJ := (goodR' hp hX hg k).2 _ hσ
  have step : ∀ d', (frag p L g i).next d ⟨pc, .setMaxReg inc n inst⟩ = some (some d') →
      Frame.stateAt (thread p L) X g (k + 1) = some (some (.inr ⟨i, d'⟩,
        Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩)) := by
    intro d' h
    rw [Frame.stateAt_succ (C := thread p L) (show (X.tr g)[k]? = _ from he), hσ]
    show (thread p L g).next (.inr ⟨i, d⟩, n0) _ = _
    simp [thread, glued, Code.counted, Code.glue, h]
  have h3 : n0 .shfl = Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩ .shfl := by
    simp [Code.bump, cls, Execution.isShfl]
  cases i with
  | stub r => exact (JR.not_stub hJ).elim
  | softmax =>
    obtain ⟨site, v, kk⟩ := d
    simp only [IsEntry] at hE
    subst hE
    refine ⟨_, step _ rfl, ?_⟩
    simp [Progress.time, Progress.roleTime, Progress.Sm.time, Progress.Sm.place, Progress.Sm.pre,
      Progress.Sm.endOff, Softmax.Control.D.scheduler, Softmax.Control.erase]
  | correction =>
    obtain ⟨site, v, kk⟩ := d
    simp only [IsEntry] at hE
    subst hE
    refine ⟨_, step _ rfl, ?_⟩
    simp [Progress.time, Progress.roleTime, Progress.Cr.time, Progress.Cr.part,
      Progress.Cr.endOff, Correction.Control.D.scheduler, Correction.Control.erase]
  | epilogue =>
    have hF := (JR.epilogue hJ).2.1
    obtain ⟨site, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17⟩ := d
    simp only [IsEntry] at hE
    subst hE
    have hn : n0 .shfl = 3 ∧ n0 .vote = 0 := hF
    have hv : Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩ .vote = 0 := by
      simp [Code.bump, cls, hn.2, isFullVote, voteClass]
    refine ⟨_, step _ rfl, ?_⟩
    have h3' : 3 ≤ Progress.collCount
        (Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩) := by
      unfold Progress.collCount
      omega
    have h1 := pass_after (p := p) (late := false) (coll := true) h3'
    have h2 := pass_after (p := p) (late := false) (coll := false) h3'
    simp only [Progress.time, Progress.roleTime]
    split <;> simpa [Progress.Out.time, Progress.Out.tail, Progress.Out.late, Progress.Out.coll,
      Epilogue.Scan.late, Epilogue.Site.shfl, Epilogue.Site.ballot] using by assumption
  | loader b =>
    have hF := ((JR.loader hJ).2.2 (ub_zero hX he hσ)).2
    obtain ⟨site, v, kk⟩ := d
    simp only [IsEntry] at hE
    subst hE
    have hn : n0 .shfl = 3 ∧ n0 .vote = 0 ∧ n0 (.load .commit) = 0 := hF
    have hc : Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩ (.load .commit) = 0 := by
      simp [Code.bump, cls, hn.2.2, Loader.cls]
    refine ⟨_, step _ rfl, ?_⟩
    have h3' : 3 ≤ Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩ .shfl -
        32 * Code.bump (cls L g) n0 ⟨pc, .setMaxReg inc n inst⟩ (.load .commit) + 0 := by
      omega
    have h1 := pass_after (p := p) (late := false) (coll := true) h3'
    have h2 := pass_after (p := p) (late := false) (coll := false) h3'
    simp only [Progress.time, Progress.roleTime, Loader.passStart, Loader.D.ite,
      Bool.false_eq_true, ↓reduceIte]
    split <;> simpa [Progress.Ld.time, Progress.Ld.late, Progress.Ld.toE, Progress.Out.ballots,
      Progress.Out.coll, Epilogue.Scan.late, Epilogue.Site.shfl, Epilogue.Site.ballot] using
        by assumption
  | mma =>
    simp only [IsEntry] at hE
    subst hE
    refine ⟨_, step _ rfl, ?_⟩
    show Progress.scanBase < Progress.scanBase + 1
    omega

end PTX.Kernels.TmlFa4Fwd.Proof.Top
