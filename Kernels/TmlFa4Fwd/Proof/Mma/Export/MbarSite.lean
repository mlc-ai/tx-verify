-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Poll
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The MMA warp's sites that name an mbarrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option hygiene false in
/-- Close a site whose shape names no object. -/
local macro "no_mbar" : tactic => `(tactic| (
  first
    | (exfalso
       rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;>
         simp [Mma.Site.toE] at h; done)
    | (exfalso
       (try shape_destruct hev)
       all_goals (try subst_vars)
       all_goals first
         | exact (False.elim hm)
         | (cases hm; done))))

/-- **The MMA warp's uses of an object**: a poll, or a commit. -/
inductive MmaUse (L : Launch) (g : Nat) (d : Mma.D) (e : Event) (l : Loc) : Prop where
  | poll (ok : Bool) (hs : Progress.isPoll d.site = true) (hl : l = Progress.pollLoc L g d)
      (hk : e.kind = .wait l (Progress.pollPar L d) ok true .cta)
  | commit (c : Fin 12) (s : TcCommit.Spec) (hs : d.site = .cm c) (hk : e.kind = .tc (.commit s))
      (hb : s.mbar = smLoc L g (Mma.cmOp L d.v c).1 (Mma.cmOp L d.v c).2)

set_option maxHeartbeats 4000000 in
/-- **Every use of an object by the MMA warp.** -/
theorem mma_use {d : Mma.D} {e : Event} {l : Loc} (hev : Mma.Ev p L g d e) (hm : MbarOf e l) :
    MmaUse L g d e l := by
  obtain ⟨site, v⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site <;> simp only [Mma.Ev] at hev
  case wt kk =>
    rcases hev with ⟨ok, hk⟩ | ⟨_, hk⟩ <;> subst hk
    · have hl : l = _ := hm
      exact .poll ok rfl hl (by subst hl; rfl)
    · exact False.elim hm
  case mw b ld =>
    rcases hev with ⟨ok, hk⟩ | ⟨_, hk⟩ <;> subst hk
    · have hl : l = _ := hm
      exact .poll ok rfl hl (by subst hl; rfl)
    · exact False.elim hm
  case cm c =>
    rcases hev with ⟨s, hk, hb, -⟩ | ⟨_, hk⟩
    · exact .commit c s rfl hk hb
    · subst hk; exact False.elim hm
  all_goals no_mbar

/-- The barrier offset of an MMA poll: a Q stage, a K/V slot, or a softmax or P barrier. -/
theorem pollO_cases' (r : Nat) (s : Mma.Site) :
    Progress.pollO r s = 0 ∨ Progress.pollO r s = 8 ∨ 96 ≤ Progress.pollO r s ∨
      ∃ j : Fin 3, Progress.pollO r s = 32 + 8 * j.val := by
  cases s <;> simp only [Progress.pollO]
  case wt k =>
    fin_cases k <;> simp
    all_goals first
      | exact .inr (.inr ⟨⟨(2 * r + 1) % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩)
      | exact .inr (.inr ⟨⟨(2 * r + 2) % 3, Nat.mod_lt _ (by decide)⟩, rfl⟩)
  case mw b ld => split <;> simp
  all_goals simp

set_option maxHeartbeats 8000000 in
/-- An MMA lane's election is at an election site of the pipeline. -/
theorem mma_elect_site {d : Mma.D} {e : Event} {mask inst ld : Nat} (hev : Mma.Ev p L g d e)
    (hk : e.kind = .elect mask inst ld) :
    d.site.pipe = true ∧ ((∃ b, d.site = .eq b) ∨ (∃ b, d.site = .ep b) ∨ ∃ c, d.site = .ce c) := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, v⟩ := d
  cases site <;> simp only [Mma.Ev] at hev
  case eq b => exact ⟨rfl, .inl ⟨b, rfl⟩⟩
  case ep b => exact ⟨rfl, .inr (.inl ⟨b, rfl⟩)⟩
  case ce c => exact ⟨rfl, .inr (.inr ⟨c, rfl⟩)⟩
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Mma.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq] at *)

set_option maxHeartbeats 8000000 in
/-- An MMA lane's commit is at a commit site of the pipeline, on the site's barrier. -/
theorem mma_commit_site {d : Mma.D} {e : Event} {s : TcCommit.Spec} (hev : Mma.Ev p L g d e)
    (hk : e.kind = .tc (.commit s)) :
    ∃ c, d.site = .cm c ∧ s.mbar = smLoc L g (Mma.cmOp L d.v c).1 (Mma.cmOp L d.v c).2 := by
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  obtain ⟨site, v⟩ := d
  cases site <;> simp only [Mma.Ev] at hev
  case cm c =>
    rcases hev with ⟨s', h, hb, -⟩ | ⟨_, h⟩
    · cases h; exact ⟨c, rfl, hb⟩
    · cases h
  all_goals exfalso
  all_goals (try simp only [Epilogue.Ev, Mma.Site.toE] at hev)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (simp only [reduceCtorEq, Kind.tc.injEq, TcKind.commit.injEq] at *)

end
end PTX.Kernels.TmlFa4Fwd.Proof
