-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepArr
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's sites that name an mbarrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The parity word of a loader poll. -/
def ldPar (p : Params) (L : Launch) (g w : Nat) (d : Loader.D) : Nat :=
  (truncBits 32 (Loader.rv p L g w d (Loader.waitRegs d.site).2)).toNat % 2

/-- **The loader's uses of an object**, site by site (`k`, `A`: the loop positions). -/
inductive LdUse (p : Params) (L : Launch) (g w k A : Nat) (d : Loader.D) (e : Event) (l : Loc) :
    Prop where
  | slot (per : Loader.Per) (vv ok : Bool) (hs : d.site = .slot per vv)
      (hl : l = obj L g (56 + 8 * (Loader.pkOf per vv k % 3)))
      (hk : e.kind = .wait l (ldPar p L g w d) ok true .cta)
  | tw (t : Fin 7) (ok : Bool) (hs : d.site = .tw t) (hl : l = obj L g (Loader.twOff t))
      (hk : e.kind = .wait l (ldPar p L g w d) ok true .cta)
  | dw (j : Fin 3) (ok : Bool) (hs : d.site = .dw j) (hl : l = obj L g (56 + 8 * ((A + j.val) % 3)))
      (hk : e.kind = .wait l (ldPar p L g w d) ok true .cta)
  | dq (ok : Bool) (hs : d.site = .dq) (hl : l = obj L g 24)
      (hk : e.kind = .wait l (ldPar p L g w d) ok true .cta)
  | arrive (per : Loader.Per) (vv : Bool) (hs : d.site = .arrive per vv)
      (hl : l = obj L g (32 + 8 * (Loader.pkOf per vv k % 3))) (hk : e.kind = .asyncArrive l true)
  | ta (t : Fin 7) (tx : Nat) (hs : d.site = .ta t) (hl : l = obj L g (Loader.taOff t))
      (hk : e.kind = .arrive l tx 1 true .cta)
  | da (tx : Nat) (hs : d.site = .da) (hl : l = obj L g 8) (hk : e.kind = .arrive l tx 1 true .cta)
  | tc (t : Fin 7) (c : Fin 2) (a : Nat) (s : TensorCopy.Spec) (hs : d.site = .tc t c)
      (hl : l = obj L g (Loader.taOff t)) (hk : e.kind = .tensorIssue a s) (hb : s.mbar = l)

theorem twOff_mem (t : Fin 7) : (t = 0 ∧ Loader.twOff t = 16) ∨ Loader.twOff t = 24 ∨
    Loader.twOff t = 336 ∨ Loader.twOff t = 344 := by revert t; decide

theorem taOff_mem (t : Fin 7) : Loader.taOff t = 0 ∨ Loader.taOff t = 8 ∨
    Loader.taOff t = 320 ∨ Loader.taOff t = 328 := by revert t; decide

theorem tc_loc (hp : Pre p L m) (t : Fin 7) (c : Fin 2) {w : Nat} {v : Loader.V} {kk : Fin 2} :
    smLoc L g (Loader.rv p L g w ⟨.tc t c, v, kk⟩ (Loader.tcBar t).1) (Loader.tcBar t).2 =
      obj L g (Loader.taOff t) := by
  fin_cases t
  · exact Loader.smLoc_sb hp 0 (by norm_num)
  · exact Loader.smLoc_addi hp 320 (by norm_num)
  · exact Loader.smLoc_sb hp 8 (by norm_num)
  · exact Loader.smLoc_sb hp 328 (by norm_num)
  · exact Loader.smLoc_addi hp 320 (by norm_num)
  · exact Loader.smLoc_sb hp 328 (by norm_num)
  · exact Loader.smLoc_addi hp 320 (by norm_num)

set_option hygiene false in
/-- Close a site whose shape names no object. -/
local macro "no_mbar" : tactic => `(tactic| (
  first
    | (exfalso
       rcases epi_site hev hm with ⟨_, h, -⟩ | ⟨_, h, -⟩ <;>
         simp [Loader.Site.toE] at h; done)
    | (exfalso
       (try shape_destruct hev)
       all_goals (try subst_vars)
       all_goals first
         | exact (False.elim hm)
         | (cases hm; done))))

set_option maxHeartbeats 4000000 in
/-- **Every use of an object by the loader.** -/
theorem ld_use (hp : Pre p L m) {w : Nat} {d : Loader.D} {k A : Nat} {e : Event} {l : Loc}
    (hR : Loader.RefRing p L g w d k A) (hev : Loader.Ev p L g w d e) (hm : MbarOf e l) :
    LdUse p L g w k A d e l := by
  obtain ⟨site, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases site <;> simp only [Loader.Ev] at hev
  case slot per vv =>
    obtain ⟨ok, hk⟩ := hev
    subst hk
    have hl : l = _ := hm
    exact .slot per vv ok rfl (hl.trans (Loader.slot_loc hp hR)) (by subst hl; rfl)
  case tw t =>
    obtain ⟨ok, hk⟩ := hev
    subst hk
    have hl : l = _ := hm
    exact .tw t ok rfl (hl.trans (Loader.tw_loc hp t)) (by subst hl; rfl)
  case dw j =>
    obtain ⟨ok, hk⟩ := hev
    subst hk
    have hl : l = _ := hm
    exact .dw j ok rfl (hl.trans (Loader.dw_loc hp j hR)) (by subst hl; rfl)
  case dq =>
    obtain ⟨ok, hk⟩ := hev
    subst hk
    have hl : l = _ := hm
    exact .dq ok rfl (hl.trans (Loader.smLoc_addi hp 24 (by norm_num))) (by subst hl; rfl)
  case arrive per vv =>
    subst hev
    have hl : l = _ := hm
    exact .arrive per vv rfl (hl.trans (Loader.arrive_loc hp hR)) (by subst hl; rfl)
  case ta t =>
    subst hev
    have hl : l = _ := hm
    exact .ta t _ rfl (hl.trans (Loader.ta_loc hp t)) (by subst hl; rfl)
  case da =>
    subst hev
    have hl : l = _ := hm
    exact .da _ rfl (hl.trans (Loader.smLoc_sb hp 8 (by norm_num))) (by subst hl; rfl)
  case tc t c =>
    rcases hev with ⟨a, s, hk, hb⟩ | ⟨_, hk⟩
    · subst hk
      have hl : s.mbar = l := hm
      exact .tc t c a s rfl (hl.symm.trans (hb.trans (tc_loc hp t c))) rfl hl
    · subst hk
      exact False.elim hm
  all_goals no_mbar

end
end PTX.Kernels.TmlFa4Fwd.Proof
