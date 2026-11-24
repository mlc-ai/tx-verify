-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Ref
public import Kernels.TmlFa4Fwd.Proof.Mma.Places
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputSlots
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CommitTarget
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
public import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Kernel.Safety.Classes
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Top.JRMma
import Kernels.TmlFa4Fwd.Proof.Top.JRLoader

@[expose] public section

/-! # Every mbarrier a role names is one of the startup's objects

`use_obj`: an event fired from a followed state of a lane, with its role's shape, that names an
mbarrier object (`MbarOf`) and is no initialization names one of the 34 objects the startup of
the lane's CTA initializes (`IsObj`: the shared base plus an offset of `ObjOff`). Per role, the
objects are read off the shape tables: the output warp's ready and free barriers, the correction
and softmax warps' barriers at constant offsets (the softmax warps' shifted by their stage), the
MMA warp's polls and commits (its ring slots from its loop registers; a commit's target is the
issuing CTA's by `noTcCommitUnsafe`), the loader warps' polls, arrivals and tensor copies (its
ring slots from `RefRing`). The startup names objects only by its initializations. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- One of the startup's objects of lane `g`'s CTA. -/
def IsObj (L : Launch) (g : Nat) (l : Loc) : Prop := ∃ o, ObjOff o ∧ l = obj L g o

/-- One of the objects of lane `g`'s CTA at an offset of `P`. -/
def IsObjIn (L : Launch) (g : Nat) (l : Loc) (P : Nat → Prop) : Prop := ∃ o, P o ∧ l = obj L g o

/-- The offsets the softmax warps name: their stage's barriers at 80 to 120, the request barrier
at 192 or 200, and 320 to 344 (and 0 or 8, the table's value at a site without a barrier). -/
abbrev SoftOff (o : Nat) : Prop :=
  ObjOff o ∧ (o ≤ 8 ∨ (80 ≤ o ∧ o ≤ 120) ∨ o = 192 ∨ o = 200 ∨ 320 ≤ o)
/-- The offsets the MMA warp names: below 128, and 144 and 152. -/
abbrev MmaOff (o : Nat) : Prop := ObjOff o ∧ (o ≤ 120 ∨ o = 144 ∨ o = 152)
/-- The offsets the loader warps name: below 80, and 320 to 344. -/
abbrev LdOff (o : Nat) : Prop := ObjOff o ∧ (o ≤ 72 ∨ 320 ≤ o)

theorem IsObjIn.obj {l : Loc} {P : Nat → Prop} (hP : ∀ o, P o → ObjOff o)
    (h : IsObjIn L g l P) : IsObj L g l := by
  obtain ⟨o, ho, rfl⟩ := h
  exact ⟨o, hP o ho, rfl⟩

/-- Close `IsObj` of a location stated as the shared base plus a literal offset. -/
macro "obj_close" : tactic => `(tactic| (
  first
    | (subst_vars; refine ⟨_, ?_, rfl⟩; simp only [ObjOff]; omega)
    | (refine ⟨_, ?_, rfl⟩; simp only [ObjOff]; omega)))

theorem epi_obj {d : Epilogue.D} {e : Event} {l : Loc} (hev : Epilogue.Ev p L g d e)
    (hm : MbarOf e l) : IsObj L g l := by
  rcases epi_site hev hm with ⟨st, -, rfl⟩ | ⟨st, -, rfl⟩
  · exact ⟨208 + 8 * st.val, by simp only [ObjOff]; omega, rfl⟩
  · exact ⟨224 + 8 * st.val, by simp only [ObjOff]; omega, rfl⟩

theorem corr_obj {d : Correction.D} {e : Event} {l : Loc} (hev : Correction.Ev p L g d e)
    (hm : MbarOf e l) : IsObj L g l := by
  rcases corr_mbar2 hev hm with ⟨-, hl, ho⟩ | ⟨_, _, -, hl, ho⟩
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    exact ⟨_, by simp only [ObjOff]; omega, hl⟩

theorem soft_obj {d : Softmax.D} {e : Event} {l : Loc} (hev : Softmax.Ev p L g d e)
    (hm : MbarOf e l) : IsObjIn L g l SoftOff := by
  have hst : Softmax.stS L g = 0 ∨ Softmax.stS L g = 8 := by
    unfold Softmax.stS; split <;> simp
  rcases soft_mbar hev hm with ⟨-, hl, ho⟩ | ⟨_, _, -, hl, ho⟩
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    exact ⟨_, by simp only [SoftOff, ObjOff]; omega, hl⟩

/-- A location of the MMA warp's table as an object. -/
theorem mma_bl {o : Nat} (h : MmaOff o) : IsObjIn L g (Mma.bl L g o) MmaOff := ⟨o, h, rfl⟩

set_option maxHeartbeats 4000000 in
/-- The MMA warp's polls outside the PV blocks name objects. -/
theorem mma_wt (hp : Pre p L m) {v : Mma.V} {n : Mma.Cnt → Nat} {r : Nat} {w : Bool} (k : Fin 10)
    (hQ : Mma.RefQ p L g (Mma.Site.wt k).ord v n r w) :
    IsObjIn L g (smLoc L g (Mma.wtOp L v k).1 0) MmaOff := by
  fin_cases k <;> simp only [Mma.wtOp, Fin.isValue, Fin.reduceFinMk]
  · rw [Mma.smLoc_sbW hp 0 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [Mma.smLoc_addi hp 32 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [Mma.smLoc_addi hp 8 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [(hQ.regs (by decide)).1, Mma.smLoc_slot hp (by omega)]
    exact mma_bl (by simp only [MmaOff, ObjOff]; omega)
  · rw [Mma.smLoc_addi hp 96 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [(Mma.slot1_eq (hQ.regs (by decide))).1, Mma.smLoc_slot hp (by omega)]
    exact mma_bl (by simp only [MmaOff, ObjOff]; omega)
  · rw [Mma.smLoc_addi hp 104 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [(hQ.regs (by decide)).1, Mma.smLoc_slot hp (by omega)]
    exact mma_bl (by simp only [MmaOff, ObjOff]; omega)
  · rw [Mma.smLoc_addi hp 96 (by decide) (by decide)]; exact mma_bl (by decide)
  · rw [Mma.smLoc_addi hp 104 (by decide) (by decide)]; exact mma_bl (by decide)

theorem mma_cmO (r : Nat) (c : Fin 12) : MmaOff (Mma.cmO r c) := by
  fin_cases c <;> simp only [Mma.cmO, MmaOff, ObjOff] <;> simp <;> omega

/-- **The MMA warp's objects**: its polls and its commits' targets. -/
theorem mma_obj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {d : Mma.D} {n : Mma.Cnt → Nat} {e : Event} {l : Loc} (he : X.get (g, k) = some e)
    (hQ0 : Mma.RefCounts p L g (d, n)) (hev : Mma.Ev p L g d e) (hm : MbarOf e l) :
    IsObjIn L g l MmaOff := by
  obtain ⟨r, w, hQ, -⟩ := hQ0
  obtain ⟨site, v⟩ := d
  cases mma_use hev hm with
  | poll ok hs hl hk =>
    cases site <;> simp only [Progress.isPoll, Bool.false_eq_true] at hs
    · rw [hl]; exact mma_wt hp _ hQ
    · rw [hl]
      exact ⟨_, by split <;> decide, Mma.mw_loc hp _⟩
  | commit c s hs hk hb =>
    simp only at hs
    subst hs
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    obtain ⟨rank, ht⟩ := hm
    rw [commit_target hp hX he ht, hb, Mma.cm_loc hp c (r := r) (fun hc => hQ.regs (by
      fin_cases c <;> simp_all [Mma.Site.ord]))]
    exact ⟨_, mma_cmO r c, rfl⟩

theorem twOff_obj : ∀ t, LdOff (Loader.twOff t) := by decide
theorem taOff_obj : ∀ t, LdOff (Loader.taOff t) := by decide

/-- **The loader warps' objects**: their polls, arrivals and tensor copies' barriers. -/
theorem ld_obj (hp : Pre p L m) {w : Nat} {d : Loader.D} {k A : Nat} {e : Event} {l : Loc}
    (hR : Loader.RefRing p L g w d k A) (hev : Loader.Ev p L g w d e) (hm : MbarOf e l) :
    IsObjIn L g l LdOff := by
  cases ld_use hp hR hev hm with
  | slot _ _ _ _ hl _ | dw _ _ _ hl _ | arrive _ _ _ hl _ =>
    exact ⟨_, by simp only [LdOff, ObjOff]; omega, hl⟩
  | dq _ _ hl _ | da _ _ hl _ => exact ⟨_, by decide, hl⟩
  | tw t _ _ hl _ => exact ⟨_, twOff_obj t, hl⟩
  | ta t _ _ hl _ | tc t _ _ _ _ hl _ _ => exact ⟨_, taOff_obj t, hl⟩


set_option maxHeartbeats 8000000 in
/-- **Every use of an mbarrier names one of the startup's objects, from a role state.** An event
of a lane, fired from a followed state with the table's shape, that names an object and is no
initialization of it is fired from a role state and names an object of `IsObj`. -/
theorem use_obj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread p L g).D} {e : Event} {l : Loc} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hJ : JR p L g σ)
    (hi : (thread p L g).inv σ) (hev : TEv p L g σ e) (hm : MbarOf e l)
    (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ r, σ.1 = .inr r) ∧ IsObj L g l := by
  obtain ⟨σ1, n⟩ := σ
  have hub0 : n .ub = 0 := ub_zero hX he hσ
  rcases σ1 with s | ⟨i, d⟩
  · exact absurd (start_mbar hev hi.2 hm) (fun ⟨c, hc⟩ => hni c hc)
  refine ⟨⟨_, rfl⟩, ?_⟩
  cases i with
  | epilogue => exact epi_obj hev hm
  | correction =>
    rcases hev.1.data_or_vote with h | ⟨_,_,h⟩
    · exact corr_obj h hm
    · obtain ⟨pc,kind⟩ := e
      cases h
      exact hm.elim
  | softmax => exact (soft_obj hev.1 hm).obj fun _ h => h.1
  | stub r =>
    exact (jr_stub hJ).elim
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exfalso
      obtain ⟨pc, kind⟩ := e
      simp only [TEv, Mma.PreEv] at hev
      cases kind <;> (try cases ‹TcKind›) <;> simp only [MbarOf] at hm <;> simp_all
    · have hR : Mma.Ref p L g (.inr ⟨.mma, .inr ⟨(), d⟩⟩, n) :=
        (jr_mma_ref hJ).2
      exact (mma_obj hp hX he (hR hub0).1 hev hm).obj fun _ h => h.1
  | loader b =>
    have hR : LdWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.loader b, d⟩, n) :=
      (jr_loader hJ).2
    have hRing := (hR.2 hub0).1.toRefRing
    rw [← hR.1] at hRing
    exact (ld_obj hp hRing hev hm).obj fun _ h => h.1

end
end PTX.Kernels.TmlFa4Fwd.Proof
