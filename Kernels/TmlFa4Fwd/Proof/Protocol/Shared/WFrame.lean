-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Input
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.Mma.Shape
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Flow.Step.ShapeRegs
public import Lemmas.Kernel.Safety.Classes
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Top.JRLoader
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MemWrite
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.MemWrite
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The write frame of the thread machine below `sb + 316`

Every memory write of a consistent execution that lands in shared memory below `sb + 316` is the
MMA warp's allocation store (`wr_low`): per role, from the role table's shapes and the instruction
at the state,

* the startup, the MMA warp's role and (outside its tensor stores, which write global memory) the
  output warp write no memory;
* the MMA warp's allocation prefix writes only at its address-store state;
* the correction warps' final stores write at `sb + 2848` or above (`Correction.fst_at`), their
  LSE stores in global memory;
* the softmax warps' statistics stores write at `sb + 368` or above (`Softmax.stat_at`);
* the loader warps' local stores write local memory, their row copies at `sb + 68496` or above
  (`Loader.cp_lo`, with the ring slot from `RefRing`), their tensor loads at `sb + 3072` or above
  (the decoded copies' destinations, `input_box`);
* no cluster launch control request is issued (`noClcIssue`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A tensor store writes global memory. -/
theorem tstore_global {s : TensorStore.Spec} {x y k : Nat} {l : Loc}
    (h : TensorStore.writeLoc s x y k = some l) : l.space = .global := by
  unfold TensorStore.writeLoc TensorStore.destination at h
  cases hs : TensorTransfer.slotAt s.descriptor x y k with
  | none => rw [hs] at h; cases h
  | some slot =>
    rw [hs] at h
    simp only [Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h
    rfl

/-- A tensor load writes at or above its shared base. -/
theorem tload_ge {s : TensorCopy.Spec} {x y k : Nat} {l : Loc}
    (h : TensorCopy.writeLoc s x y k = some l) :
    l.space = s.sharedBase.space ∧ s.sharedBase.addr ≤ l.addr := by
  unfold TensorCopy.writeLoc at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨slot, -, rfl⟩ := h
  exact ⟨rfl, Nat.le_add_right _ _⟩

theorem input_off (j : Fin 14) : 3072 ≤ (Loader.inputSite j).sharedOffset := by
  revert j; decide

/-- **The loader warps' tensor loads write at `sb + 3072` or above.** -/
theorem tload_low (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i : EvId} {pc a : Nat} {s : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue a s⟩)
    {x y k : Nat} {l : Loc} (hw : TensorCopy.writeLoc s x y k = some l) :
    L.sharedBase + 3072 ≤ l.addr := by
  obtain ⟨-, j, org, mb, -, rfl⟩ := input_box hp hX hFw he
  obtain ⟨-, hl⟩ := tload_ge hw
  have := input_off j
  simp only [inputSpec] at hl
  omega

/-- The writes of a thread or a linear copy: a store, an atomic with a result, a copy. -/
def WrKind (e : Event) : Prop :=
  (∃ a bs, e.kind = .wr a bs) ∨ (∃ a o n, e.kind = .rmw a o (some n)) ∨ ∃ s, e.kind = .copy s

theorem writeOf_kind {e : Event} {dst : Acc} (hw : WriteOf e dst) :
    WrKind e ∨
    (∃ a s x y k, e.kind = .tensorIssue a s ∧ TensorCopy.writeLoc s x y k = some dst.loc) ∨
    (∃ a s x y k, e.kind = .tensorStore a s ∧ TensorStore.writeLoc s x y k = some dst.loc) ∨
    ∃ s t, e.kind = .clcIssue s t := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [WriteOf] at hw
  all_goals first
    | exact .inl (.inl ⟨_, _, rfl⟩)
    | exact .inl (.inr (.inr ⟨_, rfl⟩))
    | exact .inr (.inr (.inr ⟨_, _, rfl⟩))
    | (obtain ⟨x, y, k, h⟩ := hw; exact .inr (.inr (.inl ⟨_, _, x, y, k, rfl, h⟩)))
    | (obtain ⟨x, y, k, h⟩ := hw; exact .inr (.inl ⟨_, _, x, y, k, rfl, h⟩))
    | (rename_i n
       cases n with
       | none => simp only at hw
       | some n => exact .inl (.inr (.inl ⟨_, _, _, rfl⟩)))

theorem wrKind_cases {e : Event} (hw : WrKind e) :
    ∃ pc, (∃ a bs, e = ⟨pc, .wr a bs⟩) ∨ (∃ a o n, e = ⟨pc, .rmw a o (some n)⟩) ∨
      ∃ s, e = ⟨pc, .copy s⟩ := by
  obtain ⟨pc, kind⟩ := e
  refine ⟨pc, ?_⟩
  rcases hw with ⟨a, bs, hk⟩ | ⟨a, o, n, hk⟩ | ⟨s, hk⟩ <;> simp only at hk <;> subst hk
  · exact .inl ⟨_, _, rfl⟩
  · exact .inr (.inl ⟨_, _, _, rfl⟩)
  · exact .inr (.inr ⟨_, rfl⟩)

/-- The output warp writes memory only by its tensor stores. -/
theorem epi_wr {d : Epilogue.D} {e : Event} (hev : Epilogue.Ev p L g d e) (hw : WrKind e) :
    False := by
  obtain ⟨pc, h⟩ := wrKind_cases hw
  rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;> unfold Epilogue.Ev at hev <;>
    split at hev <;> simp_all [Epilogue.isStore]

/-- The startup writes no memory. -/
theorem start_wr {s : Startup.D} {e : Event} (hev : Startup.Ev L g s e)
    (hx : exit L g s = none) (hw : WrKind e) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, h⟩ := wrKind_cases hw
  rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;>
  · cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx

set_option maxHeartbeats 4000000 in
/-- The MMA warp's role writes no memory. -/
theorem mma_wr {d : Mma.D} {e : Event} (hev : Mma.Ev p L g d e) (hw : WrKind e) : False := by
  obtain ⟨site, v⟩ := d
  unfold Mma.Ev at hev
  split at hev
  all_goals first
    | exact epi_wr hev hw
    | skip
  all_goals obtain ⟨pc, h⟩ := wrKind_cases hw
  all_goals rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;> simp_all

set_option maxHeartbeats 4000000 in
/-- The correction warps write memory only at their final and LSE stores. -/
theorem corr_wr {d : Correction.D} {e : Event} (hev : Correction.Ev p L g d e) (hw : WrKind e) :
    (∃ st j hh, d.site = .fst st j hh) ∨ ∃ hh, d.site = .lse hh := by
  obtain ⟨site, v, k⟩ := d
  unfold Correction.Ev at hev
  split at hev
  all_goals first
    | exact (epi_wr hev hw).elim
    | exact .inl ⟨_, _, _, ‹_›⟩
    | exact .inr ⟨_, ‹_›⟩
    | skip
  all_goals obtain ⟨pc, h⟩ := wrKind_cases hw
  all_goals rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;>
    simp_all [Correction.rdOrUb]

set_option maxHeartbeats 4000000 in
/-- The softmax warps write memory only at their statistics stores. -/
theorem soft_wr {d : Softmax.D} {e : Event} (hev : Softmax.Ev p L g d e) (hw : WrKind e) :
    (∃ pl, d.site = .stat pl) ∨ ∃ k, d.site = .fin k := by
  obtain ⟨site, v, k, ac⟩ := d
  unfold Softmax.Ev at hev
  split at hev
  all_goals first
    | exact (epi_wr hev hw).elim
    | exact .inl ⟨_, ‹_›⟩
    | exact .inr ⟨_, ‹_›⟩
    | skip
  all_goals obtain ⟨pc, h⟩ := wrKind_cases hw
  all_goals rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;>
    (try split at hev) <;> simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 4000000 in
/-- The loader warps write shared memory only by their row copies. -/
theorem ld_wr {w : Nat} {d : Loader.D} {e : Event} (hev : Loader.Ev p L g w d e) (hw : WrKind e)
    {dst : Acc} (hwo : WriteOf e dst) (hsh : dst.loc.space = .shared) :
    ∃ per b i c, d.site = .cp per b i c ∧
      dst.loc = smLoc L g (Loader.rv p L g w d (Loader.cpDst (Loader.pk per b) i c).1)
        (Loader.cpDst (Loader.pk per b) i c).2 := by
  obtain ⟨site, v, kk⟩ := d
  obtain ⟨pc, h⟩ := wrKind_cases hw
  rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩
  · exfalso
    simp only [WriteOf] at hwo
    subst hwo
    unfold Loader.Ev at hev
    split at hev
    all_goals first
      | exact (epi_wr hev hw).elim
      | skip
    all_goals simp_all [Loader.lacc, Loc.at]
    all_goals obtain ⟨_, -, rfl, -⟩ := hev
    all_goals simp at hsh
  · exfalso
    unfold Loader.Ev at hev
    split at hev
    all_goals first
      | exact (epi_wr hev hw).elim
      | simp_all
  · cases site
    case cp per b i c =>
      refine ⟨per, b, i, c, rfl, ?_⟩
      simp only [Loader.Ev] at hev
      rcases hev with ⟨n, hk⟩ | ⟨f, hk⟩ <;> simp only [Kind.copy.injEq, reduceCtorEq] at hk
      subst hk
      simp only [WriteOf] at hwo
      rcases hwo with ⟨-, rfl⟩ | ⟨j, hj⟩
      · rfl
      · simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets] at hj
    all_goals exfalso
    all_goals unfold Loader.Ev at hev
    all_goals first
      | exact epi_wr hev hw
      | simp_all

set_option maxHeartbeats 8000000 in
/-- **A thread write or linear copy that lands in shared memory below `sb + 316` is the MMA warp's
allocation store**: it is fired from the allocation prefix's address-store state. -/
theorem wr_low (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {σ : (thread p L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hJ : JR p L g σ)
    (hev : TEv p L g σ e) (hw : WrKind e) {dst : Acc} (hwo : WriteOf e dst)
    (hsh : dst.loc.space = .shared) :
    (∃ n, σ = (.inr ⟨.mma, .inl .wr⟩, n)) ∨ L.sharedBase + 316 ≤ dst.loc.addr := by
  obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by
      obtain ⟨pc,h⟩ := wrKind_cases hw
      rcases h with ⟨_,_,rfl⟩ | ⟨_,_,_,rfl⟩ | ⟨_,rfl⟩ <;> exact fun _ => nofun)
  obtain ⟨σ1, n⟩ := σ
  have hub0 : n .ub = 0 := ub_zero hX he hσ
  have hkd : ∀ a bs, e.kind = .wr a bs → dst = a := fun a bs hk => by
    obtain ⟨pc, kind⟩ := e
    simp only at hk
    subst hk
    exact hwo
  rcases σ1 with s | ⟨i, d⟩
  · exact (start_wr hev hi.2 hw).elim
  cases i with
  | epilogue => exact (epi_wr hev hw).elim
  | mma =>
    rcases d with s0 | ⟨⟨⟩, d⟩
    · have hk3 := Mma.pre_kind hp hat hc hf
      cases s0 with
      | set =>
        exfalso
        obtain ⟨inst, hki⟩ := hk3.1 rfl
        obtain ⟨pc, h⟩ := wrKind_cases hw
        rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;> cases hki
      | alloc =>
        exfalso
        have hki := hk3.2.1 rfl
        obtain ⟨pc, h⟩ := wrKind_cases hw
        rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩ <;> cases hki
      | wr => exact .inl ⟨n, rfl⟩
      | enter => exact absurd hi.2 (by simp [Mma.Start.exit])
    · exact (mma_wr hev hw).elim
  | correction =>
    right
    obtain ⟨pc, h⟩ := wrKind_cases hw
    have hEv := hev.1.data_or_vote.resolve_right (by
      rintro ⟨_,_,hv⟩
      rcases h with ⟨_,_,rfl⟩ | ⟨_,_,_,rfl⟩ | ⟨_,rfl⟩ <;> cases hv)
    rcases corr_wr hEv hw with hs | hs
    · rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩
      · rw [hkd a bs rfl]
        obtain ⟨st, j, hh, hs⟩ := hs
        obtain ⟨-, q, -, w, -, hl⟩ := Correction.fst_at hp hat hc hf hs rfl
        rw [hl]
        simp only
        omega
      · exfalso
        have := hEv
        obtain ⟨site, v, kk⟩ := d
        obtain ⟨st, j, hh, hs⟩ := hs
        change site = _ at hs
        subst hs
        simp [Correction.Control.D.scheduler, Correction.Ev] at this
      · exfalso
        have := hEv
        obtain ⟨site, v, kk⟩ := d
        obtain ⟨st, j, hh, hs⟩ := hs
        change site = _ at hs
        subst hs
        simp [Correction.Control.D.scheduler, Correction.Ev] at this
    · rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩
      · rw [hkd a bs rfl] at hsh
        rw [Correction.lse_wr hat hc hf hs rfl] at hsh
        cases hsh
      · exfalso
        have := hEv
        obtain ⟨site, v, kk⟩ := d
        obtain ⟨hh, hs⟩ := hs
        change site = _ at hs
        subst hs
        simp [Correction.Control.D.scheduler, Correction.Ev] at this
      · exfalso
        have := hEv
        obtain ⟨site, v, kk⟩ := d
        obtain ⟨hh, hs⟩ := hs
        change site = _ at hs
        subst hs
        simp [Correction.Control.D.scheduler, Correction.Ev] at this
  | softmax =>
    right
    obtain ⟨pc, h⟩ := wrKind_cases hw
    have hs := soft_wr hev.1 hw
    rcases h with ⟨a, bs, rfl⟩ | ⟨a, o, n, rfl⟩ | ⟨s, rfl⟩
    · rw [hkd a bs rfl]
      obtain ⟨-, n', -, hl⟩ := Softmax.stat_at hp (d := d.scheduler) hat (by
        rcases hs with ⟨pl,h⟩ | ⟨j,h⟩ <;> change d.site = _ at h <;>
          have hi0 := hi.1 <;> change Softmax.Control.Inv d at hi0 <;>
          simpa only [Softmax.Control.Inv, h, Softmax.Control.D.scheduler] using hi0) hc hf hs rfl
      rw [hl]
      simp only
      omega
    all_goals exfalso
    all_goals have := hev.1
    all_goals obtain ⟨site, v, kk, ac⟩ := d
    all_goals rcases hs with ⟨pl, hs⟩ | ⟨j, hs⟩ <;> change site = _ at hs <;> subst hs <;>
      simp [Softmax.Control.D.scheduler, Softmax.Ev] at this
  | loader b =>
    right
    have hR : LdWarp.Ref p L (Prologue.warpIndex L g) g (.inr ⟨.loader b, d⟩, n) :=
      (jr_loader hJ).2
    have hRing := (hR.2 hub0).1.toRefRing
    rw [← hR.1] at hRing
    obtain ⟨per, bb, i, c, hs, hl⟩ := ld_wr hev hw hwo hsh
    obtain ⟨site, v, k2⟩ := d
    simp only at hs
    subst hs
    rw [hl]
    exact (Loader.cp_lo hp hRing).1.trans' (by omega)
  | stub r =>
    exact (jr_stub hJ).elim

end
end PTX.Kernels.TmlFa4Fwd.Proof
