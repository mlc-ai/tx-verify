-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Def
public import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Own
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Drain
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Commits
import Kernels.TmlFa4Fwd.Proof.Protocol.Life.Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Dealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Word
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Words
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.StoreWarp
import Lemmas.Kernel.ExitChain
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.Region
import Lemmas.Protocol.RegionOrder
import Lemmas.Step.BulkWaitReady
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every use of a CTA's shared memory ends before the CTA exits

Every use is of the issuing lane's CTA (`Own.lean`), so no use needs another CTA to have started.
A thread instruction precedes its lane's exit. An MMA's completion is observed by a correction
lane's poll before that lane's exit (`mma_observer`, `mma_finished`). A tensor store's source reads
are observed by its lane's read wait (`store_finished`). The S and O commits' arrive-ons are
observed by the softmax and correction lanes (`Life/Commits.lean`). The tensor loads, the row copies
and their arrive-ons, and the empty barriers' commits are the channels' (`Life/Def.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Life
open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **An MMA's completion precedes an exit of its CTA**, once the CTA exited. -/
theorem mma_finished {i : EvId} (hi : Tmem1.IsMma X i) (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i .mmaDone) (i.1 / L.block) := by
  have hb := hp.block
  obtain ⟨d0, s0, acc0, mask0, pc0, he0⟩ := id hi
  have hg : i.1 < L.threads := Frame.lt_of_get hX (k := i.2) he0
  -- a lane of the CTA's MMA warp made its deallocation
  have hz : i.1 / L.block * L.block + 384 < L.threads := by
    unfold Launch.threads at hg ⊢
    rw [hb] at hg ⊢
    omega
  have hzc : (i.1 / L.block * L.block + 384) / L.block = i.1 / L.block := by rw [hb]; omega
  obtain ⟨pcx, hxz⟩ := exit_of_exited hx hz hzc
  have hto := tmem1Facts hp hX hFw
  have h3 := hto.exit hz (by rw [hb]; omega) hxz
  obtain ⟨j, ev, hj, hev, hq, hcnt⟩ := exists_nth Tmem.Pair.isTmemOp
    (X.tr (i.1 / L.block * L.block + 384)) (n := 2)
    (k := (X.tr (i.1 / L.block * L.block + 384)).length - 1) (by
      change _ < Tmem.Pair.tmemOps _; omega)
  obtain ⟨pcd, grp, dst, act, rfl⟩ := Tmem.Pair.tmemOp_resource hq
  have hsh := (hto.toTmem1Ops.event hz hev).2.2
  rw [show Tmem.Pair.tmemOps _ = 2 from hcnt] at hsh
  obtain ⟨base, rfl⟩ := hsh
  obtain ⟨h, k, pck, l, par, hh, hhc, hget, hobs, -⟩ := mma_observer hp hX hFw hi
    (d := (i.1 / L.block * L.block + 384, j)) hev hzc
  obtain ⟨pch, hxh⟩ := exit_of_exited hx hh hhc
  obtain ⟨hk, hl⟩ := before_exit hget (by simp) hxh
  obtain ⟨ex, hspin⟩ := poll_spin hX _ _ _ _ _ _ hget
  have hres : Resumes kernel X (h, k) (h, (X.tr h).length - 1) :=
    Resumes.of_spin hget hspin rfl hk hl
  obtain ⟨hd, hcb⟩ := CompletedBefore.of_observesMma hX.tcCommit hobs
    (.single (DepStep.of_resumes L hres))
  exact SharedFinished.of_completedBefore (finish := (h, (X.tr h).length - 1)) hd
    ⟨hh, hhc, pch, hxh⟩ hcb

/-- **A tensor store's source reads precede its lane's exit.** -/
theorem store_finished {i : EvId} {a : Nat} {s : TensorStore.Spec} (hi : X.TensorStoreIssue i a s)
    (hx : CtaExited L X (i.1 / L.block)) :
    SharedFinished L kernel Assumptions.all X (.async i .readsDone) (i.1 / L.block) := by
  obtain ⟨g, k⟩ := i
  obtain ⟨pc, he⟩ := hi
  have hg : g < L.threads := Frame.lt_of_get hX he
  obtain ⟨pcx, hxg⟩ := exit_of_exited hx hg rfl
  obtain ⟨w, pcw, hwl, hwt, hwait⟩ :=
    Epilogue.store_wait hp hX (store_warp hp hX hFw ⟨pc, he⟩) he hxg
  have hq : Part.readsDone ∈ GroupWaitStages X (g, k) (.bulk .read) := by
    simp [GroupWaitStages, he]
  have hpres : X.AsyncPresent (g, k) .readsDone :=
    Step.BulkWait.stages_of_returned hX hwait (by simpa using hwl) _ hq
  obtain ⟨hkx, hl⟩ := before_exit hwt (by simp) hxg
  exact SharedFinished.of_observer_exit (finish := (g, (X.tr g).length - 1)) hpres
    (Step.BulkWait.witness_of_waitsFor hwait hq hpres)
    (Resumes.of_blocking hwt (b := false) rfl ⟨rfl, hkx, hl⟩) ⟨hg, rfl, _, hxg⟩

/-- **Every use of a CTA's shared memory** is of the issuer's CTA and precedes an exit of an exited
CTA. -/
theorem use_ok (hload : LoadsFinished L kernel Assumptions.all X)
    (hrow : RowsFinished L kernel Assumptions.all X)
    (harr : ArrivesFinished L kernel Assumptions.all X)
    (hempty : EmptiesFinished L kernel Assumptions.all X) {e : Ref} {c : Nat}
    (huse : SharedUse L X e c) : c = e.issuer.1 / L.block ∧
      (CtaExited L X c → SharedFinished L kernel Assumptions.all X e c) := by
  have hmb : ∀ {i : EvId} {ev : Event} {l : Loc}, X.get i = some ev → Frame.MbarOf ev l →
      (∀ f, ev.kind ≠ .ub f) → l.cta = i.1 / L.block := fun he hm hu => mbar_own hX hp hFw he hm hu
  have hmma : ∀ {i : EvId} {d : Nat} {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat},
      X.MmaIssue i d s acc mask → s.lowCta = i.1 / L.block ∧ s.highCta = i.1 / L.block := by
    intro i d s acc mask hi
    obtain ⟨-, hs, -⟩ := Tm.mma_acc_at hp hX hFw hi
    exact ⟨hs.low, hs.high⟩
  have hbulk : ∀ i a, ¬ X.BulkPrefetch i a := fun _ _ => no_bulkPrefetch hX
  have hclc : ∀ i s tg, ¬ X.ClcIssue i s tg := fun _ _ _ => no_clc hX
  have hcp : ∀ i cp, ¬ X.CpIssue i cp := (Tm.scoreFacts hp hX hFw).no_cp
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, q, rfl, hfin, hsu⟩
  · -- an access of shared memory
    rcases e with i | ⟨i, q⟩
    · have hown : c = i.1 / L.block := hcta ▸ access_own hX hint hsp
      exact ⟨hown, fun hx => SharedFinished.of_access hX.outside hint hown.symm hx⟩
    · cases q with
      | mmaRead isB idx =>
        obtain ⟨-, -, hfp⟩ := hint
        rcases hfp with ⟨d, sp, acc, mask, hmi, hbl⟩ | ⟨c', k', cta, hcpi, -⟩
        · have hlh := TcMma.OperandSpec.byteLoc_cta hbl
          obtain ⟨h1, h2⟩ := hmma hmi
          have hown : c = i.1 / L.block := by
            rw [← hcta]
            rcases hlh with h | h <;> rw [h] <;> assumption
          refine ⟨hown, fun hx => ?_⟩
          rw [hown] at hx ⊢
          have hf := mma_finished hp hX hFw ⟨d, sp, acc, mask, hmi⟩ hx
          exact SharedFinished.of_stage (j := i) (q := .mmaDone) hpres
            (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
        · exact (hcp _ _ hcpi).elim
      | readStore x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        have hb := store_own hX hti
        simp only [TensorStore.readLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, -, hl⟩ := hl
        have hown : c = i.1 / L.block := by rw [← hcta, ← hl, ← hb]; rfl
        refine ⟨hown, fun hx => ?_⟩
        rw [hown] at hx ⊢
        have hf := store_finished hp hX hFw hti hx
        exact SharedFinished.of_stage (j := i) (q := .readsDone) hpres
          (.inr ⟨rfl, rfl, rfl, hpres, hf.1⟩) hf
      | readLoad x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.tensor_readLoc_global hl] at hsp
        cases hsp
      | readPrefetch x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [TensorTransfer.sourceLoc_global hl] at hsp
        cases hsp
      | readCopy =>
        obtain ⟨-, ⟨s, hcopy, rfl⟩ | hb⟩ := hint
        · obtain ⟨-, h2, -⟩ := copy_own hX hcopy
          rw [h2] at hsp
          cases hsp
        · exact (hbulk _ _ hb).elim
      | writeStore x y k =>
        obtain ⟨-, sp, addr, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | oldStore x y k =>
        obtain ⟨-, sp, addr, -, -, hl, -⟩ := hint
        rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      | writeLoad x y k =>
        obtain ⟨-, sp, addr, hti, hl, -⟩ := hint
        have hb := (load_own hX hp hti).1
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hl
        obtain ⟨slot, hslot, hl⟩ := hl
        have hown : c = i.1 / L.block := by rw [← hcta, ← hl, ← hb]; rfl
        refine ⟨hown, fun hx => ?_⟩
        rw [hown] at hx ⊢
        exact (hload _ _ _ hti hx).1 x y k (by simp [hslot])
      | writeCta c' =>
        obtain ⟨-, s, tg, hcl, -⟩ := hint
        exact (hclc _ _ _ hcl).elim
      | writeCopy =>
        obtain ⟨-, s, hcopy, -, rfl⟩ := hint
        obtain ⟨-, -, -, h4, -⟩ := copy_own hX hcopy
        have hown : c = i.1 / L.block := by rw [← hcta, h4]
        refine ⟨hown, fun hx => ?_⟩
        rw [hown] at hx ⊢
        exact hrow _ _ hcopy hx
      | writeElem j =>
        obtain ⟨-, s, hcopy, hel⟩ := hint
        obtain ⟨-, -, -, -, h5⟩ := copy_own hX hcopy
        simp [AsyncCopy.Spec.elems, AsyncCopy.Spec.elemOffsets, h5] at hel
      | oldElem j =>
        obtain ⟨-, s, r, hcopy, hw, -⟩ := hint
        obtain ⟨-, -, -, -, h5⟩ := copy_own hX hcopy
        rw [h5] at hw
        cases hw
      | _ => exact hint.2.elim
  · -- an action on an mbarrier
    have hsrc := objectAction_source (r := (⟨e, act, { state := none }, none⟩ : Record Ref)) hact
    cases hsrc with
    | @init g j pc n hid he ha' =>
      subst hid
      have hown : c = g / L.block := hmb he rfl (fun f h => by cases h)
      exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
        hown.symm hx⟩
    | @inval g j pc hid he ha' =>
      subst hid
      have hown : c = g / L.block := hmb he rfl (fun f h => by cases h)
      exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
        hown.symm hx⟩
    | @arrive g j pc tx n rel sc hid he ha' =>
      subst hid
      have hown : c = g / L.block := hmb he rfl (fun f h => by cases h)
      exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
        hown.symm hx⟩
    | @wait g j pc q ok acq sc hid he ha' =>
      subst hid
      have hown : c = g / L.block := hmb he rfl (fun f h => by cases h)
      exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
        hown.symm hx⟩
    | @increment g j pc hid he ha' =>
      subst hid
      have hown : c = g / L.block := hmb he rfl (fun f h => by cases h)
      exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
        hown.symm hx⟩
    | @tensor i pc a sp hid he hm ha' =>
      subst hid
      have hown : c = i.1 / L.block := by
        have := (load_own hX hp ⟨pc, he⟩).2
        rw [hm] at this
        exact this
      refine ⟨hown, fun hx => ?_⟩
      rw [hown] at hx ⊢
      exact (hload _ _ _ ⟨pc, he⟩ hx).2
    | @arriveOn i pc m' noinc hid he hm hn ha' =>
      subst hid
      have hown : c = i.1 / L.block := hmb he (l := ⟨.shared, c, addr⟩) hm.symm
        (fun f h => by cases h)
      refine ⟨hown, fun hx => ?_⟩
      rw [hown] at hx ⊢
      exact harr _ _ _ ⟨pc, he⟩ hn hx
    | @bulk i pc s hid he hc hn ha' =>
      subst hid
      have h1 := (copy_own hX ⟨pc, he⟩).1
      rw [hc] at h1
      cases h1
    | @commit i pc sp rank hid he htg ha' =>
      subst hid
      have hown : c = i.1 / L.block := hmb he (l := ⟨.shared, c, addr⟩) ⟨rank, htg⟩
        (fun f h => by cases h)
      refine ⟨hown, fun hx => ?_⟩
      rw [hown] at hx ⊢
      exact commit_finished hp hX hFw hempty ⟨pc, he⟩ htg hx
    | @clc i pc sp tg c' hid he hm htg ha' => exact (hclc _ _ _ ⟨pc, he⟩).elim
  · -- a commit's issue
    obtain ⟨pc, he⟩ := hc
    have hown : c = i.1 / L.block := cluster_eq hp hgrp.1
    exact ⟨hown, fun hx => SharedFinished.of_thread hX.outside he (fun _ h => by cases h)
      hown.symm hx⟩
  · -- a tensor load's write
    have hown : c = i.1 / L.block := by rw [← hcta]; exact (load_own hX hp hi).1
    refine ⟨hown, fun hx => ?_⟩
    rw [hown] at hx ⊢
    exact (hload _ _ _ hi hx).1 x y k hsl
  · -- a tensor store's source reads
    have hown : c = i.1 / L.block := by rw [← hcta]; exact store_own hX hi
    refine ⟨hown, fun hx => ?_⟩
    rw [hown] at hx ⊢
    exact store_finished hp hX hFw hi hx
  · -- the final stage of an operation
    rcases hfin with ⟨s, l, hcopy, hcm, rfl⟩ | ⟨s, hcopy, -, rfl⟩ |
        ⟨l, noinc, -, rfl⟩ | ⟨-, rfl⟩ | ⟨s, tg, c', hcl, -, rfl⟩ |
        ⟨a, s, -, rfl⟩ | ⟨a, s, -, rfl⟩ | ⟨s, rank, l, -, -, rfl⟩
    · have h1 := (copy_own hX hcopy).1
      rw [hcm] at h1
      cases h1
    · obtain ⟨s', hcopy', -, hd | hd⟩ := hsu
      · obtain ⟨-, -, -, h4, -⟩ := copy_own hX hcopy'
        have hown : c = i.1 / L.block := by rw [← hd.2, h4]
        refine ⟨hown, fun hx => ?_⟩
        rw [hown] at hx ⊢
        exact hrow _ _ hcopy' hx
      · obtain ⟨-, h2, -⟩ := copy_own hX hcopy'
        rw [h2] at hd
        cases hd.1
    · exact hsu.elim
    · rcases hsu with ⟨d, s, acc, mask, hmi, hlh⟩ | ⟨cp, hcpi, -⟩
      · obtain ⟨h1, h2⟩ := hmma hmi
        have hown : c = i.1 / L.block := by rcases hlh with h | h <;> rw [h] <;> assumption
        refine ⟨hown, fun hx => ?_⟩
        rw [hown] at hx ⊢
        exact mma_finished hp hX hFw ⟨d, s, acc, mask, hmi⟩ hx
      · exact (hcp _ _ hcpi).elim
    · exact (hclc _ _ _ hcl).elim
    · obtain ⟨address, s, hti, -, hcta⟩ := hsu
      have hown : c = i.1 / L.block := by rw [← hcta]; exact (load_own hX hp hti).2
      refine ⟨hown, fun hx => ?_⟩
      rw [hown] at hx ⊢
      exact (hload _ _ _ hti hx).2
    · exact hsu.elim
    · obtain ⟨s, l, ⟨pc, he⟩, htg, hcta⟩ := hsu
      have hown : c = i.1 / L.block := by
        rw [← hcta]
        exact hmb he ⟨rank, htg⟩ (fun f h => by cases h)
      refine ⟨hown, fun hx => ?_⟩
      rw [hown] at hx ⊢
      exact commit_finished hp hX hFw hempty ⟨pc, he⟩ htg hx

/-- **No use of a CTA's shared memory is unsafe**, from the channels' ends of their uses. -/
theorem no_sharedLifetimeUnsafe (hload : LoadsFinished L kernel Assumptions.all X)
    (hrow : RowsFinished L kernel Assumptions.all X)
    (harr : ArrivesFinished L kernel Assumptions.all X)
    (hempty : EmptiesFinished L kernel Assumptions.all X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X := by
  rintro ⟨e, owner, huse, ⟨h1, -⟩ | ⟨h3, h4⟩⟩
  · exact h1 (use_ok hp hX hFw hload hrow harr hempty huse).1
  · exact h4 ((use_ok hp hX hFw hload hrow harr hempty huse).2 h3)

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Life
