-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mbar
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Life.Def
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.Kinds
public import Lemmas.Kernel.Safety.Lifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Place
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaLayout
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsync
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticAsyncRef
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Foot
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.TmemRace.Writers
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Gather
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Mem
import Lemmas.Protocol.ObjectSource
import Lemmas.Protocol.Region

@[expose] public section

/-! # Every use of a CTA's shared memory is of the issuer's CTA

`life_own`: each of the six forms of `SharedUse` (an access, an action on an mbarrier, a commit's
issue, a tensor load's write, a tensor store's read, the completing stage of an operation) names
the CTA of the issuing lane. -/

/-! # A lane uses the shared memory of its own CTA

The clusters have one CTA (`Pre.clusterSize`), so a commit's group, a tensor load's destination
and mbarrier, a tensor store's source and an mbarrier an event names are of the issuing lane's
CTA. A shared access is of the lane's CTA by `access_place`; an asynchronous one by
`async_below`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A CTA of the cluster of a CTA is that CTA** (clusters have one CTA). -/
theorem life_cluster_eq (hp : Pre P L m) {c owner : Nat} (h : CtaInCluster L c owner) :
    owner = c := by
  have hSize (k : Nat) : L.clusterSizeAt k = L.clusterSize.val := by
    simp [Launch.clusterSizeAt, hp.clusterPlaces, gridPlace, Dim3.prod, hp.clusterSize]
  have hc := h.2.2
  simp only [Launch.clusterOfCta, Launch.locate_regular hSize, hp.clusterSize, Nat.div_one,
    Nat.zero_add] at hc
  exact hc.symm

/-- **A named mbarrier is of the naming lane's CTA** (`mbar_use`, `use_cta`). -/
theorem life_mbar_own (hR : MbarRows P L X) {g k : Nat} {e : Event} {l : Loc}
    (hg : g < L.threads) (he : X.get (g, k) = some e) (hm : Frame.MbarOf e l) :
    l.cta = g / L.block := by
  obtain ⟨f, rfl⟩ := use_cta (mbar_use hR hg he hm)
  rfl

/-- **A tensor load's mbarrier is of its lane's CTA.** -/
theorem life_load_mbar (hR : MbarRows P L X) {g k a : Nat} {s : TensorCopy.Spec}
    (hg : g < L.threads) (h : X.TensorIssue (g, k) a s) : s.mbar.cta = g / L.block := by
  obtain ⟨pc, he⟩ := h
  exact life_mbar_own hR hg he rfl

/-- **A written byte of a tensor load is of its lane's CTA.** -/
theorem life_load_byte (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k a : Nat} {s : TensorCopy.Spec} (h : X.TensorIssue (g, k) a s)
    {x y j : Nat} {b : Loc} (hl : TensorCopy.writeLoc s x y j = some b) :
    b.cta = g / L.block := by
  obtain ⟨pc, he⟩ := h
  have hpc : 1850 ≤ pc ∧ pc < 2332 := load_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inl ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · simp only [Wg0At] at h; omega
  · simp only [Wg1At] at h; omega
  · exact ((memRow_mmaLoad hp hX hFw (Frame.lt_of_get hX he) he h rfl).2 hl).2.1
  · obtain ⟨r, hr⟩ := tma_gather_raw hp hX hFw he h rfl hl
    exact hr.2.1
  · simp only [IndexAt] at h; omega
  · simp only [DequantAt] at h; omega

/-- **A tensor load with a slot has its destination in its lane's CTA.** -/
theorem life_load_base (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k a : Nat} {s : TensorCopy.Spec} (h : X.TensorIssue (g, k) a s)
    {x y j : Nat} (hsl : (TensorTransfer.slotAt s.descriptor x y j).isSome) :
    s.sharedBase.cta = g / L.block := by
  obtain ⟨slot, hs⟩ := Option.isSome_iff_exists.mp hsl
  have hl : TensorCopy.writeLoc s x y j = some (s.sharedLoc slot) := by
    simp [TensorCopy.writeLoc, hs]
  have hb := life_load_byte hp hX hFw h hl
  exact hb

/-- **A tensor store's source is in its lane's CTA.** -/
theorem life_store_base (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k a : Nat} {s : TensorStore.Spec}
    (h : X.TensorStoreIssue (g, k) a s) : s.sharedBase.cta = g / L.block := by
  obtain ⟨pc, he⟩ := h
  have hpc : 103 ≤ pc ∧ pc < 1842 := store_pc hX he rfl
  rcases tensor_place hp hX hFw he (.inr ⟨a, s, rfl⟩) with h | h | h | h | h | h | h
  · simp only [StartupAt] at h; omega
  · obtain ⟨c, -, -, hb, -⟩ := wg0_tensorStore_src hp hX hFw he h rfl
    rw [hb]
    rfl
  all_goals
    simp only [Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h
    omega

/-- **An MMA of the code names its own CTA twice** (`cta_group::1` in single-CTA clusters). -/
theorem life_mma_cta (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) {g k d : Nat}
    {s : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : X.MmaIssue (g, k) d s acc mask) : s.lowCta = g / L.block ∧ s.highCta = g / L.block := by
  obtain ⟨hgr, ctas, hc, hlo, hhi⟩ := mmaOwnership hX hi
  have hg := Frame.lt_of_get hX hi.choose_spec
  have hb : 0 < L.block := by rw [hp.block]; decide
  have hlt : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).2 hg
  rw [hgr, ctaGroup_self hp hlt] at hc
  cases hc
  simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hlo hhi
  exact ⟨hlo.symm, hhi.symm⟩

/-- **A `tcgen05.cp` names its own CTA** (the Tensor Memory rows). -/
theorem life_cp_ctas (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {c : TcCopy.Spec} (hi : X.CpIssue (g, k) c) :
    c.ctas = [g / L.block] := by
  obtain ⟨pc, he⟩ := hi
  have hg := Frame.lt_of_get hX he
  rcases TmRace.tc_role (tmem_rows hp hX hFw) hg he rfl with ⟨-, hW⟩ | ⟨hat, hM⟩ |
    ⟨_, _, _, hc'⟩
  · rcases hW with h | h | h | h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨-, _, _, h⟩ <;> cases h
  · rcases hM with h | ⟨s', k, hk, hpc, h, hsh, -, ha, hctas⟩ | ⟨_, h, -⟩ |
      ⟨_, _, -, -, h, -⟩ | ⟨_, _, _, -, -, h, -⟩ <;> cases h
    have hb : 0 < L.block := by rw [hp.block]; decide
    rw [ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)] at hctas
    exact (Option.some.inj hctas).symm
  · cases hc'

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
open PTX PTX.Flow PTX.AsyncCopy

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

private theorem shRef_size {i : EvId} {p : AsyncCopy.Part} {a : Acc} (h : AsyncShRef X i p a) :
    a.size = 1 := by
  rcases h with ⟨_, _, _, h, _⟩ | ⟨_, _, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, _, h⟩ <;>
    exact h

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X)
include hp hX hFw hR

/-- **Every use of shared memory is of the issuing lane's CTA.** -/
theorem life_own {e} {c : Nat} (huse : SharedUse L X e c) : c = e.issuer.1 / L.block := by
  have hmb : ∀ {i : EvId} {ev : Event} {l : Loc}, X.get i = some ev → Frame.MbarOf ev l →
      l.cta = i.1 / L.block := fun he hm => life_mbar_own hR (Frame.lt_of_get hX he) he hm
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, q, rfl, hfin, hsu⟩
  · rcases e with i | ⟨i, q⟩
    · rcases access_place hp hX hFw hint with hg | ⟨-, hc, -, -⟩
      · rw [hg] at hsp
        cases hsp
      · exact hcta.symm.trans hc
    · rcases async_ref hX hint with hr | ⟨x, y, k, s, addr, -, -, hl, -⟩ |
        ⟨x, y, k, s, addr, -, -, hl, -⟩
      · have hcov : a.Covers a.loc := ⟨rfl, rfl, Nat.le_refl _, by have := shRef_size hr; omega⟩
        exact hcta.symm.trans (async_below hp hX hFw hint hcov hsp).1
      · rw [Execution.store_writeLoc_global hl] at hsp
        cases hsp
      · rw [Execution.tensor_readLoc_global hl] at hsp
        cases hsp
  · have hsrc := objectAction_source (r := (⟨e, act, { state := none }, none⟩ :
      MBarrier.Record _)) hact
    cases hsrc with
    | @init g j pc n hid he ha' => subst hid; exact hmb he rfl
    | @inval g j pc hid he ha' => exact (no_inval hX hR _ _ ⟨pc, he⟩).elim
    | @arrive g j pc tx n rel sc hid he ha' => subst hid; exact hmb he rfl
    | @wait g j pc q ok acq sc hid he ha' => subst hid; exact hmb he rfl
    | @increment g j pc hid he ha' => exact (no_asyncArrive hX hR he).elim
    | @tensor i pc a sp hid he hm ha' =>
      subst hid
      have h := life_load_mbar hR (Frame.lt_of_get hX he) ⟨pc, he⟩
      rw [hm] at h
      exact h
    | @arriveOn i pc m' noinc hid he hm hn ha' => exact (no_asyncArrive hX hR he).elim
    | @bulk i pc s hid he hc hn ha' => exact (no_copy hX hR he hc).elim
    | @commit i pc sp rank hid he htg ha' =>
      subst hid
      exact hmb he ⟨rank, htg⟩
    | @clc i pc sp tg c' hid he hm htg ha' => exact (no_clc hX hR he htg).elim
  · exact (life_cluster_eq hp hgrp.1).symm ▸ rfl
  · exact hcta.symm.trans (life_load_base hp hX hFw hi hsl)
  · exact hcta.symm.trans (life_store_base hp hX hFw hi)
  · rcases hfin with ⟨s, l, hcopy, hcm, rfl⟩ | ⟨s, hcopy, -, rfl⟩ | ⟨l, noinc, hao, rfl⟩ |
      ⟨-, rfl⟩ | ⟨s, tg, c', hcl, -, rfl⟩ | ⟨a, s, hti, rfl⟩ | ⟨a, s, -, rfl⟩ |
      ⟨s, rank, l, hcm, htg, rfl⟩
    · exact (noCopy hX hcopy).elim
    · exact (noCopy hX hcopy).elim
    · exact (noAsyncArrive hX hao).elim
    · rcases hsu with ⟨d, s, acc, mask, hmi, hlh⟩ | ⟨cp, hcpi, hc⟩
      · obtain ⟨g, k⟩ := i
        obtain ⟨h1, h2⟩ := life_mma_cta hp hX hmi
        rcases hlh with h | h
        · exact h.trans h1
        · exact h.trans h2
      · obtain ⟨g, k⟩ := i
        rw [life_cp_ctas hp hX hFw hcpi, List.mem_singleton] at hc
        exact hc
    · exact (noClcIssue hX hcl).elim
    · obtain ⟨address, s', hti', -, hcta⟩ := hsu
      obtain ⟨g, k⟩ := i
      exact hcta.symm.trans (life_load_mbar hR (Frame.lt_of_get hX hti'.choose_spec) hti')
    · exact hsu.elim
    · obtain ⟨s', m', ⟨pc, he⟩, htg', hcta⟩ := hsu
      exact hcta.symm.trans (hmb he ⟨rank, htg'⟩)

omit hp hFw hR in
/-- **A tensor load's destination byte finishes with its arrival.** -/
private theorem load_byte_finished {i : EvId} {address x y k : Nat} {sp : TensorCopy.Spec}
    (hi : X.TensorIssue i address sp) (hSlot : (TensorTransfer.slotAt sp.descriptor x y k).isSome)
    {c : Nat} (hn : SharedFinished L kernel Assumptions.all X (.async i (.notify .load)) c) :
    SharedFinished L kernel Assumptions.all X (.async i (.write (.load x y k))) c := by
  obtain ⟨o, ho, hnote⟩ := hn.1
  obtain ⟨⟨mapAddr, hi'⟩, hCopy, _⟩ := hX.tensor i o ho
  have hSpec := (Kind.tensorIssue.inj (congrArg Event.kind
    (Option.some.inj (hi.choose_spec.symm.trans hi'.choose_spec)))).2
  rw [hSpec] at hSlot
  obtain ⟨slot, hs⟩ := Option.isSome_iff_exists.mp hSlot
  obtain ⟨value, hv⟩ := hCopy.complete hnote slot
  have hp : X.AsyncPresent i (.write (.load x y k)) := ⟨o, slot, value, ho, hs, hv⟩
  exact SharedFinished.of_stage (j := i) (q := .notify .load) hp
    (.inr ⟨rfl, rfl, rfl, rfl, hp, hn.1⟩) hn

/-- **Every asynchronous use finishes before an exit of an exited CTA**, from the completion of
the loads' arrivals, the MMAs, the commits' arrivals and the stores' source reads. -/
theorem life_async (hld : LoadNotified L kernel Assumptions.all X)
    (hmma : MmaFinished L kernel Assumptions.all X)
    (hcom : CommitFinished L kernel Assumptions.all X)
    (hst : StoreFinished L kernel Assumptions.all X) {i : EvId} {p : AsyncCopy.Part} {c : Nat}
    (huse : SharedUse L X (.async i p) c) (hx : CtaExited L X c) :
    SharedFinished L kernel Assumptions.all X (.async i p) c := by
  have hc : c = i.1 / L.block := life_own hp hX hFw hR huse
  subst hc
  have hmb : ∀ {j : EvId} {ev : Event} {l : Loc}, X.get j = some ev → Frame.MbarOf ev l →
      l.cta = j.1 / L.block := fun he hm => life_mbar_own hR (Frame.lt_of_get hX he) he hm
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨j, s, he, -⟩ | ⟨j, address, s, x, y, k, he, hi, hsl, -⟩ | ⟨j, address, s, he, hi, -⟩ |
      ⟨j, q, he, hfin, hsu⟩
  · rcases async_ref hX hint with hr | ⟨x, y, k, s, addr, -, -, hl, -⟩ |
        ⟨x, y, k, s, addr, -, -, hl, -⟩
    · rcases hr with ⟨isB, idx, hpp, hsz, hf⟩ | ⟨x, y, k, s, addr, hpp, hts, hl, hsz⟩ |
        ⟨x, y, k, s, addr, hpp, hti, hl, hsz⟩
      · subst hpp
        have hf' := hmma i (by
          rcases hf with ⟨d, s, acc, mask, hmi, -⟩ | ⟨cp, k, cta, hcp, -⟩
          · exact .inl ⟨d, s, acc, mask, hmi⟩
          · exact .inr ⟨cp, hcp⟩) hx
        exact SharedFinished.of_stage (j := i) (q := .mmaDone) hpres
          (.inr ⟨rfl, rfl, rfl, hpres, hf'.1⟩) hf'
      · subst hpp
        have hf' := hst i addr s hts hx
        exact SharedFinished.of_stage (j := i) (q := .readsDone) hpres
          (.inr ⟨rfl, rfl, rfl, hpres, hf'.1⟩) hf'
      · subst hpp
        exact load_byte_finished hX hti (by
          obtain ⟨slot, hs⟩ := Option.map_eq_some_iff.mp hl
          exact Option.isSome_iff_exists.mpr ⟨_, hs.1⟩) (hld i addr s hti hx)
    · rw [Execution.store_writeLoc_global hl] at hsp
      cases hsp
    · rw [Execution.tensor_readLoc_global hl] at hsp
      cases hsp
  · have hsrc := objectAction_source (r := (⟨.async i p, act, { state := none }, none⟩ :
      MBarrier.Record _)) hact
    cases hsrc with
    | @init g j pc n hid he ha' => cases hid
    | @inval g j pc hid he ha' => cases hid
    | @arrive g j pc tx n rel sc hid he ha' => cases hid
    | @wait g j pc q ok acq sc hid he ha' => cases hid
    | @increment g j pc hid he ha' => cases hid
    | @tensor i' pc a sp hid he hm ha' =>
      obtain ⟨rfl, rfl⟩ : i = i' ∧ p = .notify .load := by
        injection hid with h1 h2
        exact ⟨h1, h2⟩
      exact hld i a sp ⟨pc, he⟩ hx
    | @arriveOn i' pc m' noinc hid he hm hn ha' => exact (no_asyncArrive hX hR he).elim
    | @bulk i' pc s hid he hc hn ha' => exact (no_copy hX hR he hc).elim
    | @commit i' pc sp rank hid he htg ha' =>
      obtain ⟨rfl, rfl⟩ : i = i' ∧ p = .tcNotify rank := by
        injection hid with h1 h2
        exact ⟨h1, h2⟩
      exact hcom i sp rank _ ⟨pc, he⟩ htg hx
    | @clc i' pc sp tg c' hid he hm htg ha' => exact (no_clc hX hR he htg).elim
  · cases he
  · obtain ⟨rfl, rfl⟩ : i = j ∧ p = .write (.load x y k) := by
      injection he with h1 h2
      exact ⟨h1, h2⟩
    exact load_byte_finished hX hi hsl (hld i address s hi hx)
  · obtain ⟨rfl, rfl⟩ : i = j ∧ p = .readsDone := by
      injection he with h1 h2
      exact ⟨h1, h2⟩
    exact hst i address s hi hx
  · obtain ⟨rfl, rfl⟩ : i = j ∧ p = q := by
      injection he with h1 h2
      exact ⟨h1, h2⟩
    rcases hfin with ⟨s, l, hcopy, hcm, rfl⟩ | ⟨s, hcopy, -, rfl⟩ | ⟨l, noinc, hao, rfl⟩ |
      ⟨htc, rfl⟩ | ⟨s, tg, c', hcl, -, rfl⟩ | ⟨a, s, hti, rfl⟩ | ⟨a, s, -, rfl⟩ |
      ⟨s, rank, l, hcm, htg, rfl⟩
    · exact (noCopy hX hcopy).elim
    · exact (noCopy hX hcopy).elim
    · exact (noAsyncArrive hX hao).elim
    · rcases htc with ⟨d, s, acc, mask, hmi⟩ | ⟨cp, hcpi⟩ | ⟨sh, hsh⟩
      · exact hmma i (.inl ⟨d, s, acc, mask, hmi⟩) hx
      · exact hmma i (.inr ⟨cp, hcpi⟩) hx
      · obtain ⟨pc, he⟩ := hsh
        exact absurd rfl (no_shift_of_code hX code_noShift he sh)
    · exact (noClcIssue hX hcl).elim
    · exact hld i a s hti hx
    · exact hsu.elim
    · exact hcom i s rank l hcm htg hx

/-- **No use of a CTA's shared memory is unsafe**, from the completion of the loads' arrivals, the
MMAs, the commits' arrivals and the stores' source reads. -/
theorem no_sharedLifetime (hld : LoadNotified L kernel Assumptions.all X)
    (hmma : MmaFinished L kernel Assumptions.all X)
    (hcom : CommitFinished L kernel Assumptions.all X)
    (hst : StoreFinished L kernel Assumptions.all X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  noSharedLifetime_of_own hX (fun _ _ huse => life_own hp hX hFw hR huse)
    fun _ _ _ huse hx => life_async hp hX hFw hR hld hmma hcom hst huse hx

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Life
