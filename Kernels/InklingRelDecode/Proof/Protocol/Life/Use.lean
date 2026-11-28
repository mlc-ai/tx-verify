-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Life.Def
public import Kernels.InklingRelDecode.Proof.Protocol.Life.Own
public import Lemmas.Kernel.Safety.Lifetime
import Kernels.InklingRelDecode.Proof.Protocol.Tmem.AccessInfo
import Kernels.InklingRelDecode.Proof.Mma.Export.Columns
import Kernels.InklingRelDecode.Proof.Lib.NoEvents
import Kernels.InklingRelDecode.Proof.Lib.ReadKinds
import Kernels.InklingRelDecode.Proof.Lib.WriteKinds
import Kernels.InklingRelDecode.Proof.Protocol.Alloc.Access
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Lemmas.Cluster.Unit
import Lemmas.Protocol.ObjectSource

@[expose] public section

/-! # Every use of a CTA's shared memory is of the issuer's CTA, and finished with the CTA

`life_own`: each of the six forms of `SharedUse` (an access, an action on an mbarrier, a commit's
issue, a tensor load's write, a tensor store's read, the completing stage of an operation) names
the CTA of the issuing lane. `life_async`: an asynchronous use is finished once its CTA exited,
from the finish of the tensor loads, the MMAs and the commits. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
open PTX PTX.Flow PTX.AsyncCopy

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **A cluster has one CTA.** -/
theorem cluster_eq (hp : Pre Q L m) {c owner : Nat} (h : CtaInCluster L c owner) :
    owner = c := by
  have hs : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩ := by
    intro k
    rw [hp.clusterPlaces, hp.clusterNctaid]
    rfl
  obtain ⟨hc, ho, hcl⟩ := h
  rw [Launch.clusterOfCta_unit hs (hp.nclusters ▸ hc),
    Launch.clusterOfCta_unit hs (hp.nclusters ▸ ho)] at hcl
  exact hcl.symm

private theorem no_copy {i : EvId} {s : AsyncCopy.Spec}
    (hX : Consistent L kernel Assumptions.all m X) (h : X.Copy i s) : False := by
  obtain ⟨_, he⟩ := h
  exact Lib.no_copy hX he

private theorem no_arrive {i : EvId} {l : Loc} {n : Bool}
    (hX : Consistent L kernel Assumptions.all m X) (h : X.AsyncArrive i l n) : False := by
  obtain ⟨_, he⟩ := h
  exact Lib.no_asyncArrive hX he

private theorem no_clc {i : EvId} {s : Clc.Spec} {t : List Nat}
    (hX : Consistent L kernel Assumptions.all m X) (h : X.ClcIssue i s t) : False := by
  obtain ⟨_, he⟩ := h
  exact Lib.no_clc hX he

section
variable (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
  (rows : MbarRows Q L X) (base : Iface.BaseRead L X)
include hp hX hf rows base

/-- **Every use of shared memory is of the issuing lane's CTA.** -/
theorem life_own {e} {c : Nat} (huse : SharedUse L X e c) : c = e.issuer.1 / L.block := by
  have hmb : ∀ {i : EvId} {ev : Event} {l : Loc}, X.get i = some ev → Frame.MbarOf ev l →
      l.cta = i.1 / L.block := fun he hm => mbar_own rows (Frame.lt_of_get hX he) he hm
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨i, s, rfl, hc, hgrp⟩ | ⟨i, address, s, x, y, k, rfl, hi, hsl, hcta⟩ |
      ⟨i, address, s, rfl, hi, hcta⟩ | ⟨i, q, rfl, hfin, hsu⟩
  · exact hcta.symm.trans (intent_own hp hX hf hint hsp)
  · have hsrc := objectAction_source (r := (⟨e, act, { state := none }, none⟩ :
      MBarrier.Record _)) hact
    cases hsrc with
    | @init g j pc n hid he ha' => subst hid; exact hmb he rfl
    | @inval g j pc hid he ha' => exact (Lib.no_inval hX he).elim
    | @arrive g j pc tx n rel sc hid he ha' => subst hid; exact hmb he rfl
    | @wait g j pc q ok acq sc hid he ha' => subst hid; exact hmb he rfl
    | @increment g j pc hid he ha' => exact (Lib.no_asyncArrive hX he).elim
    | @tensor i pc a sp hid he hm ha' => subst hid; exact hmb he hm
    | @arriveOn i pc m' noinc hid he hm hn ha' => exact (Lib.no_asyncArrive hX he).elim
    | @bulk i pc s hid he hc hn ha' => exact (Lib.no_copy hX he).elim
    | @commit i pc sp rank hid he htg ha' => subst hid; exact hmb he ⟨rank, htg⟩
    | @clc i pc sp tg c' hid he hm htg ha' => exact (Lib.no_clc hX he).elim
  · exact (cluster_eq hp hgrp.1).symm ▸ rfl
  · obtain ⟨pc, he⟩ := hi
    exact hcta.symm.trans (tensor_base hX he)
  · obtain ⟨pc, he⟩ := hi
    exact (Lib.no_tensorStore hX he).elim
  · rcases hfin with ⟨s, l, hcopy, hcm, rfl⟩ | ⟨s, hcopy, -, rfl⟩ | ⟨l, noinc, hao, rfl⟩ |
      ⟨-, rfl⟩ | ⟨s, tg, c', hcl, -, rfl⟩ | ⟨a, s, hti, rfl⟩ | ⟨a, s, -, rfl⟩ |
      ⟨s, rank, l, hcm, htg, rfl⟩
    · exact (no_copy hX hcopy).elim
    · exact (no_copy hX hcopy).elim
    · exact (no_arrive hX hao).elim
    · rcases hsu with ⟨d, s, acc, mask, hmi, hlh⟩ | ⟨cp, hcpi, hc⟩
      · obtain ⟨g, k⟩ := i
        obtain ⟨pc, he⟩ := hmi
        obtain ⟨-, h1, h2, -⟩ := Mma.Export.columns hp hX hf (fun h1 h2 h3 => base h1 h2 h3) he
        rcases hlh with h | h
        · exact h.trans h1
        · exact h.trans h2
      · exact (Lib.no_cp hX _ _ hcpi).elim
    · exact (no_clc hX hcl).elim
    · obtain ⟨address, s', hti', -, hcta⟩ := hsu
      obtain ⟨pc, he⟩ := hti'
      exact hcta.symm.trans (hmb he rfl)
    · exact hsu.elim
    · obtain ⟨s', m', ⟨pc, he⟩, htg', hcta⟩ := hsu
      exact hcta.symm.trans (hmb he ⟨rank, htg'⟩)

omit hp hf rows base in
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

/-- **Every asynchronous use finishes before an exit of an exited CTA**, from the finish of the
tensor loads' arrivals, the MMAs and the commits' arrivals. -/
theorem life_async (hld : LoadNotified L kernel Assumptions.all X)
    (hmma : MmaFinished L kernel Assumptions.all X)
    (hcom : CommitFinished L kernel Assumptions.all X) {i : EvId} {p : AsyncCopy.Part} {c : Nat}
    (huse : SharedUse L X (.async i p) c) (hx : CtaExited L X c) :
    SharedFinished L kernel Assumptions.all X (.async i p) c := by
  have hc : c = i.1 / L.block := life_own hp hX hf rows base huse
  subst hc
  rcases huse with ⟨hpres, ⟨a, w, hint, hsp, hcta⟩ | ⟨addr, act, hact⟩⟩ |
      ⟨j, s, he, -⟩ | ⟨j, address, s, x, y, k, he, hi, hsl, -⟩ | ⟨j, address, s, he, hi, -⟩ |
      ⟨j, q, he, hfin, hsu⟩
  · cases w
    · rcases Lib.read_intents hX hint with ⟨_, _, _, h, _⟩ | ⟨i', isB, j, h, foot⟩ |
        ⟨i', x, y, z, addr, sp, h, -, loc, -⟩
      · cases h
      · obtain ⟨rfl, rfl⟩ : i = i' ∧ p = .mmaRead isB j := by
          injection h with h1 h2
          exact ⟨h1, h2⟩
        rcases foot with ⟨d, s, acc, mask, hmi, -⟩ | ⟨cp, k, cta, hcp, -⟩
        · have hf' := hmma i d s acc mask hmi hx
          exact SharedFinished.of_stage (j := i) (q := .mmaDone) hpres
            (.inr ⟨rfl, rfl, rfl, hpres, hf'.1⟩) hf'
        · exact (Lib.no_cp hX i cp hcp).elim
      · exact absurd hsp (by rw [Protocol.Alloc.tensor_read_space loc]; nofun)
    · rcases Lib.write_intents hX hint with ⟨_, _, _, h, _⟩ |
        ⟨i', x, y, z, addr, sp, h, hi, byte, -⟩
      · cases h
      · obtain ⟨rfl, rfl⟩ : i = i' ∧ p = .write (.load x y z) := by
          injection h with h1 h2
          exact ⟨h1, h2⟩
        simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at byte
        obtain ⟨slot, hs, -⟩ := byte
        exact load_byte_finished hX hi (Option.isSome_iff_exists.mpr ⟨_, hs⟩)
          (hld i addr sp hi hx)
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
    | @arriveOn i' pc m' noinc hid he hm hn ha' => exact (Lib.no_asyncArrive hX he).elim
    | @bulk i' pc s hid he hc hn ha' => exact (Lib.no_copy hX he).elim
    | @commit i' pc sp rank hid he htg ha' =>
      obtain ⟨rfl, rfl⟩ : i = i' ∧ p = .tcNotify rank := by
        injection hid with h1 h2
        exact ⟨h1, h2⟩
      exact hcom i sp rank _ ⟨pc, he⟩ htg hx
    | @clc i' pc sp tg c' hid he hm htg ha' => exact (Lib.no_clc hX he).elim
  · cases he
  · obtain ⟨rfl, rfl⟩ : i = j ∧ p = .write (.load x y k) := by
      injection he with h1 h2
      exact ⟨h1, h2⟩
    exact load_byte_finished hX hi hsl (hld i address s hi hx)
  · obtain ⟨pc, hti⟩ := hi
    exact (Lib.no_tensorStore hX hti).elim
  · obtain ⟨rfl, rfl⟩ : i = j ∧ p = q := by
      injection he with h1 h2
      exact ⟨h1, h2⟩
    rcases hfin with ⟨s, l, hcopy, hcm, rfl⟩ | ⟨s, hcopy, -, rfl⟩ | ⟨l, noinc, hao, rfl⟩ |
      ⟨htc, rfl⟩ | ⟨s, tg, c', hcl, -, rfl⟩ | ⟨a, s, hti, rfl⟩ | ⟨a, s, hts, rfl⟩ |
      ⟨s, rank, l, hcm, htg, rfl⟩
    · exact (no_copy hX hcopy).elim
    · exact (no_copy hX hcopy).elim
    · exact (no_arrive hX hao).elim
    · rcases htc with ⟨d, s, acc, mask, hmi⟩ | ⟨cp, hcpi⟩ | ⟨sh, hsh⟩
      · exact hmma i d s acc mask hmi hx
      · exact (Lib.no_cp hX i cp hcpi).elim
      · exact (Tmem.no_shift hX i sh hsh).elim
    · exact (no_clc hX hcl).elim
    · exact hld i a s hti hx
    · obtain ⟨pc, hti⟩ := hts
      exact (Lib.no_tensorStore hX hti).elim
    · exact hcom i s rank l hcm htg hx

/-- **No use of a CTA's shared memory is unsafe**, from the finish of the tensor loads' arrivals,
the MMAs and the commits' arrivals. -/
theorem no_sharedLifetime (hld : LoadNotified L kernel Assumptions.all X)
    (hmma : MmaFinished L kernel Assumptions.all X)
    (hcom : CommitFinished L kernel Assumptions.all X) :
    ¬ SharedLifetimeUnsafe L kernel Assumptions.all X :=
  noSharedLifetime_of_own hX (fun _ _ huse => life_own hp hX hf rows base huse)
    fun _ _ _ huse hx => life_async hp hX hf rows base hld hmma hcom huse hx

end

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Life
