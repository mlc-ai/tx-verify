-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Inputs
import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Safe.NoUninit
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticCommit
import Lemmas.Kernel.Safety.Object
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async

@[expose] public section

/-! # ERR-OBJECT-LIFETIME: the mbarriers' lifetimes, faults and bytes

The safety class of Core's `Unsafe` this file owns (`TmaUnsafe`), by the library's skeleton for a
kernel without linear copies (`Frame.noTmaUnsafe_of_noCopy`):

* no invalidation (`no_inval`, from the mbarrier rows);
* an object with a record is a family's object of a CTA (`record_issuer`, `use_cta`) and is
  initialized first (`initFirst`);
* the one initialization of an object is published to the issue of each other record
  (`Safe.init_pub`, the CTA winner's initialization before barrier 0, which is the object's one
  initialization by `init_unique`);
* no bulk copy (`noCopy`, a static scan), so no `cp.async` group overlap and no masked range;
* the other records' fault freedom (`Inputs.faults`, from the rings' gates);
* the footprints' disjointness from the objects: a thread's access (`Safe.threadBytes`,
  `mem_noMbar`) and an asynchronous stage's (`Safe.asyncBytes`, `async_below`) end below the
  first mbarrier. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {P : Params} {L : Launch} {mem0 : Mem0}

/-- An initialized mbarrier is a shared object at or above `Region.mbars.lo` of the workspace
(one of the families', `mbar_use`). -/
private theorem mbInit_loc (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {i : EvId} {l : Loc}
    {c : Nat} (hM : X.MbInit i l c) :
    l.space = .shared ∧ L.sharedBase + Region.mbars.lo ≤ l.addr := by
  obtain ⟨pci, hgi⟩ := hM
  have hmo : Frame.MbarOf ⟨pci, .mbInit l c⟩ l := by simp [Frame.MbarOf]
  obtain ⟨f, rfl⟩ := use_cta (mbar_use (hIn.mbar hp X hX hFw) (Frame.lt_of_get hX hgi) hgi hmo)
  have hoff := (MbarFam.off_range f).1
  simp only [MbarRow.loc, mbarLoc, Region.lo]
  exact ⟨trivial, by omega⟩

/-- **No access of a thread covers a byte of an initialized mbarrier**: the mbarrier is at or
above `Region.mbars.lo` of the workspace (`mbInit_loc`), and every memory access of a launched
lane is global, or shared and ending below the mbarriers (`access_place`). -/
theorem Safe.threadBytes (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {e : EvId} {a : Acc}
    {w : Bool} {i : EvId} {l : Loc} {c : Nat} {b : Loc} (hI : X.Access e a w)
    (hM : X.MbInit i l c) (hc : a.Covers b) : ¬ Acc.Covers { loc := l, size := 8 } b := by
  obtain ⟨hls, hla⟩ := mbInit_loc hp hIn hX hFw hM
  obtain ⟨g, k⟩ := e
  rintro ⟨hs, -, hlo, -⟩
  have hs' : b.space = l.space := hs
  have hlo' : l.addr ≤ b.addr := hlo
  obtain ⟨hbs, -, -, hhi⟩ := hc
  rcases access_place hp hX hFw hI with hg | ⟨-, -, -, hb⟩
  · rw [hs', hls, hg] at hbs
    cases hbs
  · omega

/-- **No asynchronous stage covers a byte of an initialized mbarrier**: the mbarrier is at or
above `Region.mbars.lo` (`mbInit_loc`), and every shared byte an asynchronous stage accesses is
below it (`async_below`). -/
theorem Safe.asyncBytes (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) {i : EvId}
    {p : AsyncCopy.Part} {a : Acc} {w : Bool} {j : EvId} {l : Loc} {c : Nat} {b : Loc}
    (hI : X.Intent (.async i p) a w) (hM : X.MbInit j l c) (hc : a.Covers b) :
    ¬ Acc.Covers { loc := l, size := 8 } b := by
  obtain ⟨hls, hla⟩ := mbInit_loc hp hIn hX hFw hM
  rintro ⟨hs, -, hlo, -⟩
  have hs' : b.space = .shared := (show b.space = l.space from hs).trans hls
  have hlo' : l.addr ≤ b.addr := hlo
  obtain ⟨g, k⟩ := i
  obtain ⟨-, -, hb⟩ := async_below hp hX hFw hI hc hs'
  omega

/-- **ERR-OBJECT-LIFETIME**: no mbarrier fault, every record inside its object's lifetime, no
access of an object's bytes, no linear copy fault. -/
theorem Safe.noTma (hp : Pre P L mem0) (hIn : Inputs P L mem0) {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hFw : Follow P L X) :
    ¬ TmaUnsafe L mem0 X := by
  have hR := hIn.mbar hp X hX hFw
  have hI := hIn.initRows hp X hX hFw
  have hloc : ∀ {l r}, r ∈ X.objects l → ∃ c f, l = mbarLoc L c f := by
    intro l r hr
    obtain ⟨ev, hget, hm, -⟩ := record_issuer hX hr
    generalize r.id.issuer = u at hget
    obtain ⟨h, k⟩ := u
    obtain ⟨f, hl⟩ := use_cta (mbar_use hR (Frame.lt_of_get hX hget) hget hm)
    exact ⟨_, f, hl⟩
  refine Frame.noTmaUnsafe_of_noCopy hX (no_inval hX hR) (fun l hne => ?_)
    (fun l e c he s hs hn => ?_) (fun l r hr hn => ?_)
    (fun e a w i l c b hI hM hc => ?_)
    (fun _ _ h => noCopy hX h)
  · obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨c, f, rfl⟩ := hloc hr
    exact ⟨_, initFirst hp hX hFw hR hI (hIn.bar0 hp X hX hFw) c f⟩
  · obtain ⟨c, f, rfl⟩ := hloc hs
    obtain ⟨ev, hget, hm, hii⟩ := record_issuer hX hs
    generalize s.id.issuer = u at hget ⊢
    obtain ⟨h, k⟩ := u
    have hni : ∀ n, ev.kind ≠ .mbInit (mbarLoc L c f) n := fun n hk => by
      obtain ⟨n', hn'⟩ := hii ⟨n, hk⟩
      exact hn n' hn'
    obtain ⟨_, _, i, -, ⟨pci, hi⟩, hc⟩ := Safe.init_pub hp hIn hX hFw hget hm hni
    obtain ⟨pce, he⟩ := he
    obtain ⟨rfl, -⟩ := init_unique hp hX hFw hR hI hi he
    exact .inl hc
  · obtain ⟨c, f, rfl⟩ := hloc hr
    exact hIn.faults hp X hX hFw c f r hr
  · cases e with
    | thread e => exact Safe.threadBytes hp hIn hX hFw hI hM hc
    | async i' p => exact Safe.asyncBytes hp hIn hX hFw hI hM hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
