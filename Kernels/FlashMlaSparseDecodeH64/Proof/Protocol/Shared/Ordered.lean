-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Lemmas.Protocol.RegionByte
import Lemmas.Order.Order
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async

@[expose] public section

/-! # Memory is ordered region by region

-- domain: consistent

The ordering facts are one family indexed by the regions of `Iface/Regions.lean`:
`RegionOrdered L X r`, conflicting accesses at a byte of region `r` of any CTA are ordered
(`ByteOrdered` of `Lemmas/Protocol/RegionByte.lean`). What holds of every region is proved here
once:

* a shared byte an access covers lies in a region of the accessing CTA below the mbarriers
  (`intent_region`: a thread's by `access_below`, an asynchronous stage's by `async_below`), so a
  conflict at a shared byte is a conflict inside one region, and the mbarrier region has none;
* two overlapping accesses of one thread are in program order (`same_thread`);
* memory is ordered once the regions but the mbarriers' and the bytes outside shared memory are
  (`mem_ordered`), so there is no race (`no_race`) and no mixed-size conflict (`no_mixed`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The per-region family**: conflicting accesses at a byte of region `r` of any CTA's
workspace are ordered, but for two writes of one value. -/
def RegionOrdered (L : Launch) (X : Execution) (r : Region) : Prop :=
  ByteOrdered L X fun l => ∃ c, MemRow.LocIn L c r l

/-- **Program order**: two overlapping accesses of one thread are ordered at every byte. -/
theorem same_thread {g i j : Nat} {a b : Acc} {we wf : Bool} (he : X.Access (g, i) a we)
    (hf : X.Access (g, j) b wf) (hne : i ≠ j) (hov : a.Overlap b) (l : Loc) :
    ByteCausality L X l (.thread (g, i)) (.thread (g, j)) ∨
      ByteCausality L X l (.thread (g, j)) (.thread (g, i)) := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact .inl (.direct (.of_base L (.single (.inl (po_of_overlap he hf rfl hlt hov)))))
  · exact .inr (.direct (.of_base L (.single (.inl (po_of_overlap hf he rfl hlt hov.symm)))))

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **A shared byte an access covers is in a region below the mbarriers** of the workspace of
its CTA. -/
theorem intent_region {e} {a : Acc} {w : Bool} {l : Loc} (hi : X.Intent e a w)
    (hc : a.Covers l) (hs : l.space = .shared) :
    ∃ r, r ≠ .mbars ∧ MemRow.LocIn L l.cta r l := by
  have hb : L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + Region.mbars.lo := by
    cases e with
    | thread i =>
      obtain ⟨g, k⟩ := i
      obtain ⟨-, h1, h2⟩ := access_below hp hX hFw hi hc hs
      exact ⟨h1, h2⟩
    | async i p =>
      obtain ⟨g, k⟩ := i
      obtain ⟨-, h1, h2⟩ := async_below hp hX hFw hi hc hs
      exact ⟨h1, h2⟩
  obtain ⟨h1, h2⟩ := hb
  have htop : l.addr - L.sharedBase < Region.top := by
    simp only [Region.lo, Region.top] at h2 ⊢
    omega
  have hmem := regionOf_cover htop
  refine ⟨regionOf (l.addr - L.sharedBase), ?_, hs, rfl, ?_, ?_⟩
  · intro h
    rw [h] at hmem
    have := hmem.1
    simp only [Region.lo] at this h2
    omega
  · have := hmem.1
    omega
  · have := hmem.2
    omega

/-- **Shared memory is ordered** once every region but the mbarriers' is. -/
theorem shared_ordered (hR : ∀ r, r ≠ .mbars → RegionOrdered L X r) :
    ByteOrdered L X fun l => l.space = .shared := by
  intro e f a b l hcon ha hb hl hE
  obtain ⟨-, _, _, he, -⟩ := id hcon
  obtain ⟨r, hr, hloc⟩ := intent_region hp hX hFw he ha hl
  exact hR r hr e f a b l hcon ha hb ⟨_, hloc⟩ hE

/-- **Memory is ordered** once every region but the mbarriers' and the bytes outside shared
memory are. -/
theorem mem_ordered (hR : ∀ r, r ≠ .mbars → RegionOrdered L X r)
    (hG : ByteOrdered L X fun l => l.space ≠ .shared) : ByteOrdered L X fun _ => True :=
  ((shared_ordered hp hX hFw hR).or hG).mono fun _ _ => Classical.em _

/-- **No data race** from the regions' and the outside bytes' orders. -/
theorem no_race (hR : ∀ r, r ≠ .mbars → RegionOrdered L X r)
    (hG : ByteOrdered L X fun l => l.space ≠ .shared) : ¬ Race L X :=
  (mem_ordered hp hX hFw hR hG).no_race

/-- **No mixed-size conflict** from the same facts. -/
theorem no_mixed (hR : ∀ r, r ≠ .mbars → RegionOrdered L X r)
    (hG : ByteOrdered L X fun l => l.space ≠ .shared) : ¬ Mixed L X :=
  (mem_ordered hp hX hFw hR hG).no_mixed

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
