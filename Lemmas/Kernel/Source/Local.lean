-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.LocalMemory
public import Lemmas.Flow.AccessLocal

@[expose] public section

/-! # Source of a returned value: a read of the thread's own local memory

A proof tool, generic over the kernel, beside the protected read (`Protected.lean`). A `ld.local`
of bytes that the same thread stored earlier with `st.local` returns those bytes, when no store of
the thread between the two covers them. No hand-off is needed: the store is before the load in
program order, so in base causality.

* `LocalOwned X`: every write of a `.local` location is an event of the location's owner thread
  (§5.1.5: "The local state space ( .local ) is private memory for each thread to keep its own
  data."). On the thread side Core places every `.local` access of thread `g` in `g`'s local
  memory (`accessLoc_local_owner`); that no asynchronous operation of a kernel writes local
  memory is the kernel's (tml-fa4: the old tree's `localWriteOwner`).
* `local_read_byte_of_last_store`: a byte of a local load is the byte of the thread's last store
  that covers it (a wider store included); `local_read_of_last_store`: a load with the footprint
  of that store returns its bytes. -/

namespace PTX.Frame

open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every write of a `.local` location is an event of the location's owner thread. -/
def LocalOwned (X : Execution) : Prop :=
  ∀ w a bs (l : Loc), X.MemWrites w a bs → l.space = .local → a.Covers l →
    ∃ j, w = .thread (l.cta, j) ∧ X.Access (l.cta, j) a true

/-- **A thread's `.local` accesses are in its own local memory.** -/
theorem accessLoc_local_owner {g : Nat} {t : TState} {a : MemAccess} {loc : Loc}
    (h : accessLoc L g t a = .ok loc) (hl : loc.space = .local) : loc.cta = g := by
  unfold accessLoc at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  all_goals (repeat' (first | split at h | (cases h; done)))
  all_goals first
    | (simp only [Except.ok.injEq] at h; subst h; first | rfl | cases hl)
    | (rw [PTX.Flow.effAddr_space h] at hl; cases hl)
    | (rw [PTX.Flow.sharedEffAddr_shared h] at hl; cases hl)
    | (unfold absLoc at h; split_ifs at h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       subst h; first | rfl | cases hl)

/-- **A byte of a local load is the byte of the thread's last store that covers it**: the store
`(g, w)` is before the load `(g, e)` in the thread's trace, and every other store of the thread
that covers the byte is before `w` or after `e`. The store may be wider than the load (a 64-bit
store read back as two 32-bit words, say). -/
theorem local_read_byte_of_last_store (hX : Consistent L K A mem0 X) (hown : LocalOwned X)
    {g w e k : Nat} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hw : X.Writes (g, w) dst written) (hk : k < a.size)
    (hc : dst.Covers (a.loc.at k)) (hl : a.loc.space = .local) (hwe : w < e)
    (hlast : ∀ j d, X.Access (g, j) d true → d.Covers (a.loc.at k) → j ≤ w ∨ e < j) :
    bs[k]? = some (wbyte dst written (a.loc.at k)) := by
  have hlk : (a.loc.at k).space = .local := by simpa [Loc.at] using hl
  -- the owner of the location is the storing thread
  have hg : (a.loc.at k).cta = g := by
    obtain ⟨j, hj, -⟩ := hown (.thread (g, w)) dst written _ (Or.inl hw) hlk hc
    simp only [AsyncCopy.Ref.thread.injEq, Prod.mk.injEq] at hj
    exact hj.1.symm
  exact local_read_byte_of_last_write hX hr hw hk hc hwe
    (fun ref d bytes hm hc' => by
      obtain ⟨j, hj, ha⟩ := hown ref d bytes _ hm hlk hc'
      exact ⟨j, by rw [hj, hg], by rw [← hg]; exact ha⟩)
    hlast

/-- **A local load returns the bytes of the thread's last store with the same footprint**: the
store `(g, w)` is before the load `(g, e)` in the thread's trace, and every other store of the
thread that covers a byte of the load is before `w` or after `e`. -/
theorem local_read_of_last_store (hX : Consistent L K A mem0 X) (hown : LocalOwned X)
    {g w e : Nat} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hw : X.Writes (g, w) dst written) (hloc : dst.loc = a.loc)
    (hsize : dst.size = a.size) (hlen : written.length = a.size) (hl : a.loc.space = .local)
    (hwe : w < e)
    (hlast : ∀ j d, X.Access (g, j) d true → (∃ k < a.size, d.Covers (a.loc.at k)) →
      j ≤ w ∨ e < j) :
    bs = written.map some := by
  have hbl : bs.length = a.size := (hX.rf (.thread (g, e)) a bs (Or.inl hr)).1
  have hcov : ∀ k < a.size, dst.Covers (a.loc.at k) := fun k hk => by
    rw [show dst = { dst with loc := a.loc, size := a.size } by cases dst; simp_all]
    exact Acc.covers_at hk
  apply List.ext_getElem?
  intro k
  by_cases hk : k < a.size
  · rw [local_read_byte_of_last_store hX hown hr hw hk (hcov k hk) hl hwe
      (fun j d ha hc => hlast j d ha ⟨k, hk, hc⟩)]
    simp only [wbyte, Loc.at, hloc, Nat.add_sub_cancel_left, List.getElem?_map,
      List.getElem?_eq_getElem (show k < written.length by omega), Option.map_some]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end PTX.Frame
