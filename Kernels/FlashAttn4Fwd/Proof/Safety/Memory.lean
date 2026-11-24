-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Stats
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Lemmas.Protocol.RegionOrderExcept

@[expose] public section

/-! # The memory branches of `Unsafe`: allocation, races, mixed-size conflicts

The kernel's memory, region by region. A CTA's shared window (`sharedBytes` from
`L.sharedBase`) holds the mbarriers (`+0 .. +328`), the Tensor Memory base word (`InBase`,
`+328`), the statistics words (`InStatsArea`, `+332 .. +1356`), the output staging buffers
(`InStaging`, `+3072 .. +68608`), the two Q stages (`InQRing`, `+68608 .. +134144`) and the six
KV slots (`InKvRing`, `+134144 .. +232448`). Global memory holds the Q, K, V and O tensors
(`InTensor`).

* **Placement** (`SharedPlaced`, `GlobalPlaced`): every byte an access touches is in a region of
  a launched CTA's window (no access touches an mbarrier's bytes), or in one of the tensors.
  Every global write is of O (`GlobalWrites`): Q, K and V are only read.
* **Allocation** (`no_unalloc`): a window byte of a launched CTA is allocated
  (`Pre.sharedAllocated`), every byte of a tensor (`tensor_element`, `Pre.inputQ/K/V`,
  `Pre.outputAllocated`).
* **Order** (`conflicts_ordered`): each shared region's protocol orders its conflicting accesses
  (`ConflictsOrdered`); a global conflict has a writer, so it is on O, whose conflicts are
  ordered but for the store warp's 32 lanes' tensor stores of one element, which write the same
  byte with the same value (`ConflictsOrderedExcept`, ERR-DATA-RACE `SameValueWrites`). So there is
  no race and no mixed-size conflict (`no_race`, `no_mixed`). The bytes outside O are ordered
  without exemption (`outside_ordered`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Safety

open PTX AsyncCopy

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### Regions -/

/-- A byte of a CTA's Tensor Memory base word. -/
def InBase (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 328 ≤ l.addr ∧ l.addr < L.sharedBase + 332

/-- A byte of a CTA's two Q stages. -/
def InQRing (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 68608 ≤ l.addr ∧ l.addr < L.sharedBase + 134144

/-- A byte of a CTA's six KV slots. -/
def InKvRing (L : Launch) (l : Loc) : Prop :=
  l.space = .shared ∧ L.sharedBase + 134144 ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes

/-- A byte of one of a CTA's accessed shared regions. -/
def InRegions (L : Launch) (l : Loc) : Prop :=
  InBase L l ∨ InStatsArea L l ∨ InStaging L l ∨ InQRing L l ∨ InKvRing L l

/-- A byte of the contiguous `(b, rows, h, 128)` f16 tensor at `base`. -/
def InTensor (P : Params) (base rows : Nat) (l : Loc) : Prop :=
  l.space = .global ∧ l.cta = 0 ∧ base ≤ l.addr ∧ l.addr < base + tensorBytes P rows

/-- **Shared placement**: every shared byte an access touches is in a region of a launched
CTA. -/
def SharedPlaced (L : Launch) (X : Execution) : Prop :=
  ∀ e a l, X.MemTouches e a → a.Covers l → l.space = .shared → l.cta < L.grid ∧ InRegions L l

/-- **Global placement**: every byte outside shared memory that an access touches is a global byte
in one of the four tensors. -/
def GlobalPlaced (P : Params) (X : Execution) : Prop :=
  ∀ e a l, X.MemTouches e a → a.Covers l → l.space ≠ .shared →
    InTensor P P.qBase P.sq l ∨ InTensor P P.kBase P.sk l ∨ InTensor P P.vBase P.sk l ∨
      InTensor P P.oBase P.sq l

/-- **Global writes**: every byte outside shared memory that a write covers is a global byte in
O. -/
def GlobalWrites (P : Params) (X : Execution) : Prop :=
  ∀ e a l, X.Intent e a true → a.Covers l → l.space ≠ .shared → InTensor P P.oBase P.sq l

/-! ### Allocation -/

/-- Every byte of a tensor is a byte of one of its elements. -/
theorem tensor_element {base rows : Nat} {l : Loc} (h : InTensor P base rows l) :
    ∃ batch < P.b, ∃ head < P.h, ∃ row < rows, ∃ d < 128, ∃ byte < 2,
      (elementLoc P base rows batch head row d).at byte = l := by
  obtain ⟨hs, hc, hlo, hhi⟩ := h
  unfold tensorBytes at hhi
  have hob : l.addr - base < P.b * rows * P.h * 128 * 2 := by
    have : 256 * P.b * P.h * rows = P.b * rows * P.h * 128 * 2 := by ring
    omega
  have hh : 0 < P.h := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hob
  have hr : 0 < rows := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hob
  set u := (l.addr - base) / 2 with hu
  set v := u / 128 with hv
  set w := v / P.h with hw
  have hu' : u < P.b * rows * P.h * 128 := (Nat.div_lt_iff_lt_mul (by decide)).mpr hob
  have hv' : v < P.b * rows * P.h := (Nat.div_lt_iff_lt_mul (by decide)).mpr hu'
  have hw' : w < P.b * rows := (Nat.div_lt_iff_lt_mul hh).mpr hv'
  refine ⟨w / rows, (Nat.div_lt_iff_lt_mul hr).mpr hw', v % P.h, Nat.mod_lt _ hh, w % rows,
    Nat.mod_lt _ hr, u % 128, Nat.mod_lt _ (by decide), (l.addr - base) % 2,
    Nat.mod_lt _ (by decide), ?_⟩
  have e1 : w / rows * rows + w % rows = w := Nat.div_add_mod' w rows
  have e2 : w * P.h + v % P.h = v := Nat.div_add_mod' v P.h
  have e3 : v * 128 + u % 128 = u := Nat.div_add_mod' u 128
  have e4 : 2 * u + (l.addr - base) % 2 = l.addr - base := Nat.div_add_mod _ 2
  obtain ⟨sp, cta, addr⟩ := l
  simp only at hs hc hlo e4 ⊢
  subst hs hc
  simp only [elementLoc, Loc.at, Loc.mk.injEq, true_and]
  rw [e1, e2, e3]
  omega

/-- A byte of an input tensor holds its element's byte at launch. -/
theorem input_allocated (hpre : Pre P L mem0) {l : Loc}
    (h : InTensor P P.qBase P.sq l ∨ InTensor P P.kBase P.sk l ∨ InTensor P P.vBase P.sk l) :
    mem0 l ≠ none := by
  rcases h with h | h | h
  · obtain ⟨b, hb, hd, hhd, r, hr, d, hd', y, hy, rfl⟩ := tensor_element h
    simp [hpre.inputQ b hb hd hhd r hr d hd' y hy]
  · obtain ⟨b, hb, hd, hhd, r, hr, d, hd', y, hy, rfl⟩ := tensor_element h
    simp [hpre.inputK b hb hd hhd r hr d hd' y hy]
  · obtain ⟨b, hb, hd, hhd, r, hr, d, hd', y, hy, rfl⟩ := tensor_element h
    simp [hpre.inputV b hb hd hhd r hr d hd' y hy]

/-- A byte of the output tensor is allocated. -/
theorem output_allocated (hpre : Pre P L mem0) {l : Loc} (h : InTensor P P.oBase P.sq l) :
    mem0 l ≠ none := by
  obtain ⟨hs, hc, hlo, hhi⟩ := h
  have hh := hpre.outputAllocated (l.addr - P.oBase) (by omega)
  obtain ⟨sp, cta, addr⟩ := l
  simp only at hs hc hlo hhi
  subst hs hc
  rwa [show P.oBase + (addr - P.oBase) = addr by omega] at hh

/-- A byte of a region of a launched CTA is allocated. -/
theorem region_allocated (hpre : Pre P L mem0) {l : Loc} (hc : l.cta < L.grid)
    (h : InRegions L l) : mem0 l ≠ none := by
  have hw : l.space = .shared ∧ L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + sharedBytes := by
    unfold InRegions InBase InStatsArea InStaging InQRing InKvRing at h
    unfold sharedBytes at *
    rcases h with h | h | h | h | h <;> exact ⟨h.1, by omega, by omega⟩
  have hh := hpre.sharedAllocated l.cta hc (l.addr - L.sharedBase) (by omega)
  obtain ⟨sp, cta, addr⟩ := l
  obtain ⟨hs, hlo, -⟩ := hw
  simp only at hs hlo hh
  subst hs
  rwa [show L.sharedBase + (addr - L.sharedBase) = addr by omega] at hh

/-- **Every touched byte is allocated**, given that the eight bytes of every named mbarrier are
(`Tma.mbar_allocated`). -/
theorem no_unalloc (hpre : Pre P L mem0) (hsh : SharedPlaced L X) (hgl : GlobalPlaced P X)
    (hmb : ∀ e m l, X.UsesMbar e m → Acc.Covers { loc := m, size := 8 } l → mem0 l ≠ none) :
    ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, ht, hc, hn⟩ | ⟨e, m, l, hu, hc, hn⟩)
  swap
  · exact hmb e m l hu hc hn
  by_cases hsp : l.space = .shared
  · obtain ⟨hcta, hr⟩ := hsh e a l ht hc hsp
    exact region_allocated hpre hcta hr hn
  · rcases hgl e a l ht hc hsp with h | h | h | h
    · exact input_allocated hpre (.inl h) hn
    · exact input_allocated hpre (.inr (.inl h)) hn
    · exact input_allocated hpre (.inr (.inr h)) hn
    · exact output_allocated hpre h hn

/-! ### Order -/

/-- **The shared bytes are ordered**, region by region. -/
theorem shared_ordered (hsh : SharedPlaced L X) (hb : ConflictsOrdered L X (InBase L))
    (hs : ConflictsOrdered L X (InStatsArea L)) (ho : ConflictsOrdered L X (InStaging L))
    (hq : ConflictsOrdered L X (InQRing L)) (hkv : ConflictsOrdered L X (InKvRing L)) :
    ConflictsOrdered L X fun l => l.space = .shared := by
  intro e f a b l hc ha hb' hsp
  obtain ⟨-, we, -, he, -⟩ := id hc
  rcases (hsh e a l (.inl ⟨we, he⟩) ha hsp).2 with h | h | h | h | h
  · exact hb e f a b l hc ha hb' h
  · exact hs e f a b l hc ha hb' h
  · exact ho e f a b l hc ha hb' h
  · exact hq e f a b l hc ha hb' h
  · exact hkv e f a b l hc ha hb' h

/-- **The bytes outside shared memory are ordered**, but for the identical-value write pairs: a
conflict has a writer, whose bytes are in O. -/
theorem global_ordered (hw : GlobalWrites P X)
    (ho : ConflictsOrderedExcept L X (InTensor P P.oBase P.sq)) :
    ConflictsOrderedExcept L X (fun l => l.space ≠ .shared) := by
  intro e f a b l hc ha hb hsp hE
  obtain ⟨-, we, wf, he, hf, hwr, -⟩ := id hc
  refine ho e f a b l hc ha hb ?_ hE
  rcases hwr with rfl | rfl
  · exact hw e a l he ha hsp
  · exact hw f b l hf hb hsp

variable (hsh : SharedPlaced L X) (hb : ConflictsOrdered L X (InBase L))
    (hs : ConflictsOrdered L X (InStatsArea L)) (ho : ConflictsOrdered L X (InStaging L))
    (hq : ConflictsOrdered L X (InQRing L)) (hkv : ConflictsOrdered L X (InKvRing L))
    (hw : GlobalWrites P X)
include hsh hb hs ho hq hkv hw

/-- **Every byte is ordered**, but for the identical-value write pairs. -/
theorem conflicts_ordered (hout : ConflictsOrderedExcept L X (InTensor P P.oBase P.sq)) :
    ConflictsOrderedExcept L X (fun _ => True) :=
  ((shared_ordered hsh hb hs ho hq hkv).except.or (global_ordered hw hout)).mono fun l _ =>
    Classical.em (l.space = .shared)

/-- **The bytes outside O are ordered**: the shared bytes region by region, and a global byte
outside O has no writer. -/
theorem outside_ordered :
    ConflictsOrdered L X fun l => ¬ InTensor P P.oBase P.sq l := by
  intro e f a b l hc ha hb' hl
  by_cases hsp : l.space = .shared
  · exact shared_ordered hsh hb hs ho hq hkv e f a b l hc ha hb' hsp
  · obtain ⟨-, we, wf, he, hf, hwr, -⟩ := hc
    rcases hwr with rfl | rfl
    · exact (hl (hw e a l he ha hsp)).elim
    · exact (hl (hw f b l hf hb' hsp)).elim

/-- **No race.** -/
theorem no_race (hout : ConflictsOrderedExcept L X (InTensor P P.oBase P.sq)) :
    ¬ Race L X :=
  (conflicts_ordered hsh hb hs ho hq hkv hw hout).no_race

/-- **No mixed-size conflict.** -/
theorem no_mixed (hout : ConflictsOrderedExcept L X (InTensor P P.oBase P.sq)) :
    ¬ Mixed L X :=
  (conflicts_ordered hsh hb hs ho hq hkv hw hout).no_mixed

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Safety
