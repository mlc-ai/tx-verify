-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Objects
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.MemLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.RefNext
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.FollowD
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Export.Loads
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # Where a dequantizer lane's raw and scale loads read

A raw load of the lane at `dqRawPc r s` reads eight bytes at tile row `g % 128 / 8 + 16 r`, column
`8 (g % 8) + 64 s` of a raw tile `b` of its CTA (`dequant_rawLoc`); a scale load at `dqScalePc r`
reads four bytes in the same row at column `512 + 4 j`, where `j` is the number of its events at
that pc before it, modulo 4 (`dequant_scaleLoc`, valid data: the data machine's element counter,
`Dequant.Data.InvD.pos`). Both are in block-use `v` of the tile: `v + 1` successful polls of
`rawReady b` and `v` arrivals on `rawFree b` before the load. Events of a row (pcs 2695 to 3594) are
no poll and no arrival (`dequant_rowQuiet`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow Dequant Dequant.Data

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- **An event of a row is no poll and no arrival**: a lane of warps 8-11's event at a pc of a
block's rows (a scale load, a raw load or a chunk store) that is no undefined behaviour is a read
or a write. -/
theorem dequant_rowQuiet (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {j : Nat} {x : Event} (hx : X.get (g, j) = some x)
    (hub : ∀ f, x.kind ≠ .ub f) (hr : 2695 ≤ x.pc ∧ x.pc ≤ 3594) :
    ∀ l, okPoll l x = false ∧ arrivesOn l x = false := by
  have hrange : 2606 ≤ x.pc ∧ x.pc < 3611 := by omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw hx hub
  obtain ⟨d, n, rfl, -, ⟨hpcd, hk⟩, -, -⟩ := dequant_state hp hJ hi hev hpcσ hrange
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have key : (∃ a bs, x.kind = .rd a bs) ∨ (∃ a bs, x.kind = .wr a bs) →
      ∀ l, okPoll l x = false ∧ arrivesOn l x = false := fun h l => by
    rcases h with ⟨a, bs, h⟩ | ⟨a, bs, h⟩
    · exact ⟨okPoll_notWait (by simp [h]), arrivesOn_notArrive (by simp [h])⟩
    · exact ⟨okPoll_notWait (by simp [h]), arrivesOn_notArrive (by simp [h])⟩
  refine key ?_
  cases site with
  | scale r =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · exact .inl ⟨a, bs, hk⟩
    · exact absurd hk (hub f)
  | raw r s =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · exact .inl ⟨a, bs, hk⟩
    · exact absurd hk (hub f)
  | store r s =>
    rcases hk with ⟨a, bs, hk, -⟩ | ⟨f, hk⟩
    · exact .inr ⟨a, bs, hk⟩
    · exact absurd hk (hub f)
  | _ =>
    exfalso
    simp only [Site.pc] at hpcd
    omega

/-- The barrier counts of a loop state of block `i` at a row site: slot `b`'s polls of `rawReady`
and `svDone` are `uses b (i + 1)`, its arrivals on `rawFree` and `dequantReady` `uses b i`. -/
private theorem slot_counts (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) {i : Nat} {d : Control.D}
    (h : LoopCounts L g d (fun c => ((X.tr g).take k).countP (Dequant.cls c)) i)
    (hR : incR d.site = 1) (hS : incS d.site = 1) (hD : incD d.site = 0) (b : Fin 2) :
    okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = uses b (i + 1) ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = uses b i ∧
      okPolls (mbarLoc L (g / L.block) (.svDone b)) ((X.tr g).take k) = uses b (i + 1) ∧
      arrivals (mbarLoc L (g / L.block) (.dequantReady b)) ((X.tr g).take k) = uses b i := by
  obtain ⟨-, -, hn⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := hn b
  simp only [wg2_okPolls hp hX hFw hw, wg2_arrivals hp hX hFw hw]
  simp only [MbarRow.loc, hR, hS, hD, incF, Nat.add_zero] at h1 h2 h3 h4 ⊢
  exact ⟨h1, h4, h2, h3⟩

/-- The block's slot is the slot of its index. -/
private theorem slot_of_counts {i : Nat} {d : Control.D}
    {n : Cnt → Nat} (h : LoopCounts L g d n i) : slotF d.sb = MbarRow.slot2 i := by
  rw [h.1, slotF_slot2]

/-- **A raw load's location** (a lane of warps 8-11): the load at `dqRawPc r s` reads eight bytes at
tile row `g % 128 / 8 + 16 r`, column `8 (g % 8) + 64 s` of a raw tile `b`, at use `v`. -/
theorem dequant_rawLoc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {r s : Nat} (hr : r < 4) (hs : s < 8)
    (hpc : pc = dqRawPc r s) :
    ∃ (b : Fin 2) (v : Nat), a.size = 8 ∧
      a.loc.addr = L.sharedBase + (Region.raw b).lo +
        (576 * (g % 128 / 8 + 16 * r) + (g % 8 * 8 + 64 * s)) ∧
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = v := by
  have hub : ∀ f, Kind.rd a bs ≠ .ub f := fun _ h => by cases h
  have hrange : 2606 ≤ pc ∧ pc < 3611 := by rw [hpc]; unfold dqRawPc; split_ifs <;> omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨hpcd, hk⟩, hw1, hw2⟩ := dequant_state hp hJ hi hev hpcσ hrange
  have hc := hR (state_ub hX hσ he)
  rw [show (fun c => n (.dequant c)) = fun c => ((X.tr g).take k).countP (Dequant.cls c) from
    funext fun c => state_count hσ (.dequant c)] at hc
  have hc := hc (wg2_take_noUb hX he)
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hq : site.pc = dqRawPc r s := hpcd.symm.trans hpc
  cases site with
  | raw r' s' =>
    obtain ⟨rfl, rfl⟩ := raw_inj (r := r') (s := s') (r' := ⟨r, hr⟩) (i := ⟨s, hs⟩) hq
    obtain ⟨i, -, hi'⟩ := hc
    obtain ⟨h1, h2, -, -⟩ := slot_counts hp hX hFw ⟨hw1, hw2⟩ hi' rfl rfl rfl (slotF sb)
    have hsl : slotF sb = MbarRow.slot2 i := slot_of_counts hi'
    have h1' : uses (slotF sb) (i + 1) = uses (slotF sb) i + 1 := by
      rw [uses_succ, hsl]; simp
    rcases hk with ⟨a', bs', hk, hl, hsz⟩ | ⟨f, hk⟩
    · simp only [Kind.rd.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.rawRd_loc hp] at hl
      refine ⟨slotF sb, _, hsz, ?_, h1.trans h1', h2⟩
      rw [hl]; simp only [wsLoc, Region.lo]; omega
    · cases hk
  | scale r' => exact absurd hq (scale_ne_raw r' ⟨r, hr⟩ ⟨s, hs⟩)
  | store r' s' => exact absurd hq (store_ne_raw r' ⟨r, hr⟩ s' ⟨s, hs⟩)
  | _ =>
    exfalso
    simp only [Site.pc] at hq
    unfold dqRawPc at hq
    split_ifs at hq <;> omega

/-- **A scale load's location** (valid data): the load at `dqScalePc r` reads four bytes at tile row
`g % 128 / 8 + 16 r`, column `512 + 4 j` of a raw tile `b`, at use `v`, where `j` is the number of
the lane's earlier events at that pc modulo 4. -/
theorem dequant_scaleLoc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) {r : Nat} (hr : r < 4) (hpc : pc = dqScalePc r)
    (hv : DqValid X g k) :
    ∃ (b : Fin 2) (v : Nat), a.size = 4 ∧
      a.loc.addr = L.sharedBase + (Region.raw b).lo + (576 * (g % 128 / 8 + 16 * r) + (512 + 4 *
        (((X.tr g).take k).countP (fun x => decide (x.pc = dqScalePc r)) % 4))) ∧
      okPolls (mbarLoc L (g / L.block) (.rawReady b)) ((X.tr g).take k) = v + 1 ∧
      arrivals (mbarLoc L (g / L.block) (.rawFree b)) ((X.tr g).take k) = v := by
  have hub : ∀ f, Kind.rd a bs ≠ .ub f := fun _ h => by cases h
  have hrange : 2606 ≤ pc ∧ pc < 3611 := by rw [hpc]; unfold dqScalePc; omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, n, rfl, hR, ⟨hpcd, hk⟩, hw1, hw2⟩ := dequant_state hp hJ hi hev hpcσ hrange
  obtain ⟨st, hst, hI, -⟩ := followD hp hX hFw ⟨hw1, hw2⟩ he ⟨_, hσ⟩ hv k le_rfl
  have h1 := control_of_data hst
  rw [hσ] at h1
  obtain ⟨dD, nD, rfl, hdc⟩ : ∃ dD nD, st = (.inr ⟨.inl .dequant, dD⟩, nD) ∧ dD.c = d := by
    rcases deq_slot hFw ⟨hw1, hw2⟩ hg hst with ⟨b, hb⟩ | ⟨dD, hdD⟩
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inl b := hb
      simp [eraseThread, Code.eraseSum] at h1
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inr ⟨.inl .dequant, dD⟩ := hdD
      simp [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, dequantErase] at h1
      exact ⟨dD, nq, rfl, h1.1.symm⟩
  have hc := hR (state_ub hX hσ he)
  rw [show (fun c => n (.dequant c)) = fun c => ((X.tr g).take k).countP (Dequant.cls c) from
    funext fun c => state_count hσ (.dequant c)] at hc
  have hc := hc (wg2_take_noUb hX he)
  have hI' := hI dD rfl
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  have hq : site.pc = dqScalePc r := hpcd.symm.trans hpc
  cases site with
  | scale r' =>
    obtain rfl : r' = ⟨r, hr⟩ := scalePc_inj (r := r') (r' := ⟨r, hr⟩) (by
      rw [← scale_pc]; exact hq)
    obtain ⟨i, -, hi'⟩ := hc
    obtain ⟨h1, h2, -, -⟩ := slot_counts hp hX hFw ⟨hw1, hw2⟩ hi' rfl rfl rfl (slotF sb)
    have hsl : slotF sb = MbarRow.slot2 i := slot_of_counts hi'
    have h1' : uses (slotF sb) (i + 1) = uses (slotF sb) i + 1 := by
      rw [uses_succ, hsl]; simp
    have hpos := hI'.pos ⟨r, hr⟩
    rw [hdc] at hpos
    simp only [↓reduceIte] at hpos
    rw [List.countP_eq_length_filter] at *
    rcases hk with ⟨a', bs', hk, hl, hsz⟩ | ⟨f, hk⟩
    · simp only [Kind.rd.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.scale_loc hp] at hl
      refine ⟨slotF sb, _, hsz, ?_, h1.trans h1', h2⟩
      rw [hl, ← hpos]
      simp only [wsLoc, Region.lo, atPc]
      omega
    · cases hk
  | raw r' s' => exact absurd hq (raw_ne_scale r' ⟨r, hr⟩ s')
  | store r' s' => exact absurd hq (store_ne_scale r' ⟨r, hr⟩ s')
  | _ =>
    exfalso
    simp only [Site.pc] at hq
    unfold dqScalePc at hq
    omega

/-! ### Lists -/

private theorem atPc_cons (x : Event) (l : List Event) (p : Nat) :
    atPc (x :: l) p = (if x.pc = p then [x] else []) ++ atPc l p := by
  unfold atPc
  rw [List.filter_cons]
  by_cases h : x.pc = p <;> simp [h]

/-- The `i`-th event at pc `p` of a list is the event at an index whose prefix holds `i` of them. -/
private theorem atPc_idx : ∀ (l : List Event) (p i : Nat), i < (atPc l p).length →
    ∃ kj < l.length, ∃ x, l[kj]? = some x ∧ (atPc l p)[i]? = some x ∧
      (atPc (l.take kj) p).length = i := by
  intro l p
  induction l with
  | nil => intro i hi; simp [atPc] at hi
  | cons x l ih =>
    intro i hi
    rw [atPc_cons] at hi ⊢
    by_cases hx : x.pc = p
    · simp only [hx, ↓reduceIte, List.singleton_append, List.length_cons] at hi ⊢
      cases i with
      | zero => exact ⟨0, by simp, x, by simp, by simp, by simp [atPc]⟩
      | succ i =>
        obtain ⟨kj, hkj, y, h2, h3, h4⟩ := ih i (by omega)
        refine ⟨kj + 1, by simpa using hkj, y, by simpa using h2, by simpa using h3, ?_⟩
        rw [List.take_succ_cons, atPc_cons]; simpa [hx] using h4
    · simp only [hx, ↓reduceIte, List.nil_append] at hi ⊢
      obtain ⟨kj, hkj, y, h2, h3, h4⟩ := ih i hi
      refine ⟨kj + 1, by simpa using hkj, y, by simpa using h2, h3, ?_⟩
      rw [List.take_succ_cons, atPc_cons]; simpa [hx] using h4

/-- An event at pc `p` whose prefix holds `i` events at `p`, `i` at least the count of `l1`, lies
after `l1`. -/
private theorem idx_ge {l1 l2 : List Event} {p i kj : Nat} {x : Event}
    (hi : (atPc l1 p).length ≤ i) (hk : (l1 ++ l2)[kj]? = some x) (hx : x.pc = p)
    (hc : (atPc ((l1 ++ l2).take kj) p).length = i) : l1.length ≤ kj := by
  by_contra hlt
  have hkj : kj < l1.length := by omega
  have h1 : (l1 ++ l2)[kj]? = l1[kj]? := List.getElem?_append_left hkj
  rw [h1] at hk
  have h2 : (l1 ++ l2).take kj = l1.take kj := List.take_append_of_le_length (by omega)
  rw [h2] at hc
  have h3 : l1.take (kj + 1) = l1.take kj ++ [x] := by
    rw [List.take_add_one, hk]; rfl
  have h4 : (atPc (l1.take (kj + 1)) p).length ≤ (atPc l1 p).length :=
    ((List.take_sublist _ _).filter _).length_le
  rw [h3, atPc_eq hx, List.length_append, List.length_singleton, hc] at h4
  omega

/-- No poll and no arrival among the events after `l1`: the prefixes past `l1` count as the
whole list. -/
private theorem counts_take {l1 l2 : List Event} {kj : Nat} (hq : ∀ x ∈ l2, ∀ l,
    okPoll l x = false ∧ arrivesOn l x = false) (hk : l1.length ≤ kj) (l : Loc) :
    okPolls l ((l1 ++ l2).take kj) = okPolls l (l1 ++ l2) ∧
      arrivals l ((l1 ++ l2).take kj) = arrivals l (l1 ++ l2) := by
  have h0 : ∀ l' : List Event, (∀ x ∈ l', ∀ l, okPoll l x = false ∧ arrivesOn l x = false) →
      okPolls l l' = 0 ∧ arrivals l l' = 0 := fun l' h =>
    ⟨List.countP_eq_zero.mpr fun x hx => by simpa using (h x hx l).1,
      List.countP_eq_zero.mpr fun x hx => by simpa using (h x hx l).2⟩
  have h2 := h0 (l2.take (kj - l1.length)) fun x hx => hq x (List.mem_of_mem_take hx)
  have h3 := h0 l2 hq
  rw [List.take_append, List.take_of_length_le (by omega : l1.length ≤ kj)]
  simp only [okPolls, arrivals, List.countP_append] at h2 h3 ⊢
  omega

/-! ### The events of a row before a store -/

private theorem lastN_get {A : List Event} {n j : Nat} (hn : n ≤ A.length) :
    (lastN n A).length = n ∧ (lastN n A)[j]? = A[A.length - n + j]? := by
  refine ⟨lastN_length hn, ?_⟩
  unfold lastN
  rw [List.getElem?_drop]

/-- **The `j`-th of the last `n` events at pc `p` before event `k`**, when the last `n` all come
after
a point `l1` from which every event is a row event (`Since`): its index, its pc, its prefix count at
`p`, and that no poll and no arrival lies between it and event `k`. -/
private theorem pick_event (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {e : Event} (he : X.get (g, k) = some e) {p n j : Nat} (hj : j < n)
    (hs : Since ((X.tr g).take k) p n) :
    (lastAt X g k p n).length = n ∧ ∃ kj x, kj < k ∧ X.get (g, kj) = some x ∧ x.pc = p ∧
      (lastAt X g k p n)[j]? = some x ∧ (∀ f, x.kind ≠ .ub f) ∧
      (atPc ((X.tr g).take kj) p).length = (atPc ((X.tr g).take k) p).length - n + j ∧
      ∀ l, okPolls l ((X.tr g).take kj) = okPolls l ((X.tr g).take k) ∧
        arrivals l ((X.tr g).take kj) = arrivals l ((X.tr g).take k) := by
  obtain ⟨l1, l2, hl, hn, hr2⟩ := hs
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hlen : ((X.tr g).take k).length = k := by simp; omega
  have hq : ∀ x ∈ l2, ∀ l, okPoll l x = false ∧ arrivesOn l x = false := by
    intro x hx
    have hxl : x ∈ (X.tr g).take k := by rw [hl]; exact List.mem_append_right _ hx
    obtain ⟨j', hj', hget⟩ := mem_take_get hxl
    exact dequant_rowQuiet hp hX hFw hget (fun f h => by
      obtain ⟨pcx, kd⟩ := x; cases h; have := ub_last hX hget he; omega) (hr2 x hx)
  have hA : atPc ((X.tr g).take k) p = atPc l1 p ++ atPc l2 p := by
    rw [hl]; simp [atPc, List.filter_append]
  have hAl : (atPc ((X.tr g).take k) p).length = (atPc l1 p).length + (atPc l2 p).length := by
    rw [hA, List.length_append]
  obtain ⟨kj, hkj, x, hx1, hx2, hx3⟩ := atPc_idx ((X.tr g).take k) p
    ((atPc ((X.tr g).take k) p).length - n + j) (by omega)
  have hxpc : x.pc = p := by
    have := List.mem_of_getElem? hx2
    simpa [atPc] using (List.mem_filter.mp this).2
  have hge : l1.length ≤ kj := idx_ge (l1 := l1) (l2 := l2)
    (i := (atPc ((X.tr g).take k) p).length - n + j) (by omega)
    (by rw [← hl]; exact hx1) hxpc (by rw [← hl]; exact hx3)
  have hkk : kj < k := by omega
  have hget : X.get (g, kj) = some x := by
    have := List.getElem?_take_of_lt (l := X.tr g) hkk
    show (X.tr g)[kj]? = some x
    rw [← this]; exact hx1
  have htk : ((X.tr g).take k).take kj = (X.tr g).take kj := by
    rw [List.take_take]; congr 1; omega
  obtain ⟨hl4, hl5⟩ := lastN_get (A := atPc ((X.tr g).take k) p) (n := n) (j := j) (by omega)
  refine ⟨hl4, kj, x, hkk, hget, hxpc, ?_, fun f h => ?_, ?_, fun l => ?_⟩
  · exact hl5.trans hx2
  · obtain ⟨pcx, kd⟩ := x; cases h; have := ub_last hX hget he; omega
  · rw [← htk]; exact hx3
  · rw [← htk, hl]; exact counts_take hq hge l

/-- Two uses of a slot, one more than the other, are the block's slot. -/
private theorem slot_pick {b : Fin 2} {i v : Nat} (h1 : uses b (i + 1) = v + 1)
    (h2 : uses b i = v) : b = MbarRow.slot2 i := by
  by_contra h
  have := uses_succ b i
  simp only [h, ↓reduceIte] at this
  omega

/-- **The loads a chunk store consumes** (valid data): the store `(r, s)` of the lane into
dequantized tile `bw`, at use `u` (`u` arrivals on `dequantReady bw` before it), consumes a last raw
load and four last scale loads that are loads of its own block: after the `u + 1`-th poll of
`rawReady bw`, with no poll between them and the store. The raw load reads row
`g % 128 / 8 + 16 r`, column `8 (g % 8) + 64 s` of raw tile `bw`; scale load `j` (in trace order)
reads
the same row's column `512 + 4 j`. -/
theorem dequant_store_loads (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {a : Acc} {bs : List Byte} {r s : Nat} (hr : r < 4) (hs : s < 8)
    (he : X.get (g, k) = some ⟨dqStorePc r s, .wr a bs⟩) (hv : DqValid X g k) {bw : Fin 2}
    (hws : MemRow.WsAcc L (g / L.block) ((Region.dequant bw).lo + MemRow.dqChunk (g % 128) r s)
      16 a) :
    ∃ u : Nat, arrivals (mbarLoc L (g / L.block) (.dequantReady bw)) ((X.tr g).take k) = u ∧
      okPolls (mbarLoc L (g / L.block) (.rawReady bw)) ((X.tr g).take k) = u + 1 ∧
      (∃ (kr : Nat) (ar : Acc) (bsr : List (Option Byte)), kr < k ∧
        X.get (g, kr) = some ⟨dqRawPc r s, .rd ar bsr⟩ ∧
        lastAt X g k (dqRawPc r s) 1 = [⟨dqRawPc r s, .rd ar bsr⟩] ∧ ar.size = 8 ∧
        ar.loc.addr = L.sharedBase + (Region.raw bw).lo +
          (576 * (g % 128 / 8 + 16 * r) + (g % 8 * 8 + 64 * s)) ∧
        okPolls (mbarLoc L (g / L.block) (.rawReady bw)) ((X.tr g).take kr) = u + 1) ∧
      (lastAt X g k (dqScalePc r) 4).length = 4 ∧
      ∀ j < 4, ∃ (kj : Nat) (aj : Acc) (bsj : List (Option Byte)), kj < k ∧
        X.get (g, kj) = some ⟨dqScalePc r, .rd aj bsj⟩ ∧
        (lastAt X g k (dqScalePc r) 4)[j]? = some ⟨dqScalePc r, .rd aj bsj⟩ ∧ aj.size = 4 ∧
        aj.loc.addr = L.sharedBase + (Region.raw bw).lo +
          (576 * (g % 128 / 8 + 16 * r) + (512 + 4 * j)) ∧
        okPolls (mbarLoc L (g / L.block) (.rawReady bw)) ((X.tr g).take kj) = u + 1 := by
  have hub : ∀ f, Kind.wr a bs ≠ .ub f := fun _ h => by cases h
  have hrange : 2606 ≤ dqStorePc r s ∧ dqStorePc r s < 3611 := by
    unfold dqStorePc; split_ifs <;> omega
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, n, rfl, hR, ⟨hpcd, hk⟩, hw1, hw2⟩ := dequant_state hp hJ hi hev hpcσ hrange
  obtain ⟨st, hst, hI, -⟩ := followD hp hX hFw ⟨hw1, hw2⟩ he ⟨_, hσ⟩ hv k le_rfl
  have h1 := control_of_data hst
  rw [hσ] at h1
  obtain ⟨dD, nD, rfl, hdc⟩ : ∃ dD nD, st = (.inr ⟨.inl .dequant, dD⟩, nD) ∧ dD.c = d := by
    rcases deq_slot hFw ⟨hw1, hw2⟩ hg hst with ⟨b, hb⟩ | ⟨dD, hdD⟩
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inl b := hb
      simp [eraseThread, Code.eraseSum] at h1
    · obtain ⟨q, nq⟩ := st
      obtain rfl : q = .inr ⟨.inl .dequant, dD⟩ := hdD
      simp [eraseThread, Code.eraseSum, Code.eraseStubs, eraseFrag, dequantErase] at h1
      exact ⟨dD, nq, rfl, h1.1.symm⟩
  have hc := hR (state_ub hX hσ he)
  rw [show (fun c => n (.dequant c)) = fun c => ((X.tr g).take k).countP (Dequant.cls c) from
    funext fun c => state_count hσ (.dequant c)] at hc
  have hc := hc (wg2_take_noUb hX he)
  have hI' := hI dD rfl
  obtain ⟨site, el, ac, l0, l1, cnt, sb, pb⟩ := d
  cases site with
  | store r' s' =>
    have hq : (Site.store r' s').pc = dqStorePc r s := hpcd.symm
    obtain ⟨rfl, rfl⟩ : r' = ⟨r, hr⟩ ∧ s' = ⟨s, hs⟩ := by
      have := r'.isLt; have := s'.isLt
      rw [store_pc] at hq
      unfold dqStorePc at hq
      refine ⟨Fin.ext (show r'.val = r from ?_), Fin.ext (show s'.val = s from ?_)⟩ <;>
        split_ifs at hq <;> omega
    obtain ⟨i, -, hi'⟩ := hc
    have hsc := slot_counts hp hX hFw ⟨hw1, hw2⟩ hi' rfl rfl rfl
    obtain ⟨hp1, ha1, -, hd1⟩ := hsc (slotF sb)
    have hsl : slotF sb = MbarRow.slot2 i := slot_of_counts hi'
    rcases hk with ⟨a', bs', hk, hl, hsz⟩ | ⟨f, hk⟩
    · simp only [Kind.wr.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      rw [Dequant.store_loc hp] at hl
      have hbw : bw = slotF sb := by
        have h := (hws.1.symm.trans hl)
        simp only [wsLoc, Loc.mk.injEq] at h
        have h2 := h.2.2
        revert h2
        cases sb <;> fin_cases bw <;> simp [slotF, Region.lo]
      subst hbw
      have hsite : dD.c.site = .store ⟨r, hr⟩ ⟨s, hs⟩ := by rw [hdc]
      have hpos := hI'.pos ⟨r, hr⟩
      rw [hsite, ite0_ne (fun h => by cases h)] at hpos
      have hsR := hI'.qrw ⟨r, hr⟩ ⟨s, hs⟩ (by rw [hsite]; simp [Done])
      have hsS := hI'.qsc ⟨r, hr⟩ (by rw [hsite]; simp [InRow])
      have hsr : (uses (slotF sb) (i + 1)) = uses (slotF sb) i + 1 := by
        rw [uses_succ, hsl]; simp
      refine ⟨uses (slotF sb) i, hd1, by rw [hp1, hsr], ?_, ?_⟩
      · obtain ⟨hlen, kr, x, hkr, hget, hxpc, hnth, hnoub, -, hq⟩ :=
          pick_event hp hX hFw he (p := dqRawPc r s) (n := 1) (j := 0) (by omega) hsR
        obtain ⟨-, ar, bsr, hkind, hsz8⟩ := dequant_raw_load hp hX hFw hget hnoub hr hs hxpc
        obtain ⟨pcx, kx⟩ := x
        simp only at hxpc hkind
        subst hxpc hkind
        obtain ⟨b, v, -, haddr, hpl, har⟩ := dequant_rawLoc hp hX hFw hget hr hs rfl
        obtain ⟨hpk, hak, -, -⟩ := hsc b
        rw [(hq _).1] at hpl
        rw [(hq _).2] at har
        obtain rfl : b = slotF sb :=
          (slot_pick (hpk.symm.trans hpl) (hak.symm.trans har)).trans hsl.symm
        have hv' : v = uses (slotF sb) i := by rw [← har, ha1]
        subst hv'
        obtain ⟨y, hy⟩ := List.length_eq_one_iff.mp hlen
        rw [hy] at hnth
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hnth
        refine ⟨kr, ar, bsr, hkr, hget, by rw [hy, hnth], hsz8, haddr, ?_⟩
        rw [(hq _).1]; exact hpl
      · have hpos' : (atPc ((X.tr g).take k) (dqScalePc r)).length % 4 = 0 := hpos
        have h4 : 4 ≤ (atPc ((X.tr g).take k) (dqScalePc r)).length := by
          obtain ⟨l1, l2, hl, hn, -⟩ := hsS
          rw [hl]; simp only [atPc, List.filter_append, List.length_append] at hn ⊢
          omega
        refine ⟨(pick_event hp hX hFw he (p := dqScalePc r) (n := 4) (j := 0) (by omega)
          hsS).1, fun j hj => ?_⟩
        obtain ⟨-, kj, x, hkj, hget, hxpc, hnth, hnoub, hcnt, hq⟩ :=
          pick_event hp hX hFw he (p := dqScalePc r) (n := 4) (j := j) hj hsS
        obtain ⟨-, aj, bsj, hkind, hsz4⟩ := dequant_scale_load hp hX hFw hget hnoub hr hxpc
        obtain ⟨pcx, kx⟩ := x
        simp only at hxpc hkind
        subst hxpc hkind
        obtain ⟨b, v, -, haddr, hpl, har⟩ := dequant_scaleLoc hp hX hFw hget hr rfl
          (fun j' hj' e' he' => hv j' (by omega) e' he')
        have hcp : ((X.tr g).take kj).countP (fun x => decide (x.pc = dqScalePc r)) =
            (atPc ((X.tr g).take kj) (dqScalePc r)).length := List.countP_eq_length_filter
        rw [hcp, hcnt, show ((atPc ((X.tr g).take k) (dqScalePc r)).length - 4 + j) % 4 = j by
          omega] at haddr
        obtain ⟨hpk, hak, -, -⟩ := hsc b
        rw [(hq _).1] at hpl
        rw [(hq _).2] at har
        obtain rfl : b = slotF sb := (slot_pick (hpk.symm.trans hpl) (hak.symm.trans har)).trans
          hsl.symm
        have hv' : v = uses (slotF sb) i := by rw [← har, ha1]
        subst hv'
        refine ⟨kj, aj, bsj, hkj, hget, hnth, hsz4, haddr, ?_⟩
        rw [(hq _).1]; exact hpl
    · cases hk
  | scale r' =>
    exfalso
    have hq : (Site.scale r').pc = dqStorePc r s := hpcd.symm
    have := r'.isLt
    simp only [Site.pc, rowBase] at hq
    unfold dqStorePc at hq
    split_ifs at hq <;> omega
  | raw r' s' =>
    exfalso
    have hq : (Site.raw r' s').pc = dqStorePc r s := hpcd.symm
    have := r'.isLt; have := s'.isLt
    simp only [Site.pc, rowBase] at hq
    unfold dqStorePc at hq
    split_ifs at hq <;> omega
  | _ =>
    exfalso
    simp only [Site.pc] at hpcd
    unfold dqStorePc at hpcd
    split_ifs at hpcd <;> omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
