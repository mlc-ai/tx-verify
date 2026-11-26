-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.Bar0
public import Lemmas.Tmem.AccessCp
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Bar0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Tmem
import Lemmas.Protocol.CountNth
import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-! # Every Tensor Memory access follows lane 0 of warp 0's allocation (`LifeCp.alloc_before`)

The allocation is handed to every access through barrier 0 (`bar0_pub`):

* an access (an MMA, a copy, a load or a store) is past pc 97, so its lane has a barrier-0 event
  before it (`bar0_before`), and its first one is the CTA's `bar.sync 0` (`startup_bar0`);
* that barrier completed, so lane 0 of warp 0 of the CTA made its first barrier-0 arrival
  (`NamedBar.Sources.member_arrival_any`; a lane that exits has a barrier-0 event first,
  `bar0_exit`); at it, the lane has made its two paired operations (`startup_bar0_tmem`);
* the first of them, before any barrier-0 event of the lane, is a startup event and so the
  allocation of 512 columns (`startup_tmemShape`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An access of the class is a `tcgen05` event past the startup. -/
private theorem op_event (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h f : Nat} (hop : Tmem.AccessCp.Op X (h, f)) :
    ∃ e, X.get (h, f) = some e ∧ 97 < e.pc := by
  have hR := tmem_rows hp hX hFw
  obtain ⟨pc, c, he, hc⟩ : ∃ pc c, X.get (h, f) = some ⟨pc, .tc c⟩ ∧
      ∀ grp dst act, c ≠ .resource grp dst act := by
    rcases hop with ⟨_, _, _, _, pc, he⟩ | ⟨_, pc, he⟩ | ⟨_, _, _, pc, he⟩ | ⟨_, _, _, pc, he⟩ <;>
      exact ⟨pc, _, he, fun _ _ _ h => by cases h⟩
  refine ⟨_, he, ?_⟩
  have hg := Frame.lt_of_get hX he
  rcases hR.place hg he rfl with h | h | h | h | h | h | h
  · obtain ⟨-, ⟨dst, h1⟩ | h1⟩ := hR.startup hg he h rfl <;> cases h1 <;>
      exact absurd rfl (hc _ _ _)
  all_goals simp only [Wg0At, Wg1At, MmaAt, TmaAt, IndexAt, DequantAt] at h; simp only; omega

/-- A barrier-0 event with no barrier-0 event before it is a startup event. -/
private theorem first_bar0_startup (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g i : Nat} {e : Event} (he : X.get (g, i) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (h0 : ((X.tr g).take i).countP isBar0 = 0) : StartupAt e.pc := by
  by_contra hn
  have := bar0_before hp hX hFw he hub (by simp only [StartupAt] at hn; omega)
  omega

/-- A member of a prefix of a trace is an event of it before the prefix's end. -/
private theorem get_of_take {g n j : Nat} {x : Event} (h : ((X.tr g).take n)[j]? = some x) :
    j < n ∧ X.get (g, j) = some x := by
  have hj : j < n := by
    have := (List.getElem?_eq_some_iff.mp h).1
    simp only [List.length_take] at this
    omega
  refine ⟨hj, ?_⟩
  change (X.tr g)[j]? = _
  rw [← h, List.getElem?_take, ite_eq_left hj]

/-- **Every access follows lane 0 of warp 0's allocation** of its CTA, in causality, and that
lane has an event after the allocation. -/
theorem alloc_before (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hB : Bar0Rows L X) {e : EvId} (hop : Tmem.AccessCp.Op X e) :
    ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block + 0 * 32, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block + 0 * 32)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block + 0 * 32, j) e := by
  have hb := hp.block
  obtain ⟨h, f⟩ := e
  obtain ⟨ev, he, hpc⟩ := op_event hp hX hFw hop
  have hg := Frame.lt_of_get hX he
  have hflen : f < (X.tr h).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr h)[f]? = _ from he)).1
  have hf0 := bar0_before hp hX hFw he (fun f' hf' => by
    obtain ⟨pc, kd⟩ := ev; simp only at hpc hf'; subst hf'; rcases hop with
      ⟨_, _, _, _, _, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, _, _, h'⟩ | ⟨_, _, _, _, h'⟩ <;>
      rw [he] at h' <;> cases h') hpc
  -- the lane's first barrier-0 event
  obtain ⟨b, evb, hbget, hbid, hbc⟩ :=
    MbarRing.Slot.exists_nth_countP isBar0 (show 0 + 1 ≤ ((X.tr h).take f).countP isBar0 by omega)
  obtain ⟨hbf, hgb⟩ := get_of_take hbget
  rw [List.take_take, Nat.min_eq_left hbf.le] at hbc
  obtain ⟨pcb, kb⟩ := evb
  obtain ⟨cntb, mb, rfl⟩ : ∃ cnt mode, kb = .bar 0 cnt mode := by
    cases kb <;> simp [isBar0] at hbid
    rename_i id c md
    cases id <;> simp at hbid
    exact ⟨c, md, rfl⟩
  obtain ⟨rfl, rfl, -⟩ := startup_bar0 hp hX hFw hgb rfl hbc
  -- lane 0 of warp 0 of the CTA
  set z := (h / L.block) * L.block + 0 * 32 with hzdef
  have hcta : z / L.block = h / L.block := by rw [hzdef, hb]; omega
  have hz : z < L.threads := by
    show (h / L.block) * L.block + 0 * 32 < L.grid * L.block
    have hg' : h < L.grid * L.block := hg
    rw [hb] at hg' ⊢
    omega
  have hzw : MbarRow.warp L z = 0 := by
    simp only [MbarRow.warp, tidOf_x_eq hp]
    rw [hzdef, hb]
    omega
  -- its first barrier-0 arrival
  obtain ⟨i, pci, mi, hzi, hci⟩ := NamedBar.Sources.member_arrival_any hX (bar0_sources hp hB)
    (bar0_shape hp) (f := (h, b)) hgb (by simp only; omega) hcta
    (by simp only [Finset.mem_range]; rw [hzdef, hb]; omega)
    (fun ⟨jx, pcx, hx⟩ => by
      have h1 := bar0_exit hp hX hFw hx
      obtain ⟨i, ev', hi, hbi, hci⟩ := MbarRing.Slot.exists_nth_countP isBar0
        (show 0 + 1 ≤ ((X.tr z).take jx).countP isBar0 by omega)
      obtain ⟨hij, hgi⟩ := get_of_take hi
      rw [List.take_take, Nat.min_eq_left hij.le] at hci
      obtain ⟨pc', k'⟩ := ev'
      obtain ⟨c', m', rfl⟩ : ∃ cnt mode, k' = .bar 0 cnt mode := by
        cases k' <;> simp [isBar0] at hbi
        rename_i id c md
        cases id <;> simp at hbi
        exact ⟨c, md, rfl⟩
      obtain ⟨rfl, -, -⟩ := startup_bar0 hp hX hFw hgi rfl hci
      refine ⟨i, pc', m', hgi, ?_⟩
      rw [← isBar0_eq, hci, hbc])
  rw [← isBar0_eq, hbc] at hci
  have hilen : i < (X.tr z).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr z)[i]? = _ from hzi)).1
  have hzS := first_bar0_startup hp hX hFw hzi (fun _ h => by cases h) hci
  have h2 := startup_bar0_tmem hp hX hFw hzi hzS rfl hzw
  -- its first paired operation
  obtain ⟨j, x, hxget, hxop, hxc⟩ := MbarRing.Slot.exists_nth_countP Tmem.Pair.isTmemOp
    (show 0 + 1 ≤ ((X.tr z).take i).countP Tmem.Pair.isTmemOp by
      have : Tmem.Pair.tmemOps ((X.tr z).take i) = 2 := h2
      unfold Tmem.Pair.tmemOps at this
      omega)
  obtain ⟨hji, hgj⟩ := get_of_take hxget
  rw [List.take_take, Nat.min_eq_left hji.le] at hxc
  have hj0 : ((X.tr z).take (j + 1)).countP isBar0 = 0 := by
    have hle : ((X.tr z).take (j + 1)).countP isBar0 ≤ ((X.tr z).take i).countP isBar0 :=
      (List.take_sublist_take_left (by omega)).countP_le
    omega
  obtain ⟨pcx, kx⟩ := x
  obtain ⟨grp, dst, act, rfl⟩ : ∃ grp dst act, kx = .tc (.resource grp dst act) := by
    cases kx <;> simp [Tmem.Pair.isTmemOp] at hxop
    rename_i c
    cases c <;> simp at hxop
    exact ⟨_, _, _, rfl⟩
  have hxS := first_bar0_startup hp hX hFw hgj (fun _ h => by cases h)
    (by
      have hle : ((X.tr z).take j).countP isBar0 ≤ ((X.tr z).take (j + 1)).countP isBar0 :=
        (List.take_sublist_take_left (by omega)).countP_le
      omega)
  have hsh := startup_tmemShape hp hX hFw hgj hxS rfl
  have h0 : Tmem.Pair.tmemOps ((X.tr z).take j) = 0 := hxc
  rw [h0] at hsh
  simp only [Tmem.Pair.TmemShape] at hsh
  subst hsh
  refine ⟨j, pcx, grp, dst, 512, hgj, by omega, ?_⟩
  exact bar0_pub hp hX hFw hB ⟨hz, hg, hcta⟩ hj0 hflen (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmRace
