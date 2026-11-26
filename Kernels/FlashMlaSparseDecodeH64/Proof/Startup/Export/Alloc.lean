-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmemCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.StartEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Measure
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Tmem
import Lemmas.Flow.NthEv
import Lemmas.Flow.AllocTmpl

@[expose] public section

/-! # The startup's allocation word

The startup's facts on the shared word `Region.tmemWord` that receives the allocated Tensor
Memory column, over the trace:

* `wr_lane`: a startup store (the allocation's second step) is made by lane 0;
* `wr_unique`: a CTA's startup stores are one event (lane 0 of warp 0 stores once: the startup
  machine's sites rise along a thread, `Startup.measure_step`);
* `rd_alloc`: the read-back at pc 92 follows its thread's allocation request naming the word
  (the startup's count of paired Tensor Memory operations is 1 there, and the only operation
  before it is the allocation, `startup_tmemShape`);
* `alloc_after`, `alloc_store`: the next event of a lane whose last event is the allocation is
  lane 0's store of the word at pc 91, or another lane's read-back at pc 92 (`Sched.NextEv`).

Every startup state of a thread is reached from startup states only (`pred_inl`), so a state
before a startup state is a startup state of lower measure (`chain`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A startup state of the thread machine came from a startup state by a startup step. -/
private theorem pred_inl {k : Nat} {e : Event} {d : Startup.D} {n : Cls → Nat}
    (he : (X.tr g)[k]? = some e)
    (hσ : Frame.stateAt (thread P L) X g (k + 1) = some (some (.inl d, n))) :
    ∃ d0 n0, Frame.stateAt (thread P L) X g k = some (some (.inl d0, n0)) ∧
      Startup.succ L g d0 e = some (some d) := by
  rw [Frame.stateAt_succ (C := thread P L) he] at hσ
  rcases h : Frame.stateAt (thread P L) X g k with _ | _ | ⟨s, n0⟩ <;> rw [h] at hσ
  · cases hσ
  · cases hσ
  · change (thread P L g).next (s, n0) e = _ at hσ
    rcases s with d0 | ⟨i | r, d'⟩
    · refine ⟨d0, n0, rfl, ?_⟩
      rw [next_startup] at hσ
      rcases hs : Startup.succ L g d0 e with _ | _ | d1 <;> rw [hs] at hσ
      · cases hσ
      · cases hσ
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hσ
        obtain ⟨hσ, -⟩ := hσ
        unfold Code.enter at hσ
        split at hσ
        · cases hσ
        · cases hσ
          rfl
    · rw [next_frag] at hσ
      rcases (frag P L g i).next d' e with _ | _ | d1 <;> simp at hσ
    · rw [Code.roleThread_stub] at hσ
      cases hσ

/-- **A state before a startup state** is a startup state, lower by the events between. -/
private theorem chain {j : Nat} {d : Startup.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g j = some (some (.inl d, n)))
    (hj : j ≤ (X.tr g).length) {i : Nat} (hi : i ≤ j) :
    ∃ d0 n0, Frame.stateAt (thread P L) X g i = some (some (.inl d0, n0)) ∧
      Startup.measure d0 + (j - i) ≤ Startup.measure d := by
  induction j generalizing d n with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact ⟨d, n, hσ, by omega⟩
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact ⟨d, n, hσ, by omega⟩
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨d0, n0, hσ0, hs⟩ := pred_inl he hσ
    have hm := Startup.measure_step hs
    obtain ⟨d1, n1, hσ1, hle⟩ := ih hσ0 (by omega) (by omega)
    exact ⟨d1, n1, hσ1, by omega⟩

/-- A startup event is fired from a startup state with its site's shape. -/
private theorem ev_inl (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hpc : e.pc < 103) :
    ∃ d n, Frame.stateAt (thread P L) X g k = some (some (.inl d, n)) ∧ Startup.Ev L g d e ∧
      Startup.exitOf d = none := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, -, -, hE, hx, -⟩ := startup_state hJ hi hev hpc' hpc
  exact ⟨d, n, hσ, hE, hx⟩

/-- A startup state whose event is a store is the allocation's store. -/
private theorem site_wr {d : Startup.D} {e : Event} {a : Acc} {bs : List Byte}
    (hE : Startup.Ev L g d e) (hx : Startup.exitOf d = none)
    (hk : e.kind = .wr a bs) : d.site = .allocSt := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hE <;> rw [hk] at h <;> cases h
  | elect j => obtain ⟨_, _, -, h⟩ := hE; rw [hk] at h; cases h
  | allocSt => rfl
  | ld => rcases hE with ⟨a, bs, h, -⟩ | ⟨f, h⟩ <;> rw [hk] at h <;> cases h
  | enter r => simp [Startup.exitOf] at hx
  | _ => (have h : e.kind = _ := hE); rw [hk] at h; cases h

/-- The steps into the store and the read-back: the allocation steps to lane 0's store or to
another lane's read-back, the store to the read-back. -/
private theorem succ_into {d0 d : Startup.D} {e : Event}
    (hs : Startup.succ L g d0 e = some (some d)) (hd : d.site = .allocSt ∨ d.site = .ld) :
    (d0.site = .alloc ∧ d.site = if PTX.laneOf L g = 0 then .allocSt else .ld) ∨
      (d0.site = .allocSt ∧ d.site = .ld) := by
  obtain ⟨site, x1, x2⟩ := d0
  cases site with
  | alloc =>
    refine .inl ⟨rfl, ?_⟩
    by_cases hl : PTX.laneOf L g = 0 <;>
      simp only [Startup.succ, hl, ↓reduceIte, Option.some.injEq] at hs <;> subst hs <;> simp [hl]
  | allocSt =>
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    exact .inr ⟨rfl, rfl⟩
  | sh j =>
    simp only [Startup.succ] at hs
    split at hs
    · unfold Startup.word32 at hs
      split at hs
      · fin_cases j
        · obtain rfl := Option.some.inj (Option.some.inj hs); rcases hd with hd | hd <;> cases hd
        · simp only [Option.some.injEq] at hs
          split_ifs at hs <;> subst hs <;> rcases hd with hd | hd <;> cases hd
      · cases hs
    · cases hs
  | elect j =>
    simp only [Startup.succ] at hs
    split at hs
    · fin_cases j
      · obtain rfl := Option.some.inj (Option.some.inj hs); rcases hd with hd | hd <;> cases hd
      · simp only [Option.some.injEq] at hs
        split_ifs at hs <;> subst hs <;> rcases hd with hd | hd <;> cases hd
    · cases hs
  | init n =>
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    simp only [Startup.initSucc] at hd
    rcases hd with hd | hd <;> split at hd <;> cases hd
  | ld =>
    simp only [Startup.succ] at hs
    split at hs
    · split at hs
      · unfold Startup.afterLd at hs
        split at hs
        · split_ifs at hs <;> obtain rfl := Option.some.inj (Option.some.inj hs) <;>
            rcases hd with hd | hd <;> cases hd
        · cases hs
      · cases hs
    · cases hs
  | bar =>
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    unfold Startup.enterOf at hd
    rcases hd with hd | hd <;> split_ifs at hd
  | trap => simp [Startup.succ] at hs
  | enter r => simp [Startup.succ] at hs
  | _ =>
    simp only [Startup.succ, Option.some.injEq] at hs
    subst hs
    rcases hd with hd | hd <;> cases hd

/-- A startup state whose event is a read is the read-back. -/
private theorem site_rd {d : Startup.D} {e : Event} {a : Acc} {bs : List (Option Byte)}
    (hE : Startup.Ev L g d e) (hx : Startup.exitOf d = none)
    (hk : e.kind = .rd a bs) : d.site = .ld := by
  obtain ⟨site, x1, x2⟩ := d
  cases site with
  | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hE <;> rw [hk] at h <;> cases h
  | elect j => obtain ⟨_, _, -, h⟩ := hE; rw [hk] at h; cases h
  | allocSt => obtain ⟨col, -, h⟩ := hE; rw [hk] at h; cases h
  | ld => rfl
  | enter r => simp [Startup.exitOf] at hx
  | _ => (have h : e.kind = _ := hE); rw [hk] at h; cases h

/-- The first startup state is no store and no read-back. -/
private theorem not_init {k : Nat} {d : Startup.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X g k = some (some (.inl d, n)))
    (hd : d.site = .allocSt ∨ d.site = .ld) : ∃ k0, k = k0 + 1 := by
  rcases k with _ | k0
  · rw [Frame.stateAt_zero, thread_init] at hσ
    cases hσ
    rcases hd with hd | hd <;> cases hd
  · exact ⟨k0, rfl⟩

variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **A startup store of the allocation word is lane 0's.** -/
theorem wr_lane {h i pc : Nat} {a : Acc} {bs : List Byte} (_hh : h < L.threads)
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hpc : StartupAt pc) : PTX.laneOf L h = 0 := by
  obtain ⟨d, n, hσ, hE, hx⟩ := ev_inl hp hX hFw he (fun f h => by cases h) hpc
  have hd := site_wr hE hx rfl
  rcases i with _ | i
  · rw [Frame.stateAt_zero, thread_init] at hσ
    cases hσ
    cases hd
  · have hlt : i < (X.tr h).length := by
      have : i + 1 < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
      omega
    obtain ⟨d0, n0, -, hs⟩ := pred_inl (List.getElem?_eq_getElem hlt) hσ
    rcases succ_into hs (.inl hd) with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hd] at h
    · by_contra hl
      simp only [hl, ↓reduceIte] at h
      cases h
    · cases h

/-- **A CTA's startup stores of the allocation word are one event**: lane 0 of warp 0 stores
once. -/
theorem wr_unique {h h' i i' pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte}
    (hh : h < L.threads) (hh' : h' < L.threads) (hc : h / L.block = h' / L.block)
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (he' : X.get (h', i') = some ⟨pc', .wr a' bs'⟩)
    (hpc : StartupAt pc) (hpc' : StartupAt pc') : h = h' ∧ i = i' := by
  have hw := ((startup_mem hp hX hFw he hpc).1 a bs rfl).1
  have hw' := ((startup_mem hp hX hFw he' hpc').1 a' bs' rfl).1
  have hl := wr_lane hp hX hFw hh he hpc
  have hl' := wr_lane hp hX hFw hh' he' hpc'
  have hhh : h = h' := by
    have hb := hp.block
    simp only [warpOf, tidOf_eq hp] at hw hw'
    simp only [PTX.laneOf, hb] at hl hl'
    rw [hb] at hc
    omega
  subst hhh
  refine ⟨rfl, ?_⟩
  obtain ⟨d, n, hσ, hE, hx⟩ := ev_inl hp hX hFw he (fun f h => by cases h) hpc
  obtain ⟨d', n', hσ', hE', hx'⟩ := ev_inl hp hX hFw he' (fun f h => by cases h) hpc'
  have hd := site_wr hE hx rfl
  have hd' := site_wr hE' hx' rfl
  have hm : ∀ {x : Startup.D}, x.site = .allocSt → Startup.measure x = 29 := by
    intro x hx; simp [Startup.measure, hx, Startup.Site.rank]
  have hlen := (List.getElem?_eq_some_iff.mp he).1
  have hlen' := (List.getElem?_eq_some_iff.mp he').1
  rcases Nat.lt_trichotomy i i' with hlt | heq | hlt
  · obtain ⟨d0, n0, hσ0, hle⟩ := chain hσ' hlen'.le hlt.le
    rw [hσ] at hσ0
    cases hσ0
    rw [hm hd, hm hd'] at hle
    omega
  · exact heq
  · obtain ⟨d0, n0, hσ0, hle⟩ := chain hσ hlen.le hlt.le
    rw [hσ'] at hσ0
    cases hσ0
    rw [hm hd, hm hd'] at hle
    omega

/-- **A read-back follows its thread's allocation request**: an earlier startup event of the
thread requests columns into the allocation word. -/
theorem rd_alloc {k : Nat} {a : Acc} {bs : List (Option Byte)} (_hg : g < L.threads)
    (he : X.get (g, k) = some ⟨92, .rd a bs⟩) : ∃ k' < k, ∃ pc grp n, StartupAt pc ∧
      X.get (g, k') = some ⟨pc, .tc (.resource grp (some (wsLoc L (g / L.block)
        Region.tmemWord.lo)) (.alloc n))⟩ := by
  obtain ⟨d, hT, hE, hx⟩ := startup_tmem hp hX hFw he (fun f h => by cases h) (by simp)
  have h1 : Tmem.Pair.tmemOps ((X.tr g).take k) = 1 := by
    obtain ⟨site, x1, x2⟩ := d
    cases site with
    | ld => exact hT.1
    | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hE <;> cases h
    | elect j => obtain ⟨_, _, -, h⟩ := hE; cases h
    | allocSt => obtain ⟨col, -, h⟩ := hE; cases h
    | enter r => simp [Startup.exitOf] at hx
    | _ => simp [Startup.Ev] at hE
  obtain ⟨x, hxm, hxop⟩ := List.countP_pos_iff.mp
    (show 0 < ((X.tr g).take k).countP Tmem.Pair.isTmemOp by
      unfold Tmem.Pair.tmemOps at h1; omega)
  obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxm
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  have hej : X.get (g, j) = some x := by
    have h := List.getElem?_eq_some_iff.mpr ⟨hj, hjx⟩
    rwa [List.getElem?_take_of_lt hjk] at h
  obtain ⟨d', n', hσ, -, -⟩ := ev_inl hp hX hFw he (fun f h => by cases h) (by simp)
  obtain ⟨d0, n0, hσ0, -⟩ := chain hσ (List.getElem?_eq_some_iff.mp he).1.le hjk.le
  obtain ⟨-, hxpc, hx0⟩ := startup_ev hp hX hej hσ0
  have hat : x.pc < 103 := by have := startup_pc_le hx0; omega
  obtain ⟨pcx, kx⟩ := x
  obtain ⟨c, rfl⟩ : ∃ c, kx = .tc c := by
    cases kx <;> simp [Tmem.Pair.isTmemOp] at hxop
    exact ⟨_, rfl⟩
  obtain ⟨grp, dst, act, rfl⟩ : ∃ grp dst act, c = .resource grp dst act := by
    cases c <;> simp [Tmem.Pair.isTmemOp] at hxop
    exact ⟨_, _, _, rfl⟩
  have hsh := startup_tmemShape hp hX hFw hej hat rfl
  have hle := countP_take_mono Tmem.Pair.isTmemOp (X.tr g) (Nat.succ_le_of_lt hjk)
  rw [List.take_add_one, show (X.tr g)[j]? = _ from hej, Option.toList_some,
    List.countP_append] at hle
  have h0 : Tmem.Pair.tmemOps ((X.tr g).take j) = 0 := by
    unfold Tmem.Pair.tmemOps at h1 ⊢
    simp [Tmem.Pair.isTmemOp] at hle
    omega
  rw [h0] at hsh
  obtain ⟨-, hc⟩ := startup_tc hp hX hFw hej hat rfl
  refine ⟨j, hjk, pcx, .one, 512, hat, ?_⟩
  rcases hc with hc | hc
  · rw [hej, hc]
  · cases hc
    cases hsh

/-- The state after a lane's allocation: lane 0's store, another lane's read-back. -/
private theorem after_alloc {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc} {f : Event}
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) (hpc : StartupAt pc)
    (hlen : (X.tr g).length = k + 1) (hn : Sched.NextEv L kernel Assumptions.all m X g f) :
    ∃ d : Startup.D, Startup.Ev L g d f ∧ f.pc = d.site.pc ∧
      d.site = if PTX.laneOf L g = 0 then .allocSt else .ld := by
  obtain ⟨d0, n0, hσ0, hE0, hx0⟩ := ev_inl hp hX hFw ha (fun f h => by cases h) hpc
  obtain ⟨Y, hY, hpre, hf⟩ := hn
  obtain ⟨site, x1, x2⟩ := d0
  obtain rfl : site = .alloc := by
    cases site with
    | alloc => rfl
    | sh j => fin_cases j <;> obtain ⟨r, ok, h⟩ := hE0 <;> cases h
    | elect j => obtain ⟨_, _, -, h⟩ := hE0; cases h
    | allocSt => obtain ⟨col, -, h⟩ := hE0; cases h
    | ld => rcases hE0 with ⟨a, bs, h, -⟩ | ⟨f, h⟩ <;> cases h
    | enter r => simp [Startup.exitOf] at hx0
    | _ => simp [Startup.Ev] at hE0
  let d1 : Startup.D := ⟨if PTX.laneOf L g = 0 then .allocSt else .ld, x1, x2⟩
  have hσ : Frame.stateAt (thread P L) Y g (X.tr g).length =
      some (some (.inl d1, Code.bump cls n0 ⟨pc, .tc (.resource grp dst (.alloc n))⟩)) := by
    have hc : Frame.stateAt (thread P L) Y g (X.tr g).length =
        Frame.stateAt (thread P L) X g (X.tr g).length :=
      Sched.stateAt_congr (by rw [hpre, List.take_length])
    rw [hc, hlen,
      Frame.stateAt_succ (C := thread P L) (show (X.tr g)[k]? = some _ from ha), hσ0]
    change (thread P L g).next (.inl ⟨.alloc, x1, x2⟩, n0)
      ⟨pc, .tc (.resource grp dst (.alloc n))⟩ = _
    rw [next_startup]
    have hs : Startup.succ L g ⟨.alloc, x1, x2⟩ ⟨pc, .tc (.resource grp dst (.alloc n))⟩ =
        some (some d1) := by
      simp only [Startup.succ, d1]
      split_ifs <;> rfl
    rw [hs]
    simp only [Option.map_some]
    rw [Code.enter_none (Code.gatedExit_none.mpr (by
      simp only [startupEnter, Startup.exitOf, d1]; split_ifs <;> rfl))]
  obtain ⟨hE, hfpc, -⟩ := startup_ev hp hY hf hσ
  exact ⟨d1, hE, hfpc, rfl⟩

/-- **After the allocation**, lane 0's next event is at the store's pc 91, every other lane's at
the read-back's pc 92, a read or the fault of the read-back. -/
theorem alloc_after {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc} {f : Event}
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) (hpc : StartupAt pc)
    (hlen : (X.tr g).length = k + 1) (hn : Sched.NextEv L kernel Assumptions.all m X g f) :
    f.pc = (if PTX.laneOf L g = 0 then 91 else 92) ∧
      (PTX.laneOf L g ≠ 0 → (∃ a bs, f.kind = .rd a bs) ∨ ∃ u, f.kind = .ub u) := by
  obtain ⟨d, hE, hfpc, hd⟩ := after_alloc hp hX hFw ha hpc hlen hn
  obtain ⟨site, x1, x2⟩ := d
  simp only at hd hfpc
  subst hd
  by_cases hl : PTX.laneOf L g = 0
  · simp only [hl, ↓reduceIte] at hfpc ⊢
    exact ⟨hfpc, fun h => (h rfl).elim⟩
  · simp only [hl, ↓reduceIte] at hE hfpc ⊢
    refine ⟨hfpc, fun _ => ?_⟩
    rcases hE with ⟨a, bs, h, -⟩ | ⟨u, h⟩
    · exact .inl ⟨a, bs, h⟩
    · exact .inr ⟨u, h⟩

/-- **Lane 0's next event after the allocation is the store of the word**: the allocated column
(below `2 ^ 16`) as four bytes, at pc 91. -/
theorem alloc_store {k pc n : Nat} {grp : CtaGroup} {dst : Option Loc} {f : Event}
    (ha : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) (hpc : StartupAt pc)
    (hlen : (X.tr g).length = k + 1) (hl : PTX.laneOf L g = 0)
    (hn : Sched.NextEv L kernel Assumptions.all m X g f) :
    ∃ col, col < 2 ^ 16 ∧
      f = ⟨91, .wr { loc := wsLoc L (g / L.block) Region.tmemWord.lo, size := 4 }
        (b32 col).toBytes⟩ := by
  obtain ⟨d, hE, hfpc, hd⟩ := after_alloc hp hX hFw ha hpc hlen hn
  obtain ⟨site, x1, x2⟩ := d
  simp only [hl, ↓reduceIte] at hd
  subst hd
  obtain ⟨col, hcol, hk⟩ := hE
  obtain ⟨fpc, fk⟩ := f
  simp only at hfpc hk
  subst hfpc hk
  exact ⟨col, hcol, rfl⟩

/-- **A startup store follows its thread's allocation**: the event before it is the request of
all 512 columns into the allocation word, at pc 91. -/
theorem wr_after_alloc {h i pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hpc : StartupAt pc) :
    ∃ i0, i = i0 + 1 ∧ X.get (h, i0) = some ⟨91, .tc (.resource .one
      (some (wsLoc L (h / L.block) Region.tmemWord.lo)) (.alloc 512))⟩ := by
  obtain ⟨d, n, hσ, hE, hx⟩ := ev_inl hp hX hFw he (fun f h => by cases h) hpc
  have hd := site_wr hE hx rfl
  obtain ⟨i0, rfl⟩ := not_init hσ (.inl hd)
  have hlt : i0 < (X.tr h).length := by
    have : i0 + 1 < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
    omega
  obtain ⟨e0, he0⟩ : ∃ e0, (X.tr h)[i0]? = some e0 := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨d0, n0, hσ0, hs⟩ := pred_inl he0 hσ
  obtain ⟨hE0, hpc0, -⟩ := startup_ev hp hX he0 hσ0
  rcases succ_into hs (.inl hd) with ⟨h0, -⟩ | ⟨-, h⟩
  · obtain ⟨site, x1, x2⟩ := d0
    simp only at h0
    subst h0
    have hk : e0.kind = _ := hE0
    obtain ⟨pc0, k0⟩ := e0
    simp only at hk hpc0
    subst hk hpc0
    exact ⟨i0, rfl, he0⟩
  · rw [hd] at h
    cases h

/-- **Lane 0's read-back follows its store**: an earlier event of the thread is the store of the
allocation word at pc 91. -/
theorem rd_after_wr {k : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨92, .rd a bs⟩) (hl : PTX.laneOf L g = 0) :
    ∃ i < k, ∃ c v, X.get (g, i) = some ⟨91, .wr c v⟩ := by
  obtain ⟨d, n, hσ, hE, hx⟩ := ev_inl hp hX hFw he (fun f h => by cases h) (by simp)
  have hd := site_rd hE hx rfl
  obtain ⟨k0, rfl⟩ := not_init hσ (.inr hd)
  have hlt : k0 < (X.tr g).length := by
    have : k0 + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    omega
  obtain ⟨e0, he0⟩ : ∃ e0, (X.tr g)[k0]? = some e0 := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨d0, n0, hσ0, hs⟩ := pred_inl he0 hσ
  obtain ⟨hE0, hpc0, -⟩ := startup_ev hp hX he0 hσ0
  rcases succ_into hs (.inr hd) with ⟨-, h⟩ | ⟨h0, -⟩
  · simp only [hl, ↓reduceIte, hd] at h
    cases h
  · obtain ⟨site, x1, x2⟩ := d0
    simp only at h0
    subst h0
    obtain ⟨col, -, hk⟩ := hE0
    obtain ⟨pc0, k0'⟩ := e0
    simp only at hk hpc0
    subst hk hpc0
    exact ⟨k0, by omega, _, _, he0⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
