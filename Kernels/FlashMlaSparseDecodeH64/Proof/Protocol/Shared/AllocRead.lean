-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.AllocRead
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Shared.Ordered
public import Lemmas.Tmem.Tmem1Protocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Async
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Region
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Alloc
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mem
import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem
import Lemmas.Flow.NthEv
import Lemmas.Tmem.AllocResultDependency
import Lemmas.Tmem.AllocWordOrder

@[expose] public section

/-! # The read-back of the allocation word reads `0`

`allocRead` (row `AllocRead`, from `Follow`): every launched lane's read at pc 92 reads the bytes
of `b32 0`. It sits below `Top/` so that `Top/Safe/NoUb.lean` imports it (the trap at pcs 93–95
is not reached, `Safe.noTrap`).

* A store of the CTA's word precedes the read at each of its bytes: lane 0's own store in program
  order (`rd_after_wr`), the leader's result store for another lane (`alloc_word_order` after the
  lane's request, `rd_alloc`). So the read reads no byte of the initial memory (`Hidden`).
* The byte's source is a startup store of the word (`word_intent`), whose bytes are the column of
  its allocation's record (Core's `ResultOk`, the allocation being the event before the store,
  `wr_after_alloc`), and that column is `0` (`Tmem.One.alloc_zero`: warp 0 makes every paired
  operation, `tmemOps_warp0`, and the record is the CTA's first, `first_recorded`). -/

/-! # The allocation word is ordered

The only accesses of a CTA's allocation word (`Region.tmemWord`) are the startup's
(`access_region`, `async_region`, `startup_mem`): the store of the allocated column at pc 91 and
the read-back at pc 92, both in warp 0. Given the startup's facts on the word
(`AllocWordRows`: a startup store is lane 0's and the CTA's only one, and a read-back follows its
thread's allocation request), every conflict is ordered (`tmemWord_ordered_of`):

* two stores are one (`wr_unique`);
* a store and a read of one thread are in program order (`same_thread`); a read of lane 0 is the
  storing thread's (`sameWarp_leader_eq`);
* the store and a read of another lane: Core's allocation-result order (`alloc_word_order`): the
  leader's result store, which is the CTA's store, precedes the read. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The startup's facts on the allocation word**: a startup store is lane 0's and the only one
of its CTA, and a read-back at pc 92 follows its thread's allocation request, a startup event
naming the word. -/
structure AllocWordRows (L : Launch) (X : Execution) : Prop where
  wr_lane : ∀ {h i pc : Nat} {a : Acc} {bs : List Byte}, h < L.threads →
    X.get (h, i) = some ⟨pc, .wr a bs⟩ → StartupAt pc → PTX.laneOf L h = 0
  wr_unique : ∀ {h h' i i' pc pc' : Nat} {a a' : Acc} {bs bs' : List Byte}, h < L.threads →
    h' < L.threads → h / L.block = h' / L.block → X.get (h, i) = some ⟨pc, .wr a bs⟩ →
    X.get (h', i') = some ⟨pc', .wr a' bs'⟩ → StartupAt pc → StartupAt pc' → h = h' ∧ i = i'
  rd_alloc : ∀ {g k : Nat} {a : Acc} {bs : List (Option Byte)}, g < L.threads →
    X.get (g, k) = some ⟨92, .rd a bs⟩ → ∃ k' < k, ∃ pc grp n, StartupAt pc ∧
      X.get (g, k') = some ⟨pc, .tc (.resource grp (some (wsLoc L (g / L.block)
        Region.tmemWord.lo)) (.alloc n))⟩

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **An access of the allocation word** is a startup store or a read-back at pc 92 of the
word, by a thread of the byte's CTA. -/
theorem word_intent {r} {c : Acc} {w : Bool} {l : Loc} {cta : Nat}
    (hi : X.Intent r c w) (hc : c.Covers l) (hl : MemRow.LocIn L cta .tmemWord l) :
    ∃ g k pc, r = .thread (g, k) ∧ g < L.threads ∧ l.cta = g / L.block ∧ StartupAt pc ∧
      ((w = true ∧ ∃ bs, X.get (g, k) = some ⟨pc, .wr c bs⟩) ∨
        (w = false ∧ pc = 92 ∧ ∃ bs, X.get (g, k) = some ⟨pc, .rd c bs⟩ ∧
          MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 c)) := by
  have hs : l.space = .shared := hl.1
  cases r with
  | async i p =>
    obtain ⟨g, k⟩ := i
    exfalso
    rcases async_region hp hX hFw hi hc hs with ⟨b, h⟩ | ⟨h, -⟩ | ⟨b, h, -⟩ <;>
      exact absurd (locIn_eq h hl).2 (by simp)
  | thread i =>
    obtain ⟨g, k⟩ := i
    obtain ⟨e, he, hr⟩ := access_region hp hX hFw hi hc hs
    have hg := Frame.lt_of_get hX he
    have hst : StartupAt e.pc ∧ l.cta = g / L.block := by
      rcases hr with ⟨h1, h⟩ | ⟨-, ((h | h | h) | h)⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, b, h | h⟩
      · exact ⟨h1, h.2.1⟩
      all_goals exact absurd (locIn_eq h hl).2 (by simp)
    obtain ⟨pc, kd⟩ := e
    refine ⟨g, k, pc, rfl, hg, hst.2, hst.1, ?_⟩
    obtain ⟨hwr, hrd, -, -⟩ := startup_mem hp hX hFw he hst.1
    rcases hi with ⟨bs, ⟨pc', h⟩, rfl⟩ | ⟨bs, ⟨pc', h⟩, rfl⟩ | ⟨o, n, pc', h⟩
    · rw [he] at h
      cases h
      obtain ⟨-, h92, hws⟩ := hrd c bs rfl
      exact .inr ⟨rfl, h92, bs, he, hws⟩
    · rw [he] at h
      cases h
      exact .inl ⟨rfl, bs, he⟩
    · rw [he] at h
      cases h
      exact absurd rfl (mem_use (mem_rows hp hX hFw) hg he)

/-- **The store precedes a read-back of the word** at its bytes, given the startup's facts. -/
theorem word_wr_rd (hA : AllocWordRows L X) {h g i j pc : Nat} {a c : Acc} {bs : List Byte}
    {bs' : List (Option Byte)} {l : Loc} (hh : h < L.threads) (hg : g < L.threads)
    (hcta : h / L.block = g / L.block) (hw : X.get (h, i) = some ⟨pc, .wr a bs⟩)
    (hpc : StartupAt pc) (hr : X.get (g, j) = some ⟨92, .rd c bs'⟩)
    (hws : MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 c) (ha : a.Covers l)
    (hc : c.Covers l) (hne : (h, i) ≠ (g, j)) :
    ByteCausality L X l (.thread (h, i)) (.thread (g, j)) ∨
      ByteCausality L X l (.thread (g, j)) (.thread (h, i)) := by
  have hw0 : warpOf L g = 0 := (startup_mem hp hX hFw hr (by simp)).2.1 c bs' rfl |>.1
  have hwh : warpOf L h = 0 :=
    ((startup_mem hp hX hFw hw hpc).1 a bs rfl).1
  have hsw : SameWarp L h g := by
    refine ⟨⟨hh, hg, hcta⟩, ?_⟩
    have hb := hp.block
    simp only [warpOf, tidOf_eq hp] at hw0 hwh
    rw [hb] at hcta ⊢
    omega
  by_cases hl0 : PTX.laneOf L g = 0
  · obtain rfl := Tmem.Pair.sameWarp_leader_eq hsw (hA.wr_lane hh hw hpc) hl0
    have hij : i ≠ j := fun h => hne (by rw [h])
    exact same_thread (.inr (.inl ⟨bs, ⟨pc, hw⟩, rfl⟩)) (.inl ⟨bs', ⟨92, hr⟩, rfl⟩) hij
      ⟨l, ha, hc⟩ l
  · obtain ⟨k', hk', pca, grp, n, hpca, hall⟩ := hA.rd_alloc hg hr
    obtain ⟨s, hss, hs0, ⟨bs0, hs⟩, hord⟩ :=
      alloc_word_order hX hall hk' (List.getElem?_eq_some_iff.mp hr).1 hl0
    obtain ⟨⟨hs1, -, hsc⟩, -⟩ := hss
    obtain ⟨rfl, rfl⟩ := hA.wr_unique hh hs1 (hcta.trans hsc.symm) hw hs hpc hpca
    refine .inl (.direct (hord hr hc ?_))
    obtain ⟨hl, hsz⟩ := hws
    obtain ⟨h1, h2, h3, h4⟩ := hc
    rw [hl] at h1 h2 h3 h4
    rw [hsz] at h4
    exact ⟨h1, h2, h3, h4⟩

/-- **The allocation word is ordered**, given the startup's facts on it. -/
theorem tmemWord_ordered_of (hA : AllocWordRows L X) : RegionOrdered L X .tmemWord := by
  intro e f a b l hcon ha hb ⟨cta, hl⟩ _
  obtain ⟨hne, we, wf, he, hf, hw, -⟩ := hcon
  obtain ⟨g, i, pc, rfl, hg, hgc, hpc, ⟨rfl, bs, hge⟩ | ⟨rfl, rfl, bs, hge, hgw⟩⟩ :=
    word_intent hp hX hFw he ha hl <;>
  obtain ⟨h, j, pc', rfl, hh, hhc, hpc', ⟨rfl, bs', hhe⟩ | ⟨rfl, rfl, bs', hhe, hhw⟩⟩ :=
    word_intent hp hX hFw hf hb hl
  · obtain ⟨rfl, rfl⟩ := hA.wr_unique hg hh (hgc.symm.trans hhc) hge hhe hpc hpc'
    exact (hne rfl).elim
  · exact word_wr_rd hp hX hFw hA hg hh (hgc.symm.trans hhc) hge hpc hhe hhw ha hb
      (fun h => hne (by rw [h]))
  · exact (word_wr_rd hp hX hFw hA hh hg (hhc.symm.trans hgc) hhe hpc' hge hgw hb ha
      (fun h => hne (by rw [h]))).symm
  · rcases hw with h | h <;> cases h

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof MbarRow Tmem.Pair

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Warp 0 of the rows is warp 0 of the CTA (`g % L.block / 32`). -/
theorem warp0_iff (hp : Pre P L m) {g : Nat} : MbarRow.warp L g = 0 ↔ g % L.block / 32 = 0 := by
  simp only [MbarRow.warp, tidOf_x_eq hp, hp.block]

/-- An operation bumps the thread's count of paired operations. -/
private theorem ops_succ {g x : Nat} {e : Event} (he : X.get (g, x) = some e)
    (hop : isTmemOp e = true) :
    tmemOps ((X.tr g).take (x + 1)) = tmemOps ((X.tr g).take x) + 1 := by
  unfold tmemOps
  rw [List.take_add_one, show (X.tr g)[x]? = some e from he, Option.toList_some,
    List.countP_append]
  simp [hop]

/-- Two operations of a thread with no operation before either are one. -/
private theorem first_op_eq {g x y : Nat} {ex ey : Event} (hx : X.get (g, x) = some ex)
    (hy : X.get (g, y) = some ey) (hex : isTmemOp ex = true) (hey : isTmemOp ey = true)
    (h0x : tmemOps ((X.tr g).take x) = 0) (h0y : tmemOps ((X.tr g).take y) = 0) : x = y := by
  rcases Nat.lt_trichotomy x y with h | h | h
  · have := Flow.countP_take_mono isTmemOp (X.tr g) (Nat.succ_le_of_lt h)
    unfold tmemOps at h0x h0y
    rw [show ((X.tr g).take (x + 1)).countP isTmemOp = _ from ops_succ hx hex] at this
    unfold tmemOps at this
    omega
  · exact h
  · have := Flow.countP_take_mono isTmemOp (X.tr g) (Nat.succ_le_of_lt h)
    unfold tmemOps at h0x h0y
    rw [show ((X.tr g).take (y + 1)).countP isTmemOp = _ from ops_succ hy hey] at this
    unfold tmemOps at this
    omega

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- **Warp 0 makes every paired Tensor Memory operation**, in group 1, its thread's `n`-th of
shape `n`. -/
theorem tmemOps_warp0 : Tmem.One.Tmem1Ops L X 0 := by
  have hR := tmem_rows hp hX hFw
  refine { warp_lt := by rw [hp.block]; decide, event := ?_ }
  intro g k pc grp dst act hg he
  obtain ⟨rfl, ⟨hS, hw, -⟩ | ⟨hA, -⟩⟩ := tmem_res hR hg he rfl
  · exact ⟨(warp0_iff hp).1 hw, rfl, startup_tmemShape hp hX hFw he hS rfl⟩
  · obtain ⟨hw, rfl, hc⟩ := wg0_deallocOps hp hX hFw he hA rfl
    refine ⟨(warp0_iff hp).1 hw, rfl, ?_⟩
    rw [hc]
    exact ⟨0, rfl⟩

/-- **The startup's facts on the allocation word** (`Startup/Export/Alloc.lean`). -/
theorem allocWordRows : AllocWordRows L X :=
  ⟨wr_lane hp hX hFw, wr_unique hp hX hFw, fun hg he => rd_alloc hp hX hFw hg he⟩

/-- **A startup store of the allocation word writes column `0`**: the column of its allocation's
record, the CTA's first allocation. -/
theorem wr_zero {h i pc : Nat} {a : Acc} {bs : List Byte} (hh : h < L.threads)
    (he : X.get (h, i) = some ⟨pc, .wr a bs⟩) (hpc : StartupAt pc) : bs = (b32 0).toBytes := by
  obtain ⟨i0, rfl, hal⟩ := wr_after_alloc hp hX hFw he hpc
  have hl0 := wr_lane hp hX hFw hh he hpc
  have hw0 := ((startup_mem hp hX hFw he hpc).1 a bs rfl).1
  have ht := tmemOps_warp0 hp hX hFw
  have hhc : h = h / L.block * L.block + 0 * 32 := by
    have hb := hp.block
    simp only [warpOf, tidOf_eq hp] at hw0
    simp only [PTX.laneOf, hb] at hl0
    rw [hb]
    omega
  have hlen : i0 + 1 < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
  have hsh := (ht.event hh hal).2.2
  have hz : tmemOps ((X.tr h).take i0) = 0 := by
    rcases hn : tmemOps ((X.tr h).take i0) with _ | _ | _ | n <;> rw [hn] at hsh <;>
      simp [TmemShape] at hsh ⊢
  have hone := ops_succ hal rfl
  rw [hz] at hone
  rw [hhc] at hlen hone hz hal
  obtain ⟨r, hr, hr0⟩ := Tmem.One.first_recorded hX ht hlen (by simp only [opsAt, hone]; omega)
  obtain ⟨hrc, hrw, -, hreq, hrget, -⟩ := Tmem.One.record_info hX ht hr
  have hidx : r.own.indices 0 = i0 := first_op_eq hrget hal rfl rfl hr0 hz
  rw [hidx, hal] at hrget
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hrget
  obtain ⟨-, -, -, hrq⟩ := hrget
  obtain ⟨base, hact⟩ : ∃ base, r.action = .alloc 512 base := by
    rcases hra : r.action with ⟨n, base⟩ | ⟨b, n⟩ | _ <;>
      rw [hra, ← hrq] at hreq <;> simp [Tmem.Action.request] at hreq
    exact ⟨base, by rw [hreq]⟩
  have hb0 := (Tmem.One.alloc_zero hX ht hr 512 base hact).2
  have hres := hX.tmemPairResult _ _ _ _ _ hal _ r base hr
    (by simp [WarpRequest.event, hrc, hrw, hidx]) hact pc a bs (by rw [← hhc]; exact he)
  rw [hres, hb0]
  rfl

/-- **Row `AllocRead`**: the read-back at pc 92 of every launched lane reads the bytes of
`b32 0`. -/
theorem allocRead : AllocRead P L X := by
  intro g k a bs hg he
  have hrd : X.MemReads (.thread (g, k)) a bs := Or.inl ⟨92, he⟩
  obtain ⟨-, -, hal, has⟩ := (startup_mem hp hX hFw he (by simp)).2.1 a bs rfl
  have hws : ∀ {l}, a.Covers l → (wsLoc L (g / L.block) Region.tmemWord.lo).InRange 4 l := by
    intro l hl
    obtain ⟨h1, h2, h3, h4⟩ := hl
    rw [hal] at h1 h2 h3 h4
    rw [has] at h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨s, c, v, pcs, hs, hcov, hcaus⟩ : ∃ (s : EvId) (c : Acc) (v : List Byte) (pcs : Nat),
      X.get s = some ⟨pcs, .wr c v⟩ ∧ (∀ l, a.Covers l → c.Covers l) ∧
      ∀ l, a.Covers l → ByteCausality L X l (.thread s) (.thread (g, k)) := by
    by_cases hl0 : PTX.laneOf L g = 0
    · obtain ⟨i, hik, c, v, hs⟩ := rd_after_wr hp hX hFw he hl0
      obtain ⟨-, -, hc, -⟩ := (startup_mem hp hX hFw hs (by simp)).1 c v rfl
      have hcov : ∀ l, a.Covers l → c.Covers l := fun l hl => by rw [hc]; exact hws hl
      refine ⟨(g, i), c, v, 91, hs, hcov, fun l hl => ?_⟩
      exact .direct (.of_base L (.single (.inl (po_of_overlap (Or.inr (Or.inl ⟨v, ⟨91, hs⟩, rfl⟩))
        (Or.inl ⟨bs, ⟨92, he⟩, rfl⟩) rfl hik ⟨l, hcov l hl, hl⟩))))
    · obtain ⟨k', hk', pca, grp, n, -, hall⟩ := rd_alloc hp hX hFw hg he
      obtain ⟨s, -, -, ⟨bs0, hs⟩, hord⟩ :=
        alloc_word_order hX hall hk' (List.getElem?_eq_some_iff.mp he).1 hl0
      exact ⟨s, _, bs0, pca, hs, fun l hl => hws hl, fun l hl => .direct (hord he hl (hws hl))⟩
  have hlen : bs.length = a.size := (hX.rf _ a bs hrd).1
  have h4 : (b32 0).toBytes.length = 4 := rfl
  apply List.ext_getElem?
  intro j
  by_cases hj : j < a.size
  swap
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by rw [List.length_map]; omega)]
  have hrf := (hX.rf _ a bs hrd).2 j hj
  have hH := hX.hidden _ a bs j (.thread s) c v hrd hj (Or.inl ⟨pcs, hs⟩)
    (hcov _ (Acc.covers_at hj)) (hcaus _ (Acc.covers_at hj))
  rcases hsrc : X.rf (.thread (g, k)) j with _ | src
  · rw [hsrc] at hH
    exact hH.elim
  rw [hsrc] at hrf
  obtain ⟨a', bs', hmw, hcv, hval⟩ := hrf
  have hin := hws (Acc.covers_at hj)
  have hlocin : MemRow.LocIn L (g / L.block) .tmemWord (a.loc.at j) := by
    obtain ⟨h1, h2, h3, h4⟩ := hin
    refine ⟨h1, h2, ?_, ?_⟩ <;> simp only [wsLoc, Region.lo, Region.size] at h3 h4 ⊢ <;> omega
  obtain ⟨h', i', pc', rfl, hh', -, hpc', hcase⟩ := word_intent hp hX hFw hmw.intent hcv hlocin
  rcases hcase with ⟨-, bs'', hget⟩ | ⟨h, -⟩
  swap
  · cases h
  obtain rfl : bs' = bs'' := by
    rcases hmw with ⟨pc0, h0⟩ | ⟨old, pc0, h0⟩ <;> rw [hget] at h0 <;> cases h0
    rfl
  obtain ⟨-, -, rfl, -⟩ := (startup_mem hp hX hFw hget hpc').1 a' bs' rfl
  rw [wr_zero hp hX hFw hh' hget hpc'] at hval
  rw [hval, List.getElem?_map, List.getElem?_eq_getElem (by rw [h4]; omega)]
  obtain ⟨-, -, h3, -⟩ := hin
  simp only [wbyte, Loc.at, hal, wsLoc, Option.map_some] at h3 ⊢
  rw [show L.sharedBase + Region.tmemWord.lo + j - (L.sharedBase + Region.tmemWord.lo) = j by omega,
    List.getElem?_eq_getElem]

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
