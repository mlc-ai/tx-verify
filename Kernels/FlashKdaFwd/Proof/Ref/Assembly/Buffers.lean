-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.BuffersCompute

@[expose] public section

/-!
# The buffer region and the stores, for every consistent execution

Three contracts of the protocol layer, proved for every consistent execution of the FlashKDA
forward kernel from the exports of the seven phases of the reference layer:

    theorem unionFacts (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) :
        UnionFacts L X (ctaTiles P) (owners P L)
    theorem storeCover (hpre) (hX) : StoreCover L X (owners P L)
    theorem storesIssued (hpre) (hX) : StoresIssued P L X

* `Protocol.UnionFacts` (`Proof/Protocol/UnionClass.lean`): every access of the buffer region
  (offsets 32768 to 98304 of a block's shared-memory window: the FP32 state buffer, whose bytes
  are also the input and output buffers of the tile loop) has its class;
* `Protocol.StoreCover` (`StoreCover.lean`): the bytes a tensor store reads have been written;
* `Protocol.StoresIssued` (`ResultGlue.lean`): what the events that write global memory are,
  and that the store leader has issued them all when it exits.

`owners P L` (`BuffersLib.lean`) are the owner functions: which load or which compute thread
writes a byte. The words used below (block, compute thread, store leader, followed state,
ledger, mbarrier, poll) are defined in the header of `BuffersLib.lean`.

## Method

Each field is about an event of one thread. `event_stage` (`Tracked.lean`) gives the followed
state before the event and the phase it is in (`Stage`: startup, Conversion, CarryLoad, one of
the three tile loops Compute / Producer / Store by the thread's role, epilogue), with the
phase's invariant and the history of the earlier phases. In each of the seven cases either the
phase's export for the field applies, or the phase fires no event of that kind (`kind_*`), or
the number of `bar.sync 0` before the event rules the phase out (`bars_*`). The proofs of the
single fields are in the namespace `Buffers`, one theorem per field, with the field's name.

* `UnionFacts.thread`: the Conversion and the CarryLoad phase (class `early`:
  `Conversion.union_early`, `CarryLoad.union_thread_carry`), the Compute phase (`input`,
  `output`: `ComputeOwes.thread`), the Store phase (`leader`: `Store.thread_store`), the
  epilogue (`final`: `Epilogue.wr_final`);
* `UnionFacts.load`: the startup (`init`: `Startup.union_load_startup`) and the Producer phase
  (`tile`: `Producer.unionLoad_producer`);
* `UnionFacts.store`, `StoreCover.store_in`: the Store phase (`tile`: `Store.store_store`) and
  the epilogue (`final`: `Epilogue.ts_final`);
* `UnionFacts.bar_fence`: the entry of a tile loop (the sixth `bar.sync 0`: the exit condition
  of the CarryLoad phase has the fence) and the epilogue (the eighth: `Epilogue.bar_fence`);
* `UnionFacts.store_bar_wait`: `Store.store_wait_after`, `Epilogue.store_bar_wait`;
* `UnionFacts.polled`: the exit ledger of the Compute phase, kept by `Epilogue.polls_in`;
* `StoreCover.out_cover`, `matrix_len`: the Compute phase (`ComputeOwes`);
* `StoreCover.final_cover`: `Epilogue.final_cover_bar`;
* `StoreCover.out_lt`, `final_lt`: `outOwner_lt`, `Epilogue.finalOwner_lt`;
* `StoresIssued.tile`, `elem`, `outIssued`: `Store.tile_store`, `elem_store`,
  `outIssued_store`;
* `StoresIssued.final`, `stateIssued`: `Epilogue.ts_state`, `state_issued`;
* `StoresIssued.finalAsync`: the frames of the write events of the phases.

Two facts are used across fields. An event with seven or more `bar.sync 0` before it is an
event of the epilogue, whatever its kind (`epi_of_bars`: through the thread's seventh
`bar.sync 0`, so the event itself may be undefined behaviour). A tensor store is issued in the
Store phase or in the epilogue (`store_cases`), a write event that covers a global byte in the
Store phase (`wr_global`), an exit in the epilogue (`exit_epilogue`). That a store of a tile
writes no byte of the final state and a store of the final state no byte of the output is the
precondition's "the two arrays are apart" (`out_ne_state`).

## Hypotheses

None beyond the precondition and consistency. The share of the Compute phase
(`Buffers.ComputeOwes P L X`: the classes `input` and `output`, the coverage of the output
buffer at the arrival, the length and the frame of a row write) is a hypothesis `hO` of the
theorems of the single fields and is proved in `BuffersCompute.lean` (`Buffers.computeOwes`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (Owners Bar bar0Before bar0Pcs InUnion InInput InOutput
  InShared ThreadClass LoadClass StoreClass UnionFacts StoreCover StoresIssued storeLeader
  computeThread ctaTiles uses blockOf stageOf outByte outOff stmatrixPcs)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Buffers

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### `UnionFacts` -/

/-- **`UnionFacts.thread`**: a thread access of a byte of the buffer region is of the thread's
own block, follows the thread's successful poll of the state mbarrier, and has one of the five
classes: `early` in the Conversion and the CarryLoad phase, `input` or `output` in the Compute
phase (its share `hO`), `leader` in the Store phase, `final` in the epilogue. The startup
phase only reads global memory and the Producer phase has no memory access. -/
theorem thread (hO : ComputeOwes P L X) {g i c : Nat} {a : Acc} {w : Bool} {l : Loc}
    (hacc : X.Access (g, i) a w) (hcov : a.Covers l) (hin : InUnion L c l) :
    g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take i) ∧
      ThreadClass L X (owners P L) c g i w l := by
  obtain ⟨e, he, hk⟩ := access_event hacc
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by
    rcases hk with ⟨bs, h'⟩ | ⟨bs, h', -⟩ | ⟨o, n, h'⟩ <;> rw [h'] at h <;> cases h)
  cases hst with
  | startup hI =>
    exfalso
    have hkd := kind_startup hpre hX hg he hσ hI
    rcases hk with ⟨bs, h⟩ | ⟨bs, h, -⟩ | ⟨o, n, h⟩
    · obtain ⟨pc, kd⟩ := e
      dsimp only at h
      subst h
      rcases Startup.read_startup hpre hX hg he hσ with ⟨j, -, rfl, -⟩ | hleft
      · have h1 : l.space = .global := hcov.1
        rw [hin.1] at h1
        cases h1
      · exact hI.inv.not_left hleft
    · rw [h] at hkd
      exact Bool.false_ne_true hkd
    · rw [h] at hkd
      exact Bool.false_ne_true hkd
  | conversion past hj hI =>
    exact Conversion.union_early hpre hX hg past.state past.conversion_in hj hσ hI hacc hcov hin
  | carryLoad past hj hI =>
    obtain ⟨j0, hen⟩ := entered_carry past
    exact CarryLoad.union_thread_carry hpre hX hg hen hσ hI hacc hcov hin
  | compute hr past hj hin' hI =>
    obtain ⟨rfl, hc⟩ := hO.thread (owners P L) rfl hg past.state hin' hσ hI hacc hcov hin
    exact ⟨rfl, polled_of_left hpre hX hg (left_carry past hj), hc⟩
  | producer hr past hj hen hI =>
    have hkd := kind_producer hpre hX hg he hσ hr hI
    rcases hk with ⟨bs, h⟩ | ⟨bs, h, -⟩ | ⟨o, n, h⟩ <;> rw [h] at hkd <;>
      exact (Bool.false_ne_true hkd).elim
  | store hr past hj hin' hI hW =>
    exact Store.thread_store hpre hX hg hacc hcov hin hσ (hI hub)
  | epilogue past hj hW hI =>
    have hkd := kind_epilogue hpre hX hg he past hj
    rcases hk with ⟨bs, h⟩ | ⟨bs, h, rfl⟩ | ⟨o, n, h⟩
    · rw [h] at hkd
      exact (Bool.false_ne_true hkd).elim
    · obtain ⟨pc, kd⟩ := e
      dsimp only at h
      subst h
      obtain ⟨ht, hb7, hu, hown⟩ :=
        Epilogue.wr_final hpre hX hg (entered_epilogue past) hj he hcov
      obtain rfl : g / L.block = c := hu.2.1.symm.trans hin.2.1
      exact ⟨rfl, polled_of_left hpre hX hg (left_tile past hj),
        .final ⟨g % L.block, ht⟩ (Protocol.thr_eq hpre.block g).symm rfl hb7 hown⟩
    · rw [h] at hkd
      exact (Bool.false_ne_true hkd).elim

/-- **`UnionFacts.load`**: a tensor load that writes a byte of the buffer region is a load of
the initial state (the startup phase: class `init`) or a load of a tile (the Producer phase:
class `tile`). No other phase issues a tensor load. -/
theorem load {g i pc al x y z c : Nat} {sp : TensorCopy.Spec} {l : Loc}
    (he : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hw : TensorCopy.writeLoc sp x y z = some l) (hin : InUnion L c l) :
    LoadClass L X (owners P L) c g i sp l := by
  have hg := Frame.lt_of_get hX he
  have hlt : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI =>
    rcases Startup.union_load_startup hpre hX hg (O := owners P L) rfl he hw hin hσ with h | h
    · exact h
    · exact absurd h hI.inv.not_left
  | conversion past hj hI => exact (Bool.false_ne_true (kind_conversion hpre hX hg he hσ hI)).elim
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin' hI => exact (Bool.false_ne_true (kind_compute hpre hX he hσ hI)).elim
  | producer hr past hj hen hI =>
    rcases Producer.unionLoad_producer hpre hX hg hr hen hj (O := owners P L)
      (owners_piece P L) he hσ hw hin with h | h
    · exact h
    · exact absurd h (producer_not_left hpre hX hg hr hlt.le hσ hI)
  | store hr past hj hin' hI hW =>
    exact (Bool.false_ne_true (kind_store hpre hX hg he hσ (hI hub))).elim
  | epilogue past hj hW hI =>
    exact (Bool.false_ne_true (kind_epilogue hpre hX hg he past hj)).elim

/-- A tensor store is issued by a thread in the Store phase or in the epilogue: the two cases
of every statement about a tensor store. -/
theorem store_cases {g i pc al : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩) :
    (∃ s j0 s0, At (code L) X g i s ∧ CarryLoadDone P L X g j0 s0 ∧ j0 ≤ i ∧
      Store.In P X g j0 s0 ∧ Store.Inv P X g i s) ∨
    ∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 ≤ i := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI => exact (Bool.false_ne_true (kind_startup hpre hX hg he hσ hI)).elim
  | conversion past hj hI => exact (Bool.false_ne_true (kind_conversion hpre hX hg he hσ hI)).elim
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin' hI => exact (Bool.false_ne_true (kind_compute hpre hX he hσ hI)).elim
  | producer hr past hj hen hI =>
    exact (Bool.false_ne_true (kind_producer hpre hX hg he hσ hr hI)).elim
  | store hr past hj hin' hI hW => exact .inl ⟨s, _, _, hσ, past, hj, hin', hI hub⟩
  | epilogue past hj hW hI => exact .inr ⟨_, _, past, hj⟩

/-- **`UnionFacts.store`**: a tensor store that reads a byte of the buffer region is the store
leader's, after its poll of the state mbarrier: a store of a full tile (the Store phase: class
`tile`) or of the final state (the epilogue: class `final`). -/
theorem store {g i pc al x y z c : Nat} {sp : TensorStore.Spec} {l : Loc}
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hr : TensorStore.readLoc sp x y z = some l) (hin : InUnion L c l) :
    g = storeLeader L c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take i) ∧
      StoreClass L X c g i l := by
  have hg := Frame.lt_of_get hX he
  rcases store_cases hpre hX he with ⟨s, j0, s0, hσ, past, hj, hin', hI⟩ | ⟨j0, s0, past, hj⟩
  · obtain ⟨hu, h1, h2, h3⟩ := Store.store_store hpre hX hg he hr hσ hI
    obtain rfl : c = g / L.block := hin.2.1.symm.trans hu.2.1
    exact ⟨h1, h2, h3⟩
  · obtain ⟨h1, h8, hu⟩ := Epilogue.ts_final hpre hX hg (entered_epilogue past) hj he hr
    obtain rfl : c = g / L.block := hin.2.1.symm.trans hu.2.1
    exact ⟨h1, polled_of_left hpre hX hg (left_tile past hj), .final h8⟩

/-- **`UnionFacts.bar_fence`**: the sixth and the eighth `bar.sync 0` of a thread directly
follow a proxy fence. The sixth is the entry of the thread's tile loop, after the fence of
instruction 1401 that ends the CarryLoad phase; the eighth is the epilogue's, after the fence
of instruction 3774. -/
theorem bar_fence {g k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hb : bar0Before X (g, k) = 5 ∨ bar0Before X (g, k) = 7) :
    0 < k ∧ ∃ pcf, X.get (g, k - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have hg := Frame.lt_of_get hX he
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI =>
    have := bars_startup hI
    omega
  | conversion past hj hI =>
    have := bars_conversion hI
    omega
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin hI =>
    exact entry_bar_fence hpre hX past hj hlt.le (bars_compute hI) hb
  | producer hr past hj hen hI =>
    exact entry_bar_fence hpre hX past hj hlt.le (bars_producer hI) hb
  | store hr past hj hin hI hW =>
    exact entry_bar_fence hpre hX past hj hlt.le (bars_store (hI hub)) hb
  | epilogue past hj hW hI =>
    rcases hb with hb | hb
    · have := (Epilogue.bar_in hpre hX hg (entered_epilogue past) hj he).2.2.2.2.1
      omega
    · exact Epilogue.bar_fence hpre hX hg (entered_epilogue past) hj he hb

/-- **`UnionFacts.store_bar_wait`**: between a tensor store of a thread and a later
`bar.sync 0` of the thread, the thread executes a `.read` bulk-group wait that covers the store:
the wait of the store's tile (instruction 3093) for a store of the Store phase, the wait of
instruction 3833 for a store of the epilogue. (Stated for any thread; only the store leader
issues tensor stores.) -/
theorem store_bar_wait {g k e pc addr pce : Nat} {cnt : Option Nat} {mode : BarMode}
    {sp : TensorStore.Spec} (hk : X.get (g, k) = some ⟨pc, .tensorStore addr sp⟩) (hke : k < e)
    (he : X.get (g, e) = some ⟨pce, .bar 0 cnt mode⟩) :
    ∃ w, k < w ∧ w < e ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  have hg := Frame.lt_of_get hX he
  rcases store_cases hpre hX hk with ⟨s, j0, s0, hσ, past, hj, hin', hI⟩ | ⟨j0, s0, past, hj⟩
  · obtain ⟨se, hσe, -, -⟩ := event_stage (P := P) hpre hX he (fun f h => by cases h)
    exact Store.store_wait_after hpre hX hg ⟨s0, past.state, hin'⟩ hj hk hσ hI hke he hσe
      (.inl ⟨_, _, _, rfl⟩)
  · exact Epilogue.store_bar_wait hpre hX hg (entered_epilogue past) hj hk hke he

/-- **`UnionFacts.polled`**: after the tile loop (seven `bar.sync 0`) a compute thread has
polled `loadFull s` successfully once for each use of stage `s`: the exit ledger of the Compute
phase, unchanged in the epilogue. -/
theorem polled {c e : Nat} {ev : Event} (s : Fin 3) (a : Fin 128)
    (he : X.get (computeThread L c a, e) = some ev)
    (hb : 7 ≤ bar0Before X (computeThread L c a, e)) :
    uses 3 (ctaTiles P c) s ≤
      okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c a)).take e) := by
  obtain ⟨hdiv, -, htid⟩ := computeThread_role hpre c a
  generalize computeThread L c a = g at he hb hdiv htid ⊢
  subst hdiv
  have hg := Frame.lt_of_get hX he
  have hlt : e < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have ht : tid g < 128 := by
    have := a.isLt
    omega
  obtain ⟨j0, s0, past, hj⟩ := epi_of_bars hpre hX he hb
  rw [Epilogue.polls_in hpre hX hg (entered_epilogue past) hj.le hlt]
  obtain ⟨j1, s1, -, -, hrole⟩ := past.entry
  rcases hrole with ⟨-, -, hout, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩
  · obtain ⟨-, hl, -⟩ := hout
    have hT : ctaTiles P (g / L.block) = Compute.tilesOf P g := by
      rw [hpre.block]
      rfl
    rw [hT]
    fin_cases s
    · exact (congrArg Compute.Led.pf0 hl).ge
    · exact (congrArg Compute.Led.pf1 hl).ge
    · exact (congrArg Compute.Led.pf2 hl).ge
  · exact absurd hw (not_warp45 ht).1
  · exact absurd hw (not_warp45 ht).2

/-! ### `StoreCover` -/

/-- **`StoreCover.store_in`**: every byte a tensor store reads lies in the buffer region of
the issuer's block. -/
theorem store_in {g i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc}
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hr : TensorStore.readLoc sp x y z = some l) : InUnion L (g / L.block) l := by
  have hg := Frame.lt_of_get hX he
  rcases store_cases hpre hX he with ⟨s, j0, s0, hσ, past, hj, hin', hI⟩ | ⟨j0, s0, past, hj⟩
  · exact (Store.store_store hpre hX hg he hr hσ hI).1
  · exact (Epilogue.ts_final hpre hX hg (entered_epilogue past) hj he hr).2.2

/-- **`StoreCover.out_cover`**: at its arrival on `storeFull o` a compute thread has written,
since its previous arrival on that mbarrier, every byte of output buffer `o` that it owns
(the share `hO` of the Compute phase; no other phase has such an arrival of a compute
thread). -/
theorem out_cover (hO : ComputeOwes P L X) {c e pce tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (a : Fin 128) (o : Fin 2) {l : Loc}
    (he : X.get (computeThread L c a, e) =
      some ⟨pce, .arrive ((Bar.storeFull o).loc L c) tx cnt rel sc⟩)
    (hl : InOutput L c o.val l) (hown : (owners P L).out l = a.val) :
    ∃ i pcw aw bs, i < e ∧ X.get (computeThread L c a, i) = some ⟨pcw, .wr aw bs⟩ ∧
      aw.Covers l ∧
      arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c a)).take i) =
        arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c a)).take e) := by
  obtain ⟨hdiv, hmod, htid⟩ := computeThread_role hpre c a
  generalize computeThread L c a = g at he hdiv hmod htid ⊢
  subst hdiv
  have hg := Frame.lt_of_get hX he
  have ht : tid g < 128 := by
    have := a.isLt
    omega
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI =>
    rcases Startup.arrive_startup hpre hX hg he hσ with ⟨-, -, -, -, -, -, h128, -⟩ | hleft
    · omega
    · exact absurd hleft hI.inv.not_left
  | conversion past hj hI => exact (Bool.false_ne_true (kind_conversion hpre hX hg he hσ hI)).elim
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin' hI =>
    exact hO.out_cover o hg past.state hin' hσ hI he hl (hown.trans hmod.symm)
  | producer hr past hj hen hI => exact absurd hr (not_warp45 ht).1
  | store hr past hj hin' hI hW => exact absurd hr (not_warp45 ht).2
  | epilogue past hj hW hI =>
    exact (Bool.false_ne_true (kind_epilogue hpre hX hg he past hj)).elim

/-- **`StoreCover.final_cover`**: at its eighth `bar.sync 0` a compute thread has written,
after its seventh, every byte of the buffer region that it owns in the final state (the 128
stores of the epilogue). -/
theorem final_cover {c e pce : Nat} {cnt : Option Nat} {mode : BarMode} (a : Fin 128) {l : Loc}
    (he : X.get (computeThread L c a, e) = some ⟨pce, .bar 0 cnt mode⟩)
    (hb : bar0Before X (computeThread L c a, e) = 7) (hl : InUnion L c l)
    (hown : (owners P L).final l = a.val) :
    ∃ i pcw aw bs, i < e ∧ X.get (computeThread L c a, i) = some ⟨pcw, .wr aw bs⟩ ∧
      aw.Covers l ∧ bar0Before X (computeThread L c a, i) = 7 := by
  obtain ⟨hdiv, hmod, -⟩ := computeThread_role hpre c a
  generalize computeThread L c a = g at he hb hdiv hmod ⊢
  subst hdiv
  have hg := Frame.lt_of_get hX he
  obtain ⟨j0, s0, past, hj⟩ := epi_of_bars hpre hX he hb.ge
  exact Epilogue.final_cover_bar hpre hX hg (entered_epilogue past) hj.le he hb
    (by have := a.isLt; omega) hl (hown.trans hmod.symm)

/-- **`StoreCover.matrix_len`**: the write event of an `stmatrix` lane carries as many bytes as
its footprint (the share `hO` of the Compute phase: the 18 `stmatrix` instructions are of the
tile loop of the compute threads, and no state of another phase is at one of them). -/
theorem matrix_len (hO : ComputeOwes P L X) {g i pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) (hpc : pc ∈ stmatrixPcs) : bs.length = a.size := by
  have hg := Frame.lt_of_get hX he
  have hrange : 2503 ≤ pc ∧ pc ≤ 2910 := by
    simp only [stmatrixPcs, List.mem_cons, List.mem_nil_iff, or_false] at hpc
    omega
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  have hpcs : pc = s.site.pc := Frame.event_pc (sounds hpre) hX he hσ
  cases hst with
  | startup hI =>
    have := pc_startup hI.inv
    omega
  | conversion past hj hI =>
    have := pc_conversion hI
    omega
  | carryLoad past hj hI =>
    have := pc_carryLoad hI
    omega
  | compute hr past hj hin' hI => exact hO.matrix_len hg past.state hin' hσ hI he
  | producer hr past hj hen hI =>
    have := pc_producer hI
    omega
  | store hr past hj hin' hI hW =>
    have := pc_store_inv (hI hub)
    omega
  | epilogue past hj hW hI =>
    have := pc_epilogue hW
    omega

/-! ### `StoresIssued` -/

/-- **A write event of a thread that covers a byte of global memory** is fired at a state of
the Store phase: the writes of the other phases are in shared memory. -/
theorem wr_global (hO : ComputeOwes P L X) {g i pc : Nat} {a : Acc} {bs : List Byte} {l : Loc}
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) (hcov : a.Covers l) (hgl : l.space = .global) :
    ∃ s, At (code L) X g i s ∧ Store.Inv P X g i s := by
  have hg := Frame.lt_of_get hX he
  have hsh : a.loc.space ≠ .shared := fun h => by
    have h1 : l.space = .shared := hcov.1.trans h
    rw [hgl] at h1
    cases h1
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI => exact (Bool.false_ne_true (kind_startup hpre hX hg he hσ hI)).elim
  | conversion past hj hI =>
    exfalso
    rcases (Conversion.access_conversion hpre hX hg hσ hI (a := a) (w := true)
      (.inr (.inl ⟨bs, ⟨pc, he⟩, rfl⟩))).2 with ⟨hw, -⟩ | ⟨-, el, -, -, rfl⟩
    · cases hw
    · exact hsh rfl
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin' hI => exact absurd (hO.wr_shared hg hσ hI he) hsh
  | producer hr past hj hen hI =>
    exact (Bool.false_ne_true (kind_producer hpre hX hg he hσ hr hI)).elim
  | store hr past hj hin' hI hW => exact ⟨s, hσ, hI hub⟩
  | epilogue past hj hW hI =>
    exact absurd (Epilogue.wr_frame hpre hX hg (entered_epilogue past) hj he).1 hsh

/-- **`StoresIssued.tile`**: a tensor store whose slot writes a byte of the output of a token
is a store of a full tile by the store leader of the token's block, in the Store phase (a
store of the epilogue writes a byte of the final state, and the two arrays are apart). -/
theorem tile {g i pc al x y z s h t k : Nat} {sp : TensorStore.Spec} {v : Fin 128}
    (hs : s < P.sequences) (hh : h < P.heads) (ht : t < P.length s) (hk : k < 2)
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hw : TensorStore.writeLoc sp x y z = some ((P.outLoc s h t v).at k)) :
    g = storeLeader L (blockOf P s h) ∧ bar0Before X (g, i) = 6 ∧
      okPolls ((Bar.storeFull (stageOf (t / 16))).loc L (blockOf P s h)) ((X.tr g).take i) =
        t / 16 / 2 + 1 ∧
      TensorStore.readLoc sp x y z =
        some (outByte L (blockOf P s h) (stageOf (t / 16)).val (outOff (t % 16) v k)) := by
  have hg := Frame.lt_of_get hX he
  rcases store_cases hpre hX he with ⟨d, j0, s0, hσ, past, hj, hin', hI⟩ | ⟨j0, s0, past, hj⟩
  · exact Store.tile_store hpre hX hg hs hh ht hk he hw hσ hI
  · exact (out_ne_state hpre ⟨s, hs, h, hh, t, ht, v, k, hk, rfl⟩
      (Epilogue.ts_writes_state hpre hX hg (entered_epilogue past) hj he hw)).elim

/-- **`StoresIssued.elem`**: a write event of a thread that covers a byte of the output of a
token is an event of the store leader of the token's block (a global store of the partial last
tile). -/
theorem elem (hO : ComputeOwes P L X) {g i pc s h t k : Nat} {a : Acc} {bs : List Byte}
    {v : Fin 128} (hs : s < P.sequences) (hh : h < P.heads) (ht : t < P.length s) (hk : k < 2)
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) (hcov : a.Covers ((P.outLoc s h t v).at k)) :
    g = storeLeader L (blockOf P s h) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ, hI⟩ := wr_global hpre hX hO he hcov rfl
  exact Store.elem_store hpre hX hg hs hh ht hk he hcov hσ hI

/-- **`StoresIssued.final`**: a tensor store whose slot writes a byte of the final state is a
store of the epilogue by the store leader of the byte's block, with eight `bar.sync 0` before
it (a store of the Store phase writes a byte of the output). -/
theorem final {g i pc al x y z s h b : Nat} {sp : TensorStore.Spec} {v k : Fin 128}
    (hs : s < P.sequences) (hh : h < P.heads) (hb : b < 4)
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hw : TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b)) :
    g = storeLeader L (blockOf P s h) ∧ bar0Before X (g, i) = 8 := by
  have hg := Frame.lt_of_get hX he
  rcases store_cases hpre hX he with ⟨d, j0, s0, hσ, past, hj, hin', hI⟩ | ⟨j0, s0, past, hj⟩
  · exfalso
    obtain ⟨pos, hr, hl, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
    obtain ⟨tt, j, rfl, -, rfl⟩ := Store.ev_ts_inv hev
    have hfull : 16 * tt + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
    obtain ⟨hx, hy, hz⟩ := Store.tileSpec_lt (.inl hw)
    rw [(Store.tileSpec_slot hpre hg j.isLt hfull hx hy hz).1] at hw
    exact out_ne_state hpre
      ⟨_, seqOf_lt hpre g, _, headOf_lt hpre hg, 16 * tt + y, by omega, _, z, hz,
        (Option.some.inj hw).symm⟩
      ⟨s, hs, h, hh, v, k, b, hb, rfl⟩
  · obtain ⟨h1, h8, -⟩ := Epilogue.ts_state hpre hX hg (entered_epilogue past) hj hh hb he hw
    exact ⟨h1, h8⟩

/-- **`StoresIssued.finalAsync`**: no write event of a thread covers a byte of the final
state: the only writes of global memory are the global stores of the Store phase, which write
bytes of the output. -/
theorem finalAsync (hO : ComputeOwes P L X) {g i pc s h b : Nat} {a : Acc} {bs : List Byte}
    {v k : Fin 128} (hs : s < P.sequences) (hh : h < P.heads) (hb : b < 4)
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) : ¬ a.Covers ((P.stateLoc s h v k).at b) := by
  intro hcov
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ, hI⟩ := wr_global hpre hX hO he hcov rfl
  obtain ⟨pos, hr, hl, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
  obtain ⟨tt, row, c, j, rfl, -, rfl, -⟩ := Store.ev_wr_inv hev
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  have hj := j.isLt
  obtain ⟨-, -, h3, h4⟩ := hcov
  simp only [Store.wrAcc] at h3 h4
  refine out_ne_state hpre (l := (P.stateLoc s h v k).at b)
    ⟨_, seqOf_lt hpre g, _, headOf_lt hpre hg, 16 * tt + row, by omega,
      ⟨8 * c + j.val, by omega⟩,
      ((P.stateLoc s h v k).at b).addr -
        (P.outLoc (seqOf P g) (headOf P g) (16 * tt + row) ⟨8 * c + j.val, by omega⟩).addr,
      ?_, ?_⟩
    ⟨s, hs, h, hh, v, k, b, hb, rfl⟩
  · simp only [Params.outLoc]
    omega
  · simp only [Params.outLoc, Params.stateLoc, Loc.at, Loc.mk.injEq, true_and] at h3 h4 ⊢
    omega

/-- An exit event is fired by a thread in the epilogue. -/
theorem exit_epilogue {g e pce : Nat} (he : X.get (g, e) = some ⟨pce, .exit⟩) :
    ∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 ≤ e := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  cases hst with
  | startup hI => exact (Bool.false_ne_true (kind_startup hpre hX hg he hσ hI)).elim
  | conversion past hj hI => exact (Bool.false_ne_true (kind_conversion hpre hX hg he hσ hI)).elim
  | carryLoad past hj hI => exact (Bool.false_ne_true (kind_carry hpre hX hg he hσ hI)).elim
  | compute hr past hj hin' hI => exact (Bool.false_ne_true (kind_compute hpre hX he hσ hI)).elim
  | producer hr past hj hen hI =>
    exact (Bool.false_ne_true (kind_producer hpre hX hg he hσ hr hI)).elim
  | store hr past hj hin' hI hW =>
    exact (Bool.false_ne_true (kind_store hpre hX hg he hσ (hI hub))).elim
  | epilogue past hj hW hI => exact ⟨_, _, past, hj⟩

/-- **`StoresIssued.outIssued`**: when the store leader of a block has exited, it has an event
for every byte of the output of every token of the block's sequence: a tensor store with a
slot that writes the byte, or a write event that covers it. They are events of its Store phase,
which it left before the epilogue. -/
theorem outIssued {s h e pce : Nat} (hs : s < P.sequences) (hh : h < P.heads)
    (he : X.get (storeLeader L (blockOf P s h), e) = some ⟨pce, .exit⟩) :
    ∀ t < P.length s, ∀ v : Fin 128, ∀ k < 2,
      (∃ i pc al sp x y z,
        X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ ∧
        TensorStore.writeLoc sp x y z = some ((P.outLoc s h t v).at k)) ∨
      (∃ i pc a bs, X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .wr a bs⟩ ∧
        a.Covers ((P.outLoc s h t v).at k)) := by
  intro t ht v k hk
  obtain ⟨-, htid, hwarp, hlane, hseq, hhead⟩ := storeLeader_role (L := L) hpre (h := h) hs
  generalize storeLeader L (blockOf P s h) = g at he htid hwarp hlane hseq hhead ⊢
  subst hseq hhead
  have hg := Frame.lt_of_get hX he
  obtain ⟨j0, s0, past, hj⟩ := exit_epilogue hpre hX he
  obtain ⟨j1, s1, hd, hle, hrole⟩ := past.entry
  have h128 : ¬ tid g < 128 := by omega
  rcases hrole with ⟨hc, -⟩ | ⟨hw4, -⟩ | ⟨-, hin, hout, -⟩
  · exact absurd hc h128
  · omega
  · rcases Store.outIssued_store hpre hX hg ⟨s1, hd.state, hin⟩ past.state hout hlane ht v hk
      with ⟨i, pc, al, sp, x, y, z, -, h1, h2⟩ | ⟨i, pc, a, bs, -, h1, h2⟩
    · exact .inl ⟨i, pc, al, sp, x, y, z, h1, h2⟩
    · exact .inr ⟨i, pc, a, bs, h1, h2⟩

/-- **`StoresIssued.stateIssued`**: when the store leader of a block has exited, it has issued
a tensor store with a slot that writes each byte of the final state of the block's sequence and
head (the 16 tensor stores of the epilogue). -/
theorem stateIssued {s h e pce : Nat} (hs : s < P.sequences) (hh : h < P.heads)
    (he : X.get (storeLeader L (blockOf P s h), e) = some ⟨pce, .exit⟩) :
    ∀ v k : Fin 128, ∀ b < 4, ∃ i pc al sp x y z,
      X.get (storeLeader L (blockOf P s h), i) = some ⟨pc, .tensorStore al sp⟩ ∧
      TensorStore.writeLoc sp x y z = some ((P.stateLoc s h v k).at b) := by
  intro v k b hb
  obtain ⟨-, htid, -, -, hseq, hhead⟩ := storeLeader_role (L := L) hpre (h := h) hs
  generalize storeLeader L (blockOf P s h) = g at he htid hseq hhead ⊢
  subst hseq hhead
  have hg := Frame.lt_of_get hX he
  obtain ⟨j0, s0, past, hj⟩ := exit_epilogue hpre hX he
  obtain ⟨i, pc, al, sp, x, y, z, -, h1, h2⟩ :=
    Epilogue.state_issued hpre hX hg (entered_epilogue past) hj he htid v k hb
  exact ⟨i, pc, al, sp, x, y, z, h1, h2⟩

end

end Buffers

/-! ### The three contracts -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The classification of the accesses of the buffer region** (`Protocol.UnionFacts`) for
the owner functions `owners P L`, for every consistent execution. -/
theorem unionFacts : UnionFacts L X (ctaTiles P) (owners P L) where
  thread := Buffers.thread hpre hX (Buffers.computeOwes hpre hX)
  load := Buffers.load hpre hX
  store := Buffers.store hpre hX
  bar_fence := Buffers.bar_fence hpre hX
  store_bar_wait := Buffers.store_bar_wait hpre hX
  polled s a _ he hb := Buffers.polled hpre hX s a he hb

/-- **The source bytes of the tensor stores are written** (`Protocol.StoreCover`) for the owner
functions `owners P L`, for every consistent execution. -/
theorem storeCover : StoreCover L X (owners P L) where
  store_in := Buffers.store_in hpre hX
  out_cover := Buffers.out_cover hpre hX (Buffers.computeOwes hpre hX)
  final_cover := Buffers.final_cover hpre hX
  matrix_len := Buffers.matrix_len hpre hX (Buffers.computeOwes hpre hX)
  out_lt _ _ := Buffers.outOwner_lt P _
  final_lt _ := Epilogue.finalOwner_lt P _

/-- **The events that write global memory** (`Protocol.StoresIssued`), for every consistent
execution. -/
theorem storesIssued : StoresIssued P L X where
  tile := Buffers.tile hpre hX
  elem := Buffers.elem hpre hX (Buffers.computeOwes hpre hX)
  final := Buffers.final hpre hX
  finalAsync := Buffers.finalAsync hpre hX (Buffers.computeOwes hpre hX)
  outIssued := Buffers.outIssued hpre hX
  stateIssued := Buffers.stateIssued hpre hX

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
