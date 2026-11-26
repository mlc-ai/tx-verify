-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.Life
public import Kernels.FlashKdaFwd.Proof.Protocol.Fences
public import Lemmas.Tensor.TensorTransfer
public import Lemmas.Tensor.TensorCompleteConsistentRead

@[expose] public section

/-! # The union region: classification of its accesses, and their order

The union region of a CTA (`InUnion L c`, offsets 32768 to 98304 of its shared-memory window)
is the FP32 state buffer; the three input buffers and the two output buffers of the tile loop
occupy the same bytes. `Union.lean` proves, for each pair of the nine classes of access, the
order of two accesses from counts. This file states the classification as a contract for the
thread layer and derives the order of every conflict from it:

* `UnionFacts L X T O`: the contract (below);
* `UnionFacts.ordered`: `∀ c, ConflictsOrdered L X (InUnion L c)`, from `UnionFacts`, the other
  thread-fact structures and `NoEvents`. `Export.lean` uses it for the field `bufOrdered` of
  `Top.SafetyFacts`. With it "the list of pairs is complete" is a Lean proof.

## The contract

Every field is about the events of one thread, or about one operation that one thread issues,
and about counts over the prefix of that thread's trace before the event: the number of
`bar.sync 0` (`bar0Before`), of arrivals on an mbarrier (`arrivals`), of successful polls of one
(`okPolls`), and of tensor loads that complete on one (`issuesTo`).

* `thread`: a thread access of a byte of the union region is of the thread's own CTA, follows
  the thread's successful poll of the state barrier, and has a `ThreadClass`:
  `early` (a read with at most five `bar.sync 0` before it), `input` (a compute thread's read
  of input buffer `s` with six before it, between its poll of `loadFull s` and its arrival on
  `loadEmpty s`: fewer arrivals than successful polls), `output` (a compute thread's write of
  output buffer `o` with six before it, between its poll of `storeEmpty o` and its arrival on
  `storeFull o`, of a byte it owns), `leader` (the store leader's read of output buffer `o` with
  six before it, between its poll of `storeFull o` and its arrival on `storeEmpty o`), `final`
  (a compute thread's write with seven before it, of a byte it owns).
* `load`: a tensor load that writes a byte of the region has a `LoadClass`: `init` (it
  completes on the state barrier and with `q` earlier such loads writes block `q`) or `tile`
  (it completes on `loadFull s`, is issued with six `bar.sync 0` before it and after the
  issuer's poll of the state barrier, writes input buffer `s`, and with `q` earlier loads on
  that barrier writes piece `q % 70`).
* `store`: a tensor store that reads a byte of the region is the store leader's, after its
  poll of the state barrier, and has a `StoreClass`: `tile` (six `bar.sync 0` before it, source
  in output buffer `o`, between the poll of `storeFull o` and the arrival on `storeEmpty o`) or
  `final` (eight before it).
* `bar_fence`: the sixth and the eighth `bar.sync 0` of a thread directly follow a proxy fence.
* `store_bar_wait`: between a store and a later `bar.sync 0` the store leader executes a
  `.read` bulk-group wait that covers the store.
* `polled`: after seven `bar.sync 0` a compute thread has polled `loadFull s` once per use.

"Owns" and "block", "piece" refer to four functions `O : Owners` from bytes to writers, a
parameter of the contract: two writers that may run at the same time (two compute threads in a
tile or in the final phase, two loads of a tile, two loads of the initial state) are told apart
by the value of the function at the byte. The thread layer picks the functions.

## What the simulator showed (`Gen/simulate.py`; all 192 threads; 0, 1, 16, 17, 37, 48, 80 tokens)

Every statement of the contract was tested on these runs before it was used, with no failure:

* every thread access of the region falls in one of the five classes with the stated count of
  `bar.sync 0` (3 or 5; 6; 7) and the stated inequality (which is an equality in the runs);
  every thread access follows the thread's poll of the state barrier;
* loads: issuer thread 128; a load of the initial state with `q` earlier ones has destination
  `32768 + 4096 q`; a tile load on `loadFull s` with `q` earlier ones has destination
  `32768 + 18048 s + pieceOff (q % 70)`, `pieceOff p = 256 p` for `p ≤ 16`, `256 p - 128` for
  `17 ≤ p ≤ 65`, `256 p + 128` for `p ≥ 66` (64 bytes at 16, 512 at 65, a 64-byte hole after
  16); six `bar.sync 0` and the state poll before it;
* stores: issuer thread 160; a tile store reads a 256-byte box of one output buffer; the
  final-state stores have eight `bar.sync 0` before them and sources `32768 + 4096 k`;
* writers: in every tile each byte of the output buffer has one writing thread, the same in
  all tiles, namely `32 * (x / 1024) + x % 512 / 16` for the byte at offset `x` of the buffer;
  each of the 65536 bytes of the final state has one writing thread;
* the event before a thread's sixth and eighth `bar.sync 0` is a proxy fence; no store is
  without a later `.read` group wait at a `bar.sync 0`, an arrival or the exit; a compute
  thread's events with seven `bar.sync 0` before them have all polls of `loadFull`.

The simulator does not model the byte layout inside a load's or a store's box, so "a load
writes only its block / its piece" was tested on the box start and size only.

## For the value layer: which write a read returns

`ConflictsOrdered.read_of_last` (`Lemmas/Protocol/RegionOrder.lean`) asks, for a read, a write
that is visible to it and such that every other visible write of the byte is that write or is
visible to it. From the lemmas here and in `Union.lean`:

* an `early` read (conversion loop, carry loads): the write of the initial-state load whose
  block holds the byte (`init_before_thread`). Every other writer of the byte is a tile load, an
  output write or a final-state write; the read is visible to each of them (`load_thread`,
  `bar_before`), so none of them is visible to the read.
* an `input` read in tile `t`: the write of the load of tile `t` whose piece holds the byte
  (`load_before_thread`); the loads of earlier uses of the stage and the initial-state load are
  visible to that load (`load_before_load`, `init_before_async`), and the read is visible to the
  loads of later uses (`LoadFacts.publish_input`) and to the final-state writes. A byte of the
  64-byte hole has no tile load; its last write is the initial-state load's.
* a store's source read or the store leader's generic read of an output buffer in tile `t`:
  the owner's write of tile `t` (`StoreFacts.publish_output`, `output_before_leader`); the
  owner's earlier writes precede it in its thread, the initial-state load is visible to it, and
  the read is visible to the owner's later writes (`StoreFacts.release_output`,
  `leader_before_output`) and to the final-state writes (`release_of_bar`, `bar_before`).
* a final-state store's source read: the owner's final-state write (`publish_of_bar`); every
  other writer of the byte is visible to that write (`bar_before`, `load_before_thread`,
  `init_before_thread`).

"Not visible" above uses that visibility at a byte has no cycle; these read-back lemmas are not
stated here.

## `storeSources`

The progress premise `storeSources` needs, beyond the order proved here, that the source writes
have been made. That is the contract `StoreCover` of `StoreCover.lean`, where
`UnionFacts.visibleReadSources` proves the premise's statement for one store. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

/-- **Which thread or which load writes a byte**, for the four classes of writers that run
concurrently. The contract `UnionFacts` is stated for any such four functions; the thread layer
chooses them (for example `out l = 32 * (x / 1024) + x % 512 / 16` for the byte at offset `x`
of an output buffer, which the simulator confirms). -/
structure Owners where
  /-- The compute thread (its index in the CTA) that writes a byte of an output buffer. -/
  out : Loc → Nat
  /-- The compute thread that writes a byte of the final state. -/
  final : Loc → Nat
  /-- The position, among the 70 loads of a tile, of the load that writes a byte of an input
  buffer. -/
  piece : Loc → Nat
  /-- The one of the 16 loads of the initial state that writes a byte. -/
  block : Loc → Nat

/-- **The class of a thread access** of byte `l` of the union region of CTA `c`, by event `i`
of thread `g`; `w` says whether it writes. -/
inductive ThreadClass (L : Launch) (X : Execution) (O : Owners) (c g i : Nat) (w : Bool)
    (l : Loc) : Prop
  /-- `R1`: a generic read of the conversion loop or of the carry loads, before the sixth
  `bar.sync 0`. -/
  | early (hw : w = false) (hbar : bar0Before X (g, i) ≤ 5)
  /-- `RI`: a compute thread's read of input buffer `s` in the tile loop, between its poll of
  `loadFull s` and its arrival on `loadEmpty s`. -/
  | input (a : Fin 128) (s : Fin 3) (hg : g = computeThread L c a) (hw : w = false)
      (hbar : bar0Before X (g, i) = 6) (hl : InInput L c s.val l)
      (hgate : arrivals ((Bar.loadEmpty s).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.loadFull s).loc L c) ((X.tr g).take i))
  /-- `WO`: a compute thread's write of output buffer `o` in the tile loop, between its poll of
  `storeEmpty o` and its arrival on `storeFull o`; the byte is the thread's own. -/
  | output (a : Fin 128) (o : Fin 2) (hg : g = computeThread L c a) (hw : w = true)
      (hbar : bar0Before X (g, i) = 6) (hl : InOutput L c o.val l)
      (hgate : arrivals ((Bar.storeFull o).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.storeEmpty o).loc L c) ((X.tr g).take i))
      (hown : O.out l = a.val)
  /-- `RG`: the store leader's generic read of output buffer `o` (the partial last tile),
  between its poll of `storeFull o` and its arrival on `storeEmpty o`. -/
  | leader (o : Fin 2) (hg : g = storeLeader L c) (hw : w = false)
      (hbar : bar0Before X (g, i) = 6) (hl : InOutput L c o.val l)
      (hgate : arrivals ((Bar.storeEmpty o).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take i))
  /-- `WF`: a compute thread's write of the final state, after the seventh `bar.sync 0`; the
  byte is the thread's own. -/
  | final (a : Fin 128) (hg : g = computeThread L c a) (hw : w = true)
      (hbar : bar0Before X (g, i) = 7) (hown : O.final l = a.val)

/-- **The class of a byte write of a tensor load** issued at event `i` of thread `g` with
specification `sp`, at byte `l` of the union region of CTA `c`. -/
inductive LoadClass (L : Launch) (X : Execution) (O : Owners) (c g i : Nat)
    (sp : TensorCopy.Spec) (l : Loc) : Prop
  /-- `A0`: a load of the initial state; with `q` earlier ones it writes block `q`. -/
  | init (hm : sp.mbar = Bar.state.loc L c)
      (hblock : O.block l = ((X.tr g).take i).countP (issuesTo (Bar.state.loc L c)))
  /-- `WL`: a load of a tile into input buffer `s`, issued in the tile loop after the issuer's
  poll of the state barrier; with `q` earlier ones on `loadFull s` it writes piece `q % 70`. -/
  | tile (s : Fin 3) (hm : sp.mbar = (Bar.loadFull s).loc L c)
      (hbar : bar0Before X (g, i) = 6) (hl : InInput L c s.val l)
      (hpiece : O.piece l =
        ((X.tr g).take i).countP (issuesTo ((Bar.loadFull s).loc L c)) % 70)
      (hpoll : 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take i))

/-- **The class of a source read of a tensor store** issued at event `i` of thread `g`, at
byte `l` of the union region of CTA `c`. -/
inductive StoreClass (L : Launch) (X : Execution) (c g i : Nat) (l : Loc) : Prop
  /-- `RS`: a store of a full tile from output buffer `o`, between the store leader's poll of
  `storeFull o` and its arrival on `storeEmpty o`. -/
  | tile (o : Fin 2) (hbar : bar0Before X (g, i) = 6) (hl : InOutput L c o.val l)
      (hgate : arrivals ((Bar.storeEmpty o).loc L c) ((X.tr g).take i) + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take i))
  /-- `RF`: a store of the final state, after the eighth `bar.sync 0`. -/
  | final (hbar : bar0Before X (g, i) = 8)

/-- **The contract for the union region** (offsets 32768 to 98304 of a CTA's window). Every
field is about the events of one thread, or about one operation that one thread issues, and
about counts over the prefix of its trace before the event. `T c` is the number of tiles of CTA
`c`; `O` names the writers of a byte (`Owners`). -/
structure UnionFacts (L : Launch) (X : Execution) (T : Nat → Nat) (O : Owners) : Prop where
  /-- A thread access of a byte of the union region is the thread's own CTA's, follows the
  thread's successful poll of the state barrier, and is of one of the five thread classes. -/
  thread : ∀ {g i c : Nat} {a : Acc} {w : Bool} {l : Loc}, X.Access (g, i) a w → a.Covers l →
    InUnion L c l → g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take i) ∧
      ThreadClass L X O c g i w l
  /-- A tensor load that writes a byte of the union region is of one of the two load
  classes. -/
  load : ∀ {g i pc al x y z c : Nat} {sp : TensorCopy.Spec} {l : Loc},
    X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩ → TensorCopy.writeLoc sp x y z = some l →
    InUnion L c l → LoadClass L X O c g i sp l
  /-- A tensor store that reads a byte of the union region is the store leader's, follows its
  successful poll of the state barrier, and is of one of the two store classes. -/
  store : ∀ {g i pc al x y z c : Nat} {sp : TensorStore.Spec} {l : Loc},
    X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ → TensorStore.readLoc sp x y z = some l →
    InUnion L c l → g = storeLeader L c ∧
      1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take i) ∧ StoreClass L X c g i l
  /-- The sixth and the eighth `bar.sync 0` of a thread (1402 and 3775) directly follow a
  `fence.proxy.async.shared::cta` (1401 and 3774). -/
  bar_fence : ∀ {g e pc : Nat} {cnt : Option Nat} {mode : BarMode},
    X.get (g, e) = some ⟨pc, .bar 0 cnt mode⟩ →
    bar0Before X (g, e) = 5 ∨ bar0Before X (g, e) = 7 →
      0 < e ∧ ∃ pcf, X.get (g, e - 1) =
        some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩
  /-- Between a store of the store leader and a later `bar.sync 0` of the leader, the leader
  executes a `.read` bulk-group wait that covers the store (3093, 3833). -/
  store_bar_wait : ∀ {c k e pc addr pce : Nat} {cnt : Option Nat} {mode : BarMode}
    {s : TensorStore.Spec}, X.get (storeLeader L c, k) = some ⟨pc, .tensorStore addr s⟩ →
    k < e → X.get (storeLeader L c, e) = some ⟨pce, .bar 0 cnt mode⟩ →
      ∃ w, k < w ∧ w < e ∧ BulkWaitsFor X .read (storeLeader L c, k) (storeLeader L c, w)
  /-- After the tile loop (seven `bar.sync 0`) a compute thread has polled `loadFull s`
  successfully once for each use of stage `s`. -/
  polled : ∀ {c e : Nat} {ev : Event} (s : Fin 3) (a : Fin 128), c < L.grid →
    X.get (computeThread L c a, e) = some ev → 7 ≤ bar0Before X (computeThread L c a, e) →
      uses 3 (T c) s ≤
        okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c a)).take e)

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat} {O : Owners}

/-! ## Helpers -/

/-- A one-byte footprint covers its own location only. -/
theorem covers_one {a : Acc} {l : Loc} (hs : a.size = 1) (h : a.Covers l) : a.loc = l := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases l with ⟨sp, ct, ad⟩
  rcases hloc : a.loc with ⟨sp', ct', ad'⟩
  rw [hloc] at h1 h2 h3 h4
  simp only at h1 h2 h3 h4
  subst h1 h2
  congr
  omega

/-- The event of a thread access: a read, a write or an atomic. -/
theorem access_kind {e : EvId} {a : Acc} {w : Bool} (h : X.Access e a w) :
    ∃ ev, X.get e = some ev ∧ ev.acc.isSome ∧ Execution.isBarId 0 ev = false := by
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩ <;>
    exact ⟨_, he, rfl, rfl⟩

/-- **The kinds of operation that touch a byte of the union region**: a thread access, a byte
write of a tensor load, or a source read of a tensor store. Every other asynchronous stage
touches global memory or needs an instruction the kernel does not have. -/
theorem intent_cases (hN : NoEvents K X) {ref : Ref} {a : Acc} {w : Bool} {l : Loc} {c : Nat}
    (hi : X.Intent ref a w) (ha : a.Covers l) (hl : InUnion L c l) :
    (∃ g i, ref = .thread (g, i) ∧ X.Access (g, i) a w) ∨
    (∃ g i pc al sp x y z, ref = .async (g, i) (.write (.load x y z)) ∧ w = true ∧
      X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩ ∧ TensorCopy.writeLoc sp x y z = some l) ∨
    (∃ g i pc al sp x y z, ref = .async (g, i) (.read (.store x y z)) ∧ w = false ∧
      X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ ∧ TensorStore.readLoc sp x y z = some l) := by
  have hsh : a.loc.space = .shared := ha.1.symm.trans hl.1
  rcases ref with ⟨g, i⟩ | ⟨⟨g, i⟩, p⟩
  · exact .inl ⟨g, i, rfl, hi⟩
  · obtain ⟨hw, hfp⟩ := hi
    cases p with
    | mmaRead isB idx =>
      obtain ⟨-, hfp⟩ := hfp
      rcases hfp with ⟨d, sp, acc, mask, ⟨pc, he⟩, -⟩ | ⟨c', k', cta, ⟨pc, he⟩, -⟩
      · exact (hN.tc _ _ _ he).elim
      · exact (hN.tc _ _ _ he).elim
    | readStore x y k =>
      obtain ⟨sp, addr, ⟨pc, he⟩, hloc, hsz⟩ := hfp
      rw [covers_one hsz ha] at hloc
      exact .inr (.inr ⟨g, i, pc, addr, sp, x, y, k, rfl, hw, he, hloc⟩)
    | writeLoad x y k =>
      obtain ⟨sp, addr, ⟨pc, he⟩, hloc, hsz⟩ := hfp
      rw [covers_one hsz ha] at hloc
      exact .inr (.inl ⟨g, i, pc, addr, sp, x, y, k, rfl, hw, he, hloc⟩)
    | readLoad x y k =>
      obtain ⟨sp, addr, -, hloc, -⟩ := hfp
      rw [Execution.tensor_readLoc_global hloc] at hsh
      cases hsh
    | readPrefetch x y k =>
      obtain ⟨sp, addr, -, hloc, -⟩ := hfp
      rw [TensorTransfer.sourceLoc_global hloc] at hsh
      cases hsh
    | readCopy =>
      rcases hfp with ⟨s, hcopy, -⟩ | hb
      · exact (hN.copy _ _ hcopy).elim
      · exact (hN.prefetch _ _ hb).elim
    | writeStore x y k =>
      obtain ⟨sp, addr, -, hloc, -⟩ := hfp
      rw [Execution.store_writeLoc_global hloc] at hsh
      cases hsh
    | oldStore x y k =>
      obtain ⟨sp, addr, -, -, hloc, -⟩ := hfp
      rw [Execution.store_writeLoc_global hloc] at hsh
      cases hsh
    | writeCta c' =>
      obtain ⟨s, tg, hcl, -⟩ := hfp
      exact (hN.clc _ _ _ hcl).elim
    | writeCopy =>
      obtain ⟨s, hcopy, -⟩ := hfp
      exact (hN.copy _ _ hcopy).elim
    | writeElem j =>
      obtain ⟨s, hcopy, -⟩ := hfp
      exact (hN.copy _ _ hcopy).elim
    | oldElem j =>
      obtain ⟨s, r, hcopy, -⟩ := hfp
      exact (hN.copy _ _ hcopy).elim
    | _ => exact hfp.elim

/-- A byte lies in one input buffer. -/
theorem input_stage_unique {c s s' : Nat} {l : Loc} (h : InInput L c s l)
    (h' : InInput L c s' l) : s = s' := by
  simp only [InInput, InShared] at h h'
  omega

/-- A byte lies in one output buffer. -/
theorem output_stage_unique {c o o' : Nat} {l : Loc} (h : InOutput L c o l)
    (h' : InOutput L c o' l) : o = o' := by
  simp only [InOutput, InShared] at h h'
  omega

/-- **A passed `bar.sync 0` has every thread's arrival of its ordinal**: when thread `h` has an
event after its `bar.sync 0` with `q` earlier ones, every thread `g` of the CTA has made its
`bar.sync 0` with `q` earlier ones. -/
theorem BarFacts.peer_bar0 (hB : BarFacts L X T) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) {g h k q : Nat} (hg : g < L.threads)
    (hcta : g / L.block = h / L.block) (hk : k < (X.tr h).length)
    (hq : q + 1 ≤ bar0Before X (h, k)) :
    ∃ e pc md, X.get (g, e) = some ⟨pc, .bar 0 none md⟩ ∧ bar0Before X (g, e) = q := by
  obtain ⟨j, pc, hjk, hbar, hord⟩ := hB.nth_bar0 hX hq
  have hh : h < L.threads := Frame.lt_of_get hX hbar
  have hq9 : q + 1 ≤ 9 := by
    have h9 := hB.bar0_le hh
    have hm := countP_take_mono (Execution.isBarId 0) (X.tr h) hk.le
    rw [List.take_length] at hm
    unfold bar0Before at hq
    simp only at hq
    omega
  obtain ⟨i, pc', md, hi, hio⟩ := (hB.sources0 hb).member_arrival_any hX (shape0 hb) hbar
    (show j + 1 < (X.tr h).length by omega) (g := g) hcta
    (Finset.mem_range.mpr (by rw [hb]; omega)) (by
      rintro ⟨jx, pcx, hx⟩
      have h9 := hB.bar0_exit hg hx
      obtain ⟨i, pci, -, hi, hio⟩ := hB.nth_bar0 hX (g := g) (k := (X.tr g).length) (q := q)
        (by rw [List.take_length, h9]; exact hq9)
      exact ⟨i, pci, .sync, hi, hio.trans hord.symm⟩)
  exact ⟨i, pc', md, hi, hio.trans hord⟩

/-- **The proxy fence between an access and the next publishing CTA barrier.** An access of
thread `g` with at most `q` `bar.sync 0` before it (`q` is 5 or 7) is followed, once a thread
`h` of the CTA has passed its `bar.sync 0` with `q` earlier ones, by a proxy fence of `g` with
fewer `bar.sync 0` up to it than `h` has. -/
theorem UnionFacts.fence_before (U : UnionFacts L X T O) (hB : BarFacts L X T)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) {g i h k q : Nat} {a : Acc} {w : Bool}
    (hacc : X.Access (g, i) a w) (hq : q = 5 ∨ q = 7) (hi : bar0Before X (g, i) ≤ q)
    (hcta : g / L.block = h / L.block) (hk : k < (X.tr h).length)
    (hlt : q + 1 ≤ bar0Before X (h, k)) :
    ∃ f pcf, i < f ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      bar0UpTo X (g, f) < bar0Before X (h, k) := by
  obtain ⟨ev, hev, hacc', hnb⟩ := access_kind hacc
  have hg := Frame.lt_of_get hX hev
  obtain ⟨e, pc, md, he, heq⟩ := hB.peer_bar0 hX hb hg hcta hk hlt
  obtain ⟨hpos, pcf, hf⟩ := U.bar_fence he (by
    rcases hq with rfl | rfl
    · exact .inl heq
    · exact .inr heq)
  have hie : i < e := by
    by_contra hcon
    have hei : e < i := by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hcon) with h1 | h1
      · exact h1
      · subst h1
        rw [hev] at he
        cases he
        simp [Execution.isBarId] at hnb
    have h1 := countP_take_succ (p := Execution.isBarId 0) he (by simp [Execution.isBarId])
    have h2 := countP_take_mono (Execution.isBarId 0) (X.tr g) (show e + 1 ≤ i from hei)
    unfold bar0Before at hi heq
    simp only at hi heq
    omega
  have hne : i ≠ e - 1 := by
    intro h1
    rw [h1, hf] at hev
    cases hev
    simp [Event.acc] at hacc'
  refine ⟨e - 1, pcf, by omega, hf, ?_⟩
  unfold bar0UpTo
  unfold bar0Before at heq hlt ⊢
  simp only at heq hlt ⊢
  rw [show e - 1 + 1 = e by omega]
  omega

/-! ## Two thread accesses -/

/-- A compute thread's write of an output buffer and the store leader's generic read of it are
ordered through the store pipeline, one way or the other by the counts. -/
theorem output_leader (hSt : StoreFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T)
    (hN : NoEvents K X) (hX : Consistent L K A mem0 X) (hb : L.block = 192) {c : Nat}
    (hc : c < L.grid) {o o' : Fin 2} (ga : Fin 128) {i k : Nat} {l : Loc}
    (hl1 : InOutput L c o.val l) (hl2 : InOutput L c o'.val l)
    (hi : i < (X.tr (computeThread L c ga)).length) (hk : k < (X.tr (storeLeader L c)).length)
    (hgt1 : arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c ga)).take i) + 1 ≤
      okPolls ((Bar.storeEmpty o).loc L c) ((X.tr (computeThread L c ga)).take i))
    (hgt2 : arrivals ((Bar.storeEmpty o').loc L c) ((X.tr (storeLeader L c)).take k) + 1 ≤
      okPolls ((Bar.storeFull o').loc L c) ((X.tr (storeLeader L c)).take k)) :
    modelCausality L X l (.thread (computeThread L c ga, i)) (.thread (storeLeader L c, k)) ∨
      modelCausality L X l (.thread (storeLeader L c, k))
        (.thread (computeThread L c ga, i)) := by
  obtain rfl : o = o' := Fin.ext (output_stage_unique hl1 hl2)
  by_cases h : arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c ga)).take i) + 1 ≤
      okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k)
  · exact .inl (output_before_leader hSt hI hB hN hX hb hc o ga le_rfl hk h)
  · exact .inr (leader_before_output hSt hI hB hN hX hb hc o ga le_rfl hi (by omega))

/-- **Two conflicting thread accesses of a byte of the union region are ordered.** -/
theorem UnionFacts.thread_thread (U : UnionFacts L X T O) (hSt : StoreFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) {c g i h k : Nat} {a b : Acc}
    {w w' : Bool} {l : Loc} (he : X.Access (g, i) a w) (hf : X.Access (h, k) b w')
    (hne : (g, i) ≠ (h, k)) (hw : w = true ∨ w' = true) (ha : a.Covers l) (hb' : b.Covers l)
    (hl : InUnion L c l) :
    modelCausality L X l (.thread (g, i)) (.thread (h, k)) ∨
      modelCausality L X l (.thread (h, k)) (.thread (g, i)) := by
  obtain ⟨hgc, -, hce⟩ := U.thread he ha hl
  obtain ⟨hhc, -, hcf⟩ := U.thread hf hb' hl
  obtain ⟨ev1, hev1, -, -⟩ := access_kind he
  obtain ⟨ev2, hev2, -, -⟩ := access_kind hf
  have hg := Frame.lt_of_get hX hev1
  have hh := Frame.lt_of_get hX hev2
  have hc : c < L.grid := hgc ▸ cta_lt hb hg
  have hi : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hev1).1
  have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hev2).1
  rcases Nat.lt_trichotomy (bar0Before X (g, i)) (bar0Before X (h, k)) with hlt | heq | hgt
  · exact .inl (bar_before hB hX hb ⟨hg, hh, hgc.trans hhc.symm⟩ hk
      (by rw [bar0UpTo_of_access he]; exact hlt))
  · -- the same phase
    have same : g = h → modelCausality L X l (.thread (g, i)) (.thread (h, k)) ∨
        modelCausality L X l (.thread (h, k)) (.thread (g, i)) := by
      intro hgh
      subst hgh
      rcases Nat.lt_trichotomy i k with h1 | h1 | h1
      · exact .inl (same_thread he hf h1 ha hb')
      · exact absurd (by rw [h1]) hne
      · exact .inr (same_thread hf he h1 hb' ha)
    rcases hce with ⟨hw1, hb1⟩ | ⟨a1, s1, hg1, hw1, hb1, hl1, hgt1⟩ |
      ⟨a1, o1, hg1, hw1, hb1, hl1, hgt1, hown1⟩ | ⟨o1, hg1, hw1, hb1, hl1, hgt1⟩ |
      ⟨a1, hg1, hw1, hb1, hown1⟩
    · rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, hg2, hw2, hb2, hown2⟩
      · subst hw1 hw2
        simp at hw
      all_goals omega
    · rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, hg2, hw2, hb2, hown2⟩
      · omega
      · subst hw1 hw2
        simp at hw
      · exact (input_output_apart s1.isLt hl1 hl2).elim
      · subst hw1 hw2
        simp at hw
      · omega
    · rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, hg2, hw2, hb2, hown2⟩
      · omega
      · exact (input_output_apart s2.isLt hl2 hl1).elim
      · obtain rfl : a1 = a2 := Fin.ext (hown1.symm.trans hown2)
        exact same (hg1.trans hg2.symm)
      · subst hg1 hg2
        exact output_leader hSt hI hB hN hX hb hc a1 hl1 hl2 hi hk hgt1 hgt2
      · omega
    · rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, hg2, hw2, hb2, hown2⟩
      · omega
      · subst hw1 hw2
        simp at hw
      · subst hg1 hg2
        exact (output_leader hSt hI hB hN hX hb hc a2 hl2 hl1 hk hi hgt2 hgt1).symm
      · subst hw1 hw2
        simp at hw
      · omega
    · rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
        ⟨a2, hg2, hw2, hb2, hown2⟩
      · omega
      · omega
      · omega
      · omega
      · obtain rfl : a1 = a2 := Fin.ext (hown1.symm.trans hown2)
        exact same (hg1.trans hg2.symm)
  · exact .inr (bar_before hB hX hb ⟨hh, hg, hhc.trans hgc.symm⟩ hi
      (by rw [bar0UpTo_of_access hf]; exact hgt))

/-! ## A tensor load and a thread access -/

/-- An event that is no `bar.sync 0` and has no more `bar.sync 0` before it than a `bar.sync 0`
event of its thread comes before that event. -/
theorem before_bar {g i e pc : Nat} {cnt : Option Nat} {mode : BarMode} {ev : Event}
    (he : X.get (g, e) = some ⟨pc, .bar 0 cnt mode⟩) (hev : X.get (g, i) = some ev)
    (hnb : Execution.isBarId 0 ev = false)
    (hle : bar0Before X (g, i) ≤ bar0Before X (g, e)) : i < e := by
  by_contra hcon
  have hei : e < i := by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hcon) with h1 | h1
    · exact h1
    · subst h1
      rw [hev] at he
      cases he
      simp [Execution.isBarId] at hnb
  have h1 := countP_take_succ (p := Execution.isBarId 0) he (by simp [Execution.isBarId])
  have h2 := countP_take_mono (Execution.isBarId 0) (X.tr g) (show e + 1 ≤ i from hei)
  unfold bar0Before at hle
  simp only at hle
  omega

/-- The footprint of a byte write of a load covers its byte. -/
theorem load_covers {g i pc al x y z : Nat} {sp : TensorCopy.Spec} {l : Loc}
    (hiss : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩)
    (hwl : TensorCopy.writeLoc sp x y z = some l) :
    AsyncCovers X (g, i) (.write (.load x y z)) l :=
  ⟨{ loc := l, size := 1 }, true, ⟨rfl, sp, al, ⟨pc, hiss⟩, hwl, rfl⟩,
    ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩

/-- The footprint of a source read of a store covers its byte. -/
theorem store_covers {g i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc}
    (hiss : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hrl : TensorStore.readLoc sp x y z = some l) :
    AsyncCovers X (g, i) (.read (.store x y z)) l :=
  ⟨{ loc := l, size := 1 }, false, ⟨rfl, sp, al, ⟨pc, hiss⟩, hrl, rfl⟩,
    ⟨rfl, rfl, le_rfl, Nat.lt_succ_self _⟩⟩

/-- An issue of a load has fewer earlier issues on its barrier than the thread has in all. -/
theorem issues_lt {g i pc al : Nat} {sp : TensorCopy.Spec} {m : Loc}
    (hiss : X.get (g, i) = some ⟨pc, .tensorIssue al sp⟩) (hm : sp.mbar = m) :
    ((X.tr g).take i).countP (issuesTo m) + 1 ≤ (X.tr g).countP (issuesTo m) := by
  have h1 := countP_take_succ (p := issuesTo m) hiss (by simp [issuesTo, hm])
  have h2 := (List.take_sublist (i + 1) (X.tr g)).countP_le (p := issuesTo m)
  omega

section pairs
variable (U : UnionFacts L X T O) (hF : LifeFacts L X T) (hLd : LoadFacts L X)
  (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T)
  (hN : NoEvents K X) (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include U hF hLd hSt hS hI hB hN hX hb

omit hSt in
/-- **A byte write of a tensor load and a thread access of the same byte are ordered.** -/
theorem UnionFacts.load_thread {c gl il pc al x y z h k : Nat} {sp : TensorCopy.Spec}
    {b : Acc} {w' : Bool} {l : Loc}
    (hiss : X.get (gl, il) = some ⟨pc, .tensorIssue al sp⟩)
    (hwl : TensorCopy.writeLoc sp x y z = some l) (hf : X.Access (h, k) b w')
    (hb' : b.Covers l) (hl : InUnion L c l) :
    modelCausality L X l (.async (gl, il) (.write (.load x y z))) (.thread (h, k)) ∨
      modelCausality L X l (.thread (h, k)) (.async (gl, il) (.write (.load x y z))) := by
  have hcov := load_covers hiss hwl
  obtain ⟨hhc, hpoll, hcf⟩ := U.thread hf hb' hl
  have hcl := U.load hiss hwl hl
  obtain ⟨ev2, hev2, -, -⟩ := access_kind hf
  have hh := Frame.lt_of_get hX hev2
  have hgl := Frame.lt_of_get hX hiss
  have hc : c < L.grid := hhc ▸ cta_lt hb hh
  have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hev2).1
  have hil : il < (X.tr gl).length := (List.getElem?_eq_some_iff.mp hiss).1
  have hldiv : loadLeader L c / L.block = c := thr_div hb (by decide)
  rcases hcl with ⟨hm, hblock⟩ | ⟨s, hm, hbar, hlin, hpiece, hpollL⟩
  · -- a load of the initial state: the thread polled the state barrier
    obtain ⟨rfl, -, -⟩ := hS.issue hgl hiss hm
    obtain ⟨j, pcw, par, acq, sc, hjk, hw, -⟩ :=
      MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpoll
    exact .inl (init_before_thread hS hI hB hN hX hb hc hiss hm hw hjk hk hcov)
  · obtain ⟨rfl, -, hge, -⟩ := hLd.full_issue hgl hiss hm
    rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
      ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
      ⟨a2, hg2, hw2, hb2, hown2⟩
    · -- an early read: the thread's fence 1401, then the CTA barrier
      obtain ⟨f, pcf, hif, hfget, hlt⟩ := U.fence_before hB hX hb hf (.inl rfl) hb2
        (hhc.trans hldiv.symm) hil (by omega)
      exact .inr (publish_of_bar (hB.handoff0 hX hb) hif hfget
        ⟨hh, hgl, hhc.trans hldiv.symm⟩ hil hlt hl.1 (hl.2.1.trans hhc.symm) hcov)
    · -- a read of the input buffer
      obtain rfl : s = s2 := Fin.ext (input_stage_unique hlin hl2)
      subst hg2
      by_cases hq : ((X.tr (loadLeader L c)).take il).countP
          (issuesTo ((Bar.loadFull s).loc L c)) / 70 + 1 ≤
          okPolls ((Bar.loadFull s).loc L c) ((X.tr (computeThread L c a2)).take k)
      · exact .inl (load_before_thread hLd hI hB hN hX hb hc s hiss hm a2 hk hq hcov)
      · exact .inr (hLd.publish_input hI hB hN hX hb hc s a2 hf hb' hl2 le_rfl hil
          (by omega) hcov)
    · exact (input_output_apart s.isLt hlin hl2).elim
    · exact (input_output_apart s.isLt hlin hl2).elim
    · -- a write of the final state: the thread polled every use
      subst hg2
      have hp := U.polled s a2 hc hev2 (by omega)
      have h1 := hF.full_issues s hc
      have h2 := issues_lt hiss hm
      exact .inl (load_before_thread hLd hI hB hN hX hb hc s hiss hm a2 hk (by omega) hcov)

omit hF hLd hS in
/-- **A source read of a tensor store and a thread write of the same byte are ordered.** -/
theorem UnionFacts.store_thread {c gs is pc al x y z h k : Nat} {sp : TensorStore.Spec}
    {b : Acc} {l : Loc} (hiss : X.get (gs, is) = some ⟨pc, .tensorStore al sp⟩)
    (hrl : TensorStore.readLoc sp x y z = some l) (hf : X.Access (h, k) b true)
    (hb' : b.Covers l) (hl : InUnion L c l) :
    modelCausality L X l (.async (gs, is) (.read (.store x y z))) (.thread (h, k)) ∨
      modelCausality L X l (.thread (h, k)) (.async (gs, is) (.read (.store x y z))) := by
  have hcov := store_covers hiss hrl
  obtain ⟨rfl, hpollS, hcs⟩ := U.store hiss hrl hl
  obtain ⟨hhc, -, hcf⟩ := U.thread hf hb' hl
  obtain ⟨ev2, hev2, -, -⟩ := access_kind hf
  have hh := Frame.lt_of_get hX hev2
  have hgs := Frame.lt_of_get hX hiss
  have hc : c < L.grid := hhc ▸ cta_lt hb hh
  have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp hev2).1
  have his : is < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp hiss).1
  have hsdiv : storeLeader L c / L.block = c := thr_div hb (by decide)
  -- the final-state stores: the thread's fence 3774, then the CTA barrier
  have hfinal : bar0Before X (storeLeader L c, is) = 8 → bar0Before X (h, k) ≤ 7 →
      modelCausality L X l (.thread (h, k))
        (.async (storeLeader L c, is) (.read (.store x y z))) := by
    intro h8 h7
    obtain ⟨f, pcf, hif, hfget, hlt⟩ := U.fence_before hB hX hb hf (.inr rfl) h7
      (hhc.trans hsdiv.symm) his (by omega)
    exact publish_of_bar (hB.handoff0 hX hb) hif hfget ⟨hh, hgs, hhc.trans hsdiv.symm⟩ his hlt
      hl.1 (hl.2.1.trans hhc.symm) hcov
  rcases hcf with ⟨hw2, hb2⟩ | ⟨a2, s2, hg2, hw2, hb2, hl2, hgt2⟩ |
    ⟨a2, o2, hg2, hw2, hb2, hl2, hgt2, hown2⟩ | ⟨o2, hg2, hw2, hb2, hl2, hgt2⟩ |
    ⟨a2, hg2, hw2, hb2, hown2⟩
  · cases hw2
  · cases hw2
  · -- a write of the output buffer
    rcases hcs with ⟨o, hbar, hlo, hgate⟩ | hbar8
    · obtain rfl : o = o2 := Fin.ext (output_stage_unique hlo hl2)
      subst hg2
      by_cases hq : arrivals ((Bar.storeFull o).loc L c)
          ((X.tr (computeThread L c a2)).take k) + 1 ≤
          okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take is)
      · exact .inr (hSt.publish_output hI hB hN hX hb hc o a2 hf hb' hl2 le_rfl his hq hcov)
      · exact .inl (hSt.release_output hI hB hN hX hb hc o a2 hiss hrl hlo le_rfl hk
          (by omega) hcov)
    · exact .inr (hfinal hbar8 (by omega))
  · cases hw2
  · -- a write of the final state
    rcases hcs with ⟨o, hbar, hlo, hgate⟩ | hbar8
    · -- the leader's group wait before its seventh `bar.sync 0`
      obtain ⟨e, pce, md, he, heq⟩ := hB.peer_bar0 hX hb hgs (hsdiv.trans hhc.symm) hk
        (show 6 + 1 ≤ bar0Before X (h, k) by omega)
      have hise : is < e := before_bar he hiss rfl (by omega)
      obtain ⟨w, hkw, hwe, hwait⟩ := U.store_bar_wait hiss hise he
      have hel : e < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp he).1
      refine .inl (release_of_bar hX (hB.handoff0 hX hb) hwait (by omega)
        ⟨hgs, hh, hsdiv.trans hhc.symm⟩ hk ?_ hcov)
      have hm := countP_take_mono (Execution.isBarId 0) (X.tr (storeLeader L c))
        (show w + 1 ≤ e from hwe)
      unfold bar0UpTo
      unfold bar0Before at heq hb2 ⊢
      simp only at heq hb2 ⊢
      omega
    · exact .inr (hfinal hbar8 (by omega))

omit U hF hLd hSt hS hI hB hN hX hb in
/-- Two byte writes of one load at one byte are one stage: distinct slots of a load have
distinct bytes. -/
theorem same_load {g i x y z x' y' z' : Nat} {sp : TensorCopy.Spec} {l : Loc}
    (hw1 : TensorCopy.writeLoc sp x y z = some l)
    (hw2 : TensorCopy.writeLoc sp x' y' z' = some l) :
    (Ref.async (g, i) (.write (.load x y z))) = .async (g, i) (.write (.load x' y' z')) := by
  obtain ⟨s1, hs1, hl1⟩ := Option.map_eq_some_iff.mp hw1
  obtain ⟨s2, hs2, hl2⟩ := Option.map_eq_some_iff.mp hw2
  have hslot : s1 = s2 :=
    TensorTransfer.sharedByte_injective _ _ (congrArg Loc.addr (hl1.trans hl2.symm))
  obtain ⟨a1, a2, a3⟩ := TensorCopy.slotAt_coordinates hs1
  obtain ⟨b1, b2, b3⟩ := TensorCopy.slotAt_coordinates hs2
  subst hslot
  rw [← a1, ← a2, ← a3, ← b1, ← b2, ← b3]

omit hF hSt in
/-- **Two byte writes of tensor loads at one byte are ordered.** -/
theorem UnionFacts.load_load {c g1 i1 pc1 al1 x y z g2 i2 pc2 al2 x' y' z' : Nat}
    {sp1 sp2 : TensorCopy.Spec} {l : Loc}
    (h1 : X.get (g1, i1) = some ⟨pc1, .tensorIssue al1 sp1⟩)
    (hw1 : TensorCopy.writeLoc sp1 x y z = some l)
    (h2 : X.get (g2, i2) = some ⟨pc2, .tensorIssue al2 sp2⟩)
    (hw2 : TensorCopy.writeLoc sp2 x' y' z' = some l)
    (hne : (Ref.async (g1, i1) (.write (.load x y z))) ≠
      .async (g2, i2) (.write (.load x' y' z')))
    (hl : InUnion L c l) :
    modelCausality L X l (.async (g1, i1) (.write (.load x y z)))
        (.async (g2, i2) (.write (.load x' y' z'))) ∨
      modelCausality L X l (.async (g2, i2) (.write (.load x' y' z')))
        (.async (g1, i1) (.write (.load x y z))) := by
  have hcov1 := load_covers h1 hw1
  have hcov2 := load_covers h2 hw2
  have hc1 := U.load h1 hw1 hl
  have hc2 := U.load h2 hw2 hl
  have hg1 := Frame.lt_of_get hX h1
  have hg2 := Frame.lt_of_get hX h2
  have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp h1).1
  have hk2 : i2 < (X.tr g2).length := (List.getElem?_eq_some_iff.mp h2).1
  -- one issue: the two stages are the same
  have hsame : g1 = g2 → i1 = i2 → False := by
    rintro rfl rfl
    rw [h1] at h2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorIssue.injEq] at h2
    obtain ⟨-, -, rfl⟩ := h2
    exact hne (same_load hw1 hw2)
  have hldiv : loadLeader L c / L.block = c := thr_div hb (by decide)
  rcases hc1 with ⟨hm1, hblock1⟩ | ⟨s1, hm1, hbar1, hl1, hpiece1, hpoll1⟩
  · obtain ⟨rfl, -, -⟩ := hS.issue hg1 h1 hm1
    have hc : c < L.grid := by
      have := cta_lt hb hg1
      rwa [hldiv] at this
    rcases hc2 with ⟨hm2, hblock2⟩ | ⟨s2, hm2, hbar2, hl2, hpiece2, hpoll2⟩
    · -- two loads of the initial state write different blocks
      obtain ⟨rfl, -, -⟩ := hS.issue hg2 h2 hm2
      exact (hsame rfl (nthEv_unique (p := issuesTo (Bar.state.loc L c)) h1
        (by simp [issuesTo, hm1]) h2 (by simp [issuesTo, hm2])
        (hblock1.symm.trans hblock2))).elim
    · obtain ⟨rfl, -, -, -⟩ := hLd.full_issue hg2 h2 hm2
      obtain ⟨j, pcw, par, acq, sc, hjk, hw, -⟩ :=
        MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpoll2
      exact .inl (init_before_async hS hI hB hN hX hb hc h1 hm1 hw hjk hk2 hcov1 hcov2)
  · obtain ⟨rfl, -, hge1, -⟩ := hLd.full_issue hg1 h1 hm1
    have hc : c < L.grid := by
      have := cta_lt hb hg1
      rwa [hldiv] at this
    rcases hc2 with ⟨hm2, hblock2⟩ | ⟨s2, hm2, hbar2, hl2, hpiece2, hpoll2⟩
    · obtain ⟨rfl, -, -⟩ := hS.issue hg2 h2 hm2
      obtain ⟨j, pcw, par, acq, sc, hjk, hw, -⟩ :=
        MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpoll1
      exact .inr (init_before_async hS hI hB hN hX hb hc h2 hm2 hw hjk hk1 hcov2 hcov1)
    · -- two loads of tiles
      obtain rfl : s1 = s2 := Fin.ext (input_stage_unique hl1 hl2)
      obtain ⟨rfl, -, hge2, -⟩ := hLd.full_issue hg2 h2 hm2
      rcases Nat.lt_trichotomy
          (((X.tr (loadLeader L c)).take i1).countP
            (issuesTo ((Bar.loadFull s1).loc L c)) / 70)
          (((X.tr (loadLeader L c)).take i2).countP
            (issuesTo ((Bar.loadFull s1).loc L c)) / 70) with hlt | heq | hgt
      · exact .inl (load_before_load hLd hI hB hN hX hb hc s1 h1 hm1 hk2 (by omega)
          hcov1 hcov2)
      · -- one tile: different loads write different pieces
        refine (hsame rfl (nthEv_unique (p := issuesTo ((Bar.loadFull s1).loc L c)) h1
          (by simp [issuesTo, hm1]) h2 (by simp [issuesTo, hm2]) ?_)).elim
        have hp := hpiece1.symm.trans hpiece2
        omega
      · exact .inr (load_before_load hLd hI hB hN hX hb hc s1 h2 hm2 hk1 (by omega)
          hcov2 hcov1)

omit hSt in
/-- **A byte write of a tensor load is visible to a source read of a tensor store of the same
byte.** -/
theorem UnionFacts.load_store {c g1 i1 pc1 al1 x y z g2 i2 pc2 al2 x' y' z' : Nat}
    {sp1 : TensorCopy.Spec} {sp2 : TensorStore.Spec} {l : Loc}
    (h1 : X.get (g1, i1) = some ⟨pc1, .tensorIssue al1 sp1⟩)
    (hw1 : TensorCopy.writeLoc sp1 x y z = some l)
    (h2 : X.get (g2, i2) = some ⟨pc2, .tensorStore al2 sp2⟩)
    (hr2 : TensorStore.readLoc sp2 x' y' z' = some l) (hl : InUnion L c l) :
    modelCausality L X l (.async (g1, i1) (.write (.load x y z)))
      (.async (g2, i2) (.read (.store x' y' z'))) := by
  have hcov1 := load_covers h1 hw1
  have hcov2 := store_covers h2 hr2
  obtain ⟨rfl, hpollS, hcs⟩ := U.store h2 hr2 hl
  have hc1 := U.load h1 hw1 hl
  have hg1 := Frame.lt_of_get hX h1
  have hg2 := Frame.lt_of_get hX h2
  have hk2 : i2 < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp h2).1
  have hsdiv : storeLeader L c / L.block = c := thr_div hb (by decide)
  have hc : c < L.grid := by
    have := cta_lt hb hg2
    rwa [hsdiv] at this
  rcases hc1 with ⟨hm1, hblock1⟩ | ⟨s, hm1, hbar1, hl1, hpiece1, hpoll1⟩
  · -- a load of the initial state: the store leader polled the state barrier
    obtain ⟨rfl, -, -⟩ := hS.issue hg1 h1 hm1
    obtain ⟨j, pcw, par, acq, sc, hjk, hw, -⟩ :=
      MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpollS
    exact init_before_async hS hI hB hN hX hb hc h1 hm1 hw hjk hk2 hcov1 hcov2
  · obtain ⟨rfl, -, -, -⟩ := hLd.full_issue hg1 h1 hm1
    rcases hcs with ⟨o, hbar, hlo, hgate⟩ | hbar8
    · exact (input_output_apart s.isLt hl1 hlo).elim
    · -- a final-state store: compute thread 0 polled the load's use before its eighth
      -- `bar.sync 0`, which the store leader has passed
      have hc0 := computeThread_lt hb hc 0
      have hc0div : computeThread L c 0 / L.block = c := computeThread_div hb 0
      obtain ⟨e, pce, md, he, heq⟩ := hB.peer_bar0 hX hb hc0 (hc0div.trans hsdiv.symm) hk2
        (show 7 + 1 ≤ bar0Before X (storeLeader L c, i2) by omega)
      have hp := U.polled s 0 hc he (by omega)
      have h3 := hF.full_issues s hc
      have h4 := issues_lt h1 hm1
      obtain ⟨j, pcw, par, acq, sc, hje, hw, hu⟩ := MbarRing.UnitHandoff.exists_poll
        (X := X) (m := (Bar.loadFull s).loc L c) (h := computeThread L c 0) (f := e)
        (c := ((X.tr (loadLeader L c)).take i1).countP
          (issuesTo ((Bar.loadFull s).loc L c)) / 70) (by omega)
      have hbc : baseCausality L X (computeThread L c 0, j) (storeLeader L c, i2) := by
        refine hB.handoff0 hX hb _ _ _ _ ⟨hc0, hg2, hc0div.trans hsdiv.symm⟩ hk2 ?_
        have hm := countP_take_mono (Execution.isBarId 0) (X.tr (computeThread L c 0))
          (show j + 1 ≤ e from hje)
        unfold bar0UpTo
        unfold bar0Before at heq hbar8 ⊢
        simp only at heq hbar8 ⊢
        omega
      exact load_before_async hLd hI hB hN hX hb hc s h1 hm1 0 hw hu
        ⟨hg1, hg2, (thr_div hb (by decide)).trans hsdiv.symm⟩ hbc hcov1 hcov2

/-- **Every conflict on the union region of a CTA is ordered**: the case split over the kinds
and classes of the two operations. This is the premise of `Facts.bufOrdered`. -/
theorem UnionFacts.ordered (c : Nat) : ConflictsOrdered L X (InUnion L c) := by
  intro e f a b l hconf ha hb' hl
  obtain ⟨hne, we, wf, hie, hif, hwr, -⟩ := hconf
  rcases intent_cases hN hie ha hl with ⟨g1, i1, rfl, he⟩ |
      ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, rfl, he, hle⟩ |
      ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, rfl, he, hle⟩ <;>
    rcases intent_cases hN hif hb' hl with ⟨g2, i2, rfl, hf⟩ |
      ⟨g2, i2, pc2, al2, sp2, x2, y2, z2, rfl, rfl, hf, hlf⟩ |
      ⟨g2, i2, pc2, al2, sp2, x2, y2, z2, rfl, rfl, hf, hlf⟩
  · exact U.thread_thread hSt hI hB hN hX hb he hf (fun h => hne (by rw [h])) hwr ha hb' hl
  · exact (U.load_thread hF hLd hS hI hB hN hX hb hf hlf he ha hl).symm
  · have hw : we = true := by simpa using hwr
    subst hw
    exact (U.store_thread hSt hI hB hN hX hb hf hlf he ha hl).symm
  · exact U.load_thread hF hLd hS hI hB hN hX hb he hle hf hb' hl
  · exact U.load_load hLd hS hI hB hN hX hb he hle hf hlf hne hl
  · exact .inl (U.load_store hF hLd hS hI hB hN hX hb he hle hf hlf hl)
  · have hw : wf = true := by simpa using hwr
    subst hw
    exact U.store_thread hSt hI hB hN hX hb he hle hf hb' hl
  · exact .inr (U.load_store hF hLd hS hI hB hN hX hb hf hlf he hle hl)
  · simp at hwr

end pairs

end PTX.Kernels.FlashKdaFwd.Protocol
