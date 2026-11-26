-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.ReadBack
public import Lemmas.TensorStore.SourceBytes

@[expose] public section

/-! # Which write a read of an output buffer returns, and what a tensor store writes

The last part of the read-back theorems (`ReadBack.lean` has the input buffers, the early reads
and the bf16 state copy). The bytes of the result leave the block (the "CTA") through its store
leader (thread 160 of the block), in three ways:

1. **a partial last tile**: the store leader reads the live rows of the output buffer with
   ordinary loads (`ld.shared.v4.b32`: four read events of four bytes each) and writes them to
   global memory with `st.global.b16`;
2. **a full tile**: sixteen tensor stores (asynchronous copies from shared to global memory)
   whose source is the output buffer;
3. **the final state**: sixteen tensor stores whose source is the FP32 state buffer, which is
   the whole union region.

In all three the bytes read are the bytes that a compute thread (threads 0 to 127) wrote. This
file says which write: the **last write of the byte by the compute thread that owns it**, in the
tile for (1) and (2), in the epilogue for (3).

## The witness: `LastWrite`

`LastWrite X g l cnt n iw aw bw`: event `iw` of thread `g` is a write event with footprint `aw`
and bytes `bw` that covers byte `l`; a count `cnt iw` over the thread's earlier events is `n`;
and no later write event of the thread that covers `l` has count `n`. Two instances:

* `OutLast L X c o ga u l iw aw bw`: thread = compute thread `ga` of block `c`, count = its
  arrivals on the mbarrier `storeFull o` before the event, `n = u`. Since a compute thread
  arrives on `storeFull o` once per tile that uses output buffer `o`, this is "the thread's last
  write of `l` in tile `2 u + o`".
* `FinalLast L X c ga l iw aw bw`: count = the thread's `bar.sync 0` before the event, `n = 7`:
  "the thread's last write of `l` in the epilogue".

That such a write exists is `StoreCover.out_last` and `StoreCover.final_last` (from the
contract `StoreCover`: a compute thread has written all its bytes when it arrives, resp. when
it reaches its eighth `bar.sync 0`).

## The theorems

* **D.1** `UnionFacts.leader_read_byte`, `UnionFacts.leader_read`: a read event of the store
  leader of bytes of output buffer `o`, after `u + 1` successful polls of `storeFull o`, returns
  at each byte the byte of the owner's `OutLast` write. The list form takes the content as a
  function `oc` of the offset in the buffer: `bs = (List.range a.size).map fun i => oc (off + i)`,
  under the hypothesis `hoc`: the owner's last write of byte `off + i` in the tile carries
  `oc (off + i)` there. `hoc` speaks of write events of compute threads only.
* **D.2, a tile** `UnionFacts.tile_source_byte`, `UnionFacts.tile_store_write`: for a tensor
  store of the store leader issued in the tile loop (six `bar.sync 0` before it) after `u + 1`
  successful polls of `storeFull o`, whose slot `(x, y, z)` reads byte `l` of output buffer
  `o`: the byte that its write stage puts into global memory is the byte of the owner's
  `OutLast` write of `l`.
* **D.2, the final state** `UnionFacts.final_source_byte`, `UnionFacts.final_store_write`: for
  a tensor store of the store leader with eight `bar.sync 0` before it, whose slot reads byte
  `l`: the byte written is the byte of the owner's `FinalLast` write of `l`.

The `_write` forms are about a performed write `X.MemWrites (.async i (.write (.store x y z)))
dst bytes` and a location `gl` that `dst` covers, and conclude `wbyte dst bytes gl = …`: the
shape of the result fields `outputValue` and `stateValue` (`Proof/Top/Result.lean`).

## How they are proved

A copy store writes at a slot the byte it read there (`TensorStore.writeByte_read`). The byte
read is the library's `ConflictsOrdered.read_byte` on the order of the union region
(`UnionFacts.ordered`): the witness is visible to the read, and every other performed write of
the byte that is visible to the read is the witness or is visible to it.

The three readers are the leader's thread read (D.1), the source read of a tile store and the
source read of a final-state store. By class of the other writer:

* the witness is visible to the reader: `output_before_leader`; `StoreFacts.publish_output`;
  the proxy fence 3774 and the CTA barrier (`publish_of_bar`);
* the owner's earlier writes of the same phase: `same_thread`, for all three;
* the owner's later writes in the tile loop: the reader is visible to them
  (`leader_before_output`; `StoreFacts.release_output`), then asymmetry; for a final-state
  store they come before the witness (`bar_before`);
* the writes of the final state: the reader is visible to them (`bar_before`; the group wait
  and `release_of_bar`), then asymmetry; for a final-state store they are the owner's, and the
  witness is the last of them;
* the load of the initial state: visible to the witness (`init_before_thread`), for all three;
* the loads of the tiles: they write other bytes than an output buffer (`input_output_apart`);
  for a final-state store they are visible to the witness (`load_before_thread`).

"Asymmetry" is `modelCausality_asymm` (visibility at a byte has no cycle) and needs
`SyncGuarded L K X`, as in `ReadBack.lean`; the final-state theorems do not need it. The first
two readers share `UnionFacts.out_others`. For the kernel, `Facts.syncGuarded`
(`ResultGuard.lean`) proves `SyncGuarded` from the protocol contract and consistency.

A read of the store leader with at most five `bar.sync 0` before it (its share of the
conversion loop reads the same addresses) cannot have `u + 1 ≥ 1` successful polls of
`storeFull o` in the kernel; the theorem does not ask for the count of `bar.sync 0` and
excludes that case by asymmetry (such a read would be visible to the witness write through the
CTA barrier).

## Hypotheses beyond the contracts

Consistency; `SyncGuarded L K X` (D.1 and the tile store); `hrmw` (the kernel has no atomic
instruction: `Export.no_rmw`); for the stores `sp.reduce = none` (`Top.tensorStore_form`). -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat} {O : Owners}

/-! ## The last write of a byte by a thread, among the events with a given count -/

/-- Event `iw` of thread `g` is a write event (footprint `aw`, bytes `bw`) that covers byte `l`
and has count `n` (`cnt i` is a count over the thread's events before event `i`), and no later
write event of the thread that covers `l` has count `n`. -/
structure LastWrite (X : Execution) (g : Nat) (l : Loc) (cnt : Nat → Nat) (n iw : Nat)
    (aw : Acc) (bw : List Byte) : Prop where
  /-- The event is a write event. -/
  get : ∃ pcw, X.get (g, iw) = some ⟨pcw, .wr aw bw⟩
  /-- It covers the byte. -/
  covers : aw.Covers l
  /-- Its count is `n`. -/
  count : cnt iw = n
  /-- No later write event of the thread that covers the byte has count `n`. -/
  last : ∀ i' pc' a' b', iw < i' → X.get (g, i') = some ⟨pc', .wr a' b'⟩ → a'.Covers l →
    cnt i' ≠ n

/-- **The last write exists** when the thread has a write of the byte with count `n` before
position `e`, and every write event with count `n` comes before `e`. -/
theorem LastWrite.exists_of {g : Nat} {l : Loc} {cnt : Nat → Nat} {n e : Nat}
    (h : ∃ i < e, ∃ pcw aw bw, X.get (g, i) = some ⟨pcw, .wr aw bw⟩ ∧ aw.Covers l ∧ cnt i = n)
    (hbound : ∀ i pc a b, X.get (g, i) = some ⟨pc, .wr a b⟩ → cnt i = n → i < e) :
    ∃ iw aw bw, LastWrite X g l cnt n iw aw bw := by
  obtain ⟨iw, -, ⟨pcw, aw, bw, hget, hcov, hcnt⟩, hlast⟩ :=
    exists_last (P := fun i => ∃ pcw aw bw, X.get (g, i) = some ⟨pcw, .wr aw bw⟩ ∧
      aw.Covers l ∧ cnt i = n) h
  exact ⟨iw, aw, bw, ⟨pcw, hget⟩, hcov, hcnt, fun i' pc' a' b' hi' hg' hc' hn' =>
    hlast i' hi' (hbound i' pc' a' b' hg' hn') ⟨pc', a', b', hg', hc', hn'⟩⟩

/-- **The last write of byte `l` by compute thread `ga` of block `c` in the tile that is use
`u` of output buffer `o`**: a write event that covers `l`, with `u` arrivals of the thread on
`storeFull o` before it, and no later write event of the thread that covers `l` has `u` arrivals
before it. -/
def OutLast (L : Launch) (X : Execution) (c : Nat) (o : Fin 2) (ga : Fin 128) (u : Nat)
    (l : Loc) (iw : Nat) (aw : Acc) (bw : List Byte) : Prop :=
  LastWrite X (computeThread L c ga) l
    (fun i => arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c ga)).take i)) u iw
    aw bw

/-- **The last write of byte `l` by compute thread `ga` of block `c` in the epilogue**: a write
event that covers `l`, with seven `bar.sync 0` of the thread before it, and no later write event
of the thread that covers `l` has seven before it. -/
def FinalLast (L : Launch) (X : Execution) (c : Nat) (ga : Fin 128) (l : Loc) (iw : Nat)
    (aw : Acc) (bw : List Byte) : Prop :=
  LastWrite X (computeThread L c ga) l (fun i => bar0Before X (computeThread L c ga, i)) 7 iw
    aw bw

/-- Byte `off` of the output buffer of store stage `o` of block `c`. -/
def outByte (L : Launch) (c o off : Nat) : Loc :=
  ⟨.shared, c, L.sharedBase + (86912 + 4096 * o + off)⟩

theorem outByte_in {c o off : Nat} (h : off < 4096) : InOutput L c o (outByte L c o off) := by
  simp only [InOutput, InShared, outByte]
  refine ⟨trivial, trivial, ?_, ?_⟩ <;> omega

/-- The store leader is a launched thread of its block, and no compute thread. -/
theorem storeLeader_lt (hb : L.block = 192) {c : Nat} (hc : c < L.grid) :
    storeLeader L c < L.threads := thr_lt hb hc (by decide)

theorem storeLeader_div (hb : L.block = 192) {c : Nat} : storeLeader L c / L.block = c :=
  thr_div hb (by decide)

theorem storeLeader_ne_compute {c : Nat} (a : Fin 128) :
    storeLeader L c ≠ computeThread L c a := by
  unfold computeThread storeLeader thr
  have := a.isLt
  omega

/-! ## The witnesses exist -/

section witness
variable (C : StoreCover L X O) (hSt : StoreFacts L X) (hI : InitFacts L X)
  (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X) (hb : L.block = 192)
include C hB hX hb

include hSt hI hN in
/-- **The owner's last write of a byte of output buffer `o` in the tile exists** once the store
leader has `u + 1` successful polls of `storeFull o`: the poll observed the owner's arrival
with `u` earlier ones (`StoreFacts.full_handoff`), before which the owner wrote the byte
(`StoreCover.out_cover`). -/
theorem StoreCover.out_last {c : Nat} (hc : c < L.grid) (o : Fin 2) {k u : Nat}
    (hpolls : u + 1 ≤ okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k))
    {l : Loc} (hlo : InOutput L c o.val l) :
    ∃ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out l = ga.val ∧ OutLast L X c o ga u l iw aw bw := by
  obtain ⟨j, pcj, par, acq, sc, -, hw, hq⟩ := MbarRing.UnitHandoff.exists_poll hpolls
  obtain ⟨xa, hxa, hs⟩ := hSt.full_handoff hI hB hN hX hb hc o (storeLeader L c) j pcj par
    acq sc u ⟨0, rfl⟩ hw (by rw [Nat.add_zero]; exact hq)
    (computeThread L c ⟨O.out l, C.out_lt o.isLt hlo⟩) ⟨_, rfl⟩
  obtain ⟨rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ := id hs
  obtain ⟨i0, pcw, aw0, bs0, hi0, hwget, hwcov, harr⟩ :=
    C.out_cover ⟨O.out l, C.out_lt o.isLt hlo⟩ o hxget hlo rfl
  obtain ⟨iw, aw, bw, hlast⟩ := LastWrite.exists_of (X := X)
    (g := computeThread L c ⟨O.out l, C.out_lt o.isLt hlo⟩) (l := l)
    (cnt := fun i => arrivals ((Bar.storeFull o).loc L c)
      ((X.tr (computeThread L c ⟨O.out l, C.out_lt o.isLt hlo⟩)).take i)) (n := u) (e := xa)
    ⟨i0, hi0, pcw, aw0, bs0, hwget, hwcov, harr.trans hxa⟩ (by
      intro i pc a b hget hcnt
      have hle : i ≤ xa := MbarRing.arrival_index_ge hxget
        (by simp [arrivesOn, sourceArrive]) hxa hcnt.le
      rcases Nat.lt_or_eq_of_le hle with h | h
      · exact h
      · subst h
        rw [hget] at hxget
        cases hxget)
  exact ⟨⟨O.out l, C.out_lt o.isLt hlo⟩, iw, aw, bw, rfl, hlast⟩

/-- **The owner's last write of a byte of the union region in the epilogue exists** once the
store leader has passed its eighth `bar.sync 0`: the owner has made its eighth
(`BarFacts.peer_bar0`), before which it wrote the byte (`StoreCover.final_cover`). -/
theorem StoreCover.final_last {c : Nat} (hc : c < L.grid) {k : Nat}
    (hk : k < (X.tr (storeLeader L c)).length)
    (h8 : 8 ≤ bar0Before X (storeLeader L c, k)) {l : Loc} (hl : InUnion L c l) :
    ∃ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.final l = ga.val ∧ FinalLast L X c ga l iw aw bw := by
  have hlt := computeThread_lt hb hc ⟨O.final l, C.final_lt hl⟩
  have hdiv : computeThread L c ⟨O.final l, C.final_lt hl⟩ / L.block = c :=
    computeThread_div hb _
  obtain ⟨e, pce, md, he, heq⟩ := hB.peer_bar0 hX hb hlt
    (hdiv.trans (storeLeader_div hb).symm) hk (show 7 + 1 ≤ _ from h8)
  obtain ⟨i0, pcw, aw0, bs0, hi0, hwget, hwcov, hb7⟩ :=
    C.final_cover ⟨O.final l, C.final_lt hl⟩ he heq hl rfl
  obtain ⟨iw, aw, bw, hlast⟩ := LastWrite.exists_of (X := X)
    (g := computeThread L c ⟨O.final l, C.final_lt hl⟩) (l := l)
    (cnt := fun i => bar0Before X (computeThread L c ⟨O.final l, C.final_lt hl⟩, i)) (n := 7)
    (e := e) ⟨i0, hi0, pcw, aw0, bs0, hwget, hwcov, hb7⟩ (by
      intro i pc a b hget hcnt
      exact before_bar he hget rfl (by rw [hcnt, heq]))
  exact ⟨⟨O.final l, C.final_lt hl⟩, iw, aw, bw, rfl, hlast⟩

end witness

/-! ## The other writers of a byte of an output buffer -/

/-- **Every performed write of a byte of output buffer `o` that is visible to a reader `e` is
the owner's last write of the tile or is visible to it**, for a reader `e` (the store leader's
read event or the source read of its tensor store) that is visible to the owner's writes of the
later tiles (`hlater`) and to the writes of the final state (`hfinal`). The writers of the byte
are the owner in the tile loop, the compute threads in the epilogue, and one load of the
initial state. -/
theorem UnionFacts.out_others (U : UnionFacts L X T O) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (hg : SyncGuarded L K X)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {c : Nat} (hc : c < L.grid)
    {o : Fin 2} {l : Loc} (hlo : InOutput L c o.val l) {ga : Fin 128} {u iw : Nat} {aw : Acc}
    {bw : List Byte} (hown : O.out l = ga.val) (hlast : OutLast L X c o ga u l iw aw bw)
    {e : Ref}
    (hlater : ∀ i1, i1 < (X.tr (computeThread L c ga)).length →
      u + 1 + 1 ≤ okPolls ((Bar.storeEmpty o).loc L c) ((X.tr (computeThread L c ga)).take i1) →
      modelCausality L X l e (.thread (computeThread L c ga, i1)))
    (hfinal : ∀ g1 i1, g1 < L.threads → g1 / L.block = c → i1 < (X.tr g1).length →
      bar0Before X (g1, i1) = 7 → modelCausality L X l e (.thread (g1, i1)))
    {w' : Ref} {dst' : Acc} {bytes : List Byte} (hw' : X.MemWrites w' dst' bytes)
    (hcov' : dst'.Covers l) (hvis : modelCausality L X l w' e) :
    w' = .thread (computeThread L c ga, iw) ∨
      modelCausality L X l w' (.thread (computeThread L c ga, iw)) := by
  have hl' : InUnion L c l := hlo.union o.isLt
  obtain ⟨⟨pcw, hwget⟩, hcov, harr, hno⟩ := hlast
  have haccw : X.Access (computeThread L c ga, iw) aw true :=
    .inr (.inl ⟨bw, ⟨pcw, hwget⟩, rfl⟩)
  have hkw : iw < (X.tr (computeThread L c ga)).length := (List.getElem?_eq_some_iff.mp hwget).1
  obtain ⟨-, hpollw, -⟩ := U.thread haccw hcov hl'
  rcases intent_cases hN hw'.intent hcov' hl' with ⟨g1, i1, rfl, hacc1⟩ |
    ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, -, hiss1, hwl1⟩ |
    ⟨_, _, _, _, _, _, _, _, -, hfalse, -⟩
  · -- a thread write
    obtain ⟨hgc1, -, hcls1⟩ := U.thread hacc1 hcov' hl'
    obtain ⟨ev1, hev1, -, -⟩ := access_kind hacc1
    have hg1 := Frame.lt_of_get hX hev1
    have hk1 : i1 < (X.tr g1).length := (List.getElem?_eq_some_iff.mp hev1).1
    have asym : modelCausality L X l e (.thread (g1, i1)) → False := fun h =>
      modelCausality_asymm hX.effectValidity hX.object
        (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk
        (show X.RefPresent (.thread (g1, i1)) from ⟨_, hev1⟩) h hvis
    rcases hcls1 with ⟨hw1, -⟩ | ⟨_, _, _, hw1, -⟩ | ⟨a1, o1, hg1', hw1, hb1, hl1, hgt1, hown1⟩ |
      ⟨_, _, hw1, -⟩ | ⟨a1, hg1', hw1, hb1, hown1⟩
    · cases hw1
    · cases hw1
    · -- a write of the tile loop: the owner's
      obtain rfl : o = o1 := Fin.ext (output_stage_unique hlo hl1)
      obtain rfl : a1 = ga := Fin.ext (hown1.symm.trans hown)
      subst hg1'
      obtain ⟨pc1, hwr1⟩ :
          ∃ pc1, X.get (computeThread L c a1, i1) = some ⟨pc1, .wr dst' bytes⟩ := by
        rcases hw' with h | ⟨old, pc1, h⟩
        · exact h
        · exact (hrmw _ _ _ _ _ h).elim
      rcases Nat.lt_trichotomy i1 iw with h | h | h
      · exact .inr (same_thread hacc1 haccw h hcov' hcov)
      · exact .inl (by rw [h])
      · -- a later write of the owner is in a later tile: the reader is visible to it
        have hmono := countP_take_mono (arrivesOn ((Bar.storeFull o).loc L c))
          (X.tr (computeThread L c a1)) h.le
        have hne := hno i1 pc1 dst' bytes h hwr1 hcov'
        refine (asym (hlater i1 hk1 ?_)).elim
        have hne' : arrivals ((Bar.storeFull o).loc L c)
            ((X.tr (computeThread L c a1)).take i1) ≠ u := hne
        unfold arrivals at harr hne' hgt1
        omega
    · cases hw1
    · exact (asym (hfinal g1 i1 hg1 hgc1 hk1 hb1)).elim
  · -- a byte write of a load: of the initial state, which the owner's poll observed
    have hcov1 := load_covers hiss1 hwl1
    have hg1 := Frame.lt_of_get hX hiss1
    rcases U.load hiss1 hwl1 hl' with ⟨hm1, -⟩ | ⟨s1, hm1, hbar1, hl1, -⟩
    · obtain ⟨rfl, -, -⟩ := hS.issue hg1 hiss1 hm1
      obtain ⟨jj, pcp, par, acq, sc, hjk, hwp, -⟩ :=
        MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpollw
      exact .inr (init_before_thread hS hI hB hN hX hb hc hiss1 hm1 hwp hjk hkw hcov1)
    · exact (input_output_apart s1.isLt hl1 hlo).elim
  · cases hfalse

/-! ## D.1: the store leader's reads of an output buffer -/

/-- **A read of the store leader of a byte of an output buffer returns the byte of the owner's
last write of the tile.** The read is event `k` of the store leader of block `c`, with `u + 1`
successful polls of `storeFull o` before it; the witness is the `OutLast` write of the byte by
its owner `ga`. -/
theorem UnionFacts.leader_read_byte (U : UnionFacts L X T O) (hF : LifeFacts L X T)
    (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X)
    (hB : BarFacts L X T) (hN : NoEvents K X) (hX : Consistent L K A mem0 X)
    (hb : L.block = 192) (hg : SyncGuarded L K X)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {c : Nat} (hc : c < L.grid)
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hrd : X.get (storeLeader L c, k) = some ⟨pc, .rd a bs⟩) {j : Nat} (hj : j < a.size)
    {o : Fin 2} (hl : InOutput L c o.val (a.loc.at j)) {ga : Fin 128} {u iw : Nat} {aw : Acc}
    {bw : List Byte} (hown : O.out (a.loc.at j) = ga.val)
    (hlast : OutLast L X c o ga u (a.loc.at j) iw aw bw)
    (hpolls : okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k) = u + 1) :
    bs[j]? = some (wbyte aw bw (a.loc.at j)) := by
  have hl' : InUnion L c (a.loc.at j) := hl.union o.isLt
  have hacc : X.Access (storeLeader L c, k) a false := .inl ⟨bs, ⟨pc, hrd⟩, rfl⟩
  have ha : a.Covers (a.loc.at j) := ⟨rfl, rfl, Nat.le_add_right _ _, by
    simp only [Loc.at]
    omega⟩
  have hk : k < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp hrd).1
  have hsl := storeLeader_lt hb hc
  have hsdiv : storeLeader L c / L.block = c := storeLeader_div hb
  have hgl := computeThread_lt hb hc ga
  have hgdiv : computeThread L c ga / L.block = c := computeThread_div hb ga
  obtain ⟨⟨pcw, hwget⟩, hcov, harr, -⟩ := id hlast
  have haccw : X.Access (computeThread L c ga, iw) aw true :=
    .inr (.inl ⟨bw, ⟨pcw, hwget⟩, rfl⟩)
  have hkw : iw < (X.tr (computeThread L c ga)).length := (List.getElem?_eq_some_iff.mp hwget).1
  have hv : modelCausality L X (a.loc.at j) (.thread (computeThread L c ga, iw))
      (.thread (storeLeader L c, k)) :=
    output_before_leader hSt hI hB hN hX hb hc o ga (Nat.le_of_eq harr) hk (by omega)
  -- the read is of the class `leader`
  obtain ⟨hbarR, hgateR⟩ : bar0Before X (storeLeader L c, k) = 6 ∧
      arrivals ((Bar.storeEmpty o).loc L c) ((X.tr (storeLeader L c)).take k) + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k) := by
    obtain ⟨-, -, hcls⟩ := U.thread hacc ha hl'
    rcases hcls with ⟨-, hb2⟩ | ⟨a2, s2, hg2, -⟩ | ⟨_, _, _, hw2, -⟩ |
      ⟨o2, -, -, hb2, hl2, hgt2⟩ | ⟨_, _, hw2, -⟩
    · -- an early read would be visible to the witness write, which is visible to the read
      have hbw : 6 ≤ bar0Before X (computeThread L c ga, iw) := by
        obtain ⟨-, -, hclsw⟩ := U.thread haccw hcov hl'
        rcases hclsw with ⟨hw3, -⟩ | ⟨_, _, _, hw3, -⟩ | ⟨_, _, _, _, hb3, -⟩ |
          ⟨_, _, hw3, -⟩ | ⟨_, _, _, hb3, -⟩
        · cases hw3
        · cases hw3
        · omega
        · cases hw3
        · omega
      exact (modelCausality_asymm hX.effectValidity hX.object
        (DepStepAcyclic.of_dependency hX.dependency) hg hX.guardOk
        (show X.RefPresent (.thread (storeLeader L c, k)) from ⟨_, hrd⟩) hv
        (bar_before hB hX hb ⟨hsl, hgl, hsdiv.trans hgdiv.symm⟩ hkw
          (by rw [bar0UpTo_of_access hacc]; omega))).elim
    · exact (storeLeader_ne_compute a2 hg2).elim
    · cases hw2
    · obtain rfl : o = o2 := Fin.ext (output_stage_unique hl hl2)
      exact ⟨hb2, hgt2⟩
    · cases hw2
  have he : X.MemReads (.thread (storeLeader L c, k)) a bs := .inl ⟨pc, hrd⟩
  exact ConflictsOrdered.read_byte hX (U.ordered hF hLd hSt hS hI hB hN hX hb c) he hj
    (by
      rintro i' acc old new ⟨h1, pc', h2⟩
      cases h1
      rw [hrd] at h2
      cases h2)
    hl' (w := .thread (computeThread L c ga, iw)) (.inl ⟨pcw, hwget⟩) hcov hv
    (fun w' dst' bytes hw' hcov' hvis =>
      U.out_others hS hI hB hN hX hb hg hrmw hc hl hown hlast
        (fun i1 hi1 hp => leader_before_output hSt hI hB hN hX hb hc o ga (j := u)
          (by omega) hi1 hp)
        (fun g1 i1 hg1 hgc1 hk1 hb1 => bar_before hB hX hb ⟨hsl, hg1, hsdiv.trans hgc1.symm⟩
          hk1 (by rw [bar0UpTo_of_access hacc]; omega))
        hw' hcov' hvis)

/-- **D.1. A read of the store leader of an output buffer returns the content of the tile.**
Event `k` of the store leader of block `c` reads `a.size` bytes at offset `off` of output
buffer `o`, after `u + 1` successful polls of `storeFull o` (so in tile `2 u + o`). `oc` is the
content of the buffer in that tile. `hoc` is the content of the compute threads' writes, for
the bytes of the read: the owner's last write of the byte in the tile (`OutLast`) carries
`oc` of the byte's offset there. That such a write exists is derived (`StoreCover.out_last`). -/
theorem UnionFacts.leader_read (U : UnionFacts L X T O) (C : StoreCover L X O)
    (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (hg : SyncGuarded L K X)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {c : Nat} (hc : c < L.grid)
    {k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (hrd : X.get (storeLeader L c, k) = some ⟨pc, .rd a bs⟩) (o : Fin 2) (u off : Nat)
    (oc : Nat → Option Byte)
    (hpolls : okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take k) = u + 1)
    (hloc : a.loc = outByte L c o.val off) (hsz : off + a.size ≤ 4096)
    (hoc : ∀ i < a.size, ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out (outByte L c o.val (off + i)) = ga.val →
      OutLast L X c o ga u (outByte L c o.val (off + i)) iw aw bw →
        wbyte aw bw (outByte L c o.val (off + i)) = oc (off + i)) :
    bs = (List.range a.size).map fun i => oc (off + i) := by
  have he : X.MemReads (.thread (storeLeader L c, k)) a bs := .inl ⟨pc, hrd⟩
  have hlen : bs.length = a.size := (hX.rf _ a bs he).1
  apply List.ext_getElem?
  intro i'
  by_cases hi' : i' < a.size
  · have hlocj : a.loc.at i' = outByte L c o.val (off + i') := by
      rw [hloc]
      simp only [outByte, Loc.at, Loc.mk.injEq, true_and]
      omega
    have hin : InOutput L c o.val (a.loc.at i') := by
      rw [hlocj]
      exact outByte_in (by omega)
    obtain ⟨ga, iw, aw, bw, hown, hlast⟩ :=
      C.out_last hSt hI hB hN hX hb hc o (Nat.le_of_eq hpolls.symm) hin
    rw [U.leader_read_byte hF hLd hSt hS hI hB hN hX hb hg hrmw hc hrd hi' hin hown hlast hpolls,
      hlocj, hoc i' hi' ga iw aw bw (hlocj ▸ hown) (hlocj ▸ hlast)]
    simp [hi']
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-! ## D.2: the byte a tensor store writes to global memory -/

/-- The record of an issued tensor store has the specification of the issue event. -/
theorem store_spec (hX : Consistent L K A mem0 X) {i : EvId} {pc al : Nat}
    {sp : TensorStore.Spec} (hiss : X.get i = some ⟨pc, .tensorStore al sp⟩)
    {rec : TensorStore.Observation} (hrec : X.tensorStores i = some rec) : rec.spec = sp := by
  obtain ⟨⟨a', pc', hio⟩, -⟩ := hX.store i rec hrec
  rw [hiss] at hio
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tensorStore.injEq] at hio
  exact hio.2.2.symm

/-- **The byte of a performed write of a tensor store is the byte its source read returned**:
a write stage of a copy store (no reduction) that covers `gl` wrote at `gl` the byte that the
store's record holds as read for the same slot. -/
theorem store_write_read (hX : Consistent L K A mem0 X) {i : EvId} {pc al x y z : Nat}
    {sp : TensorStore.Spec} (hiss : X.get i = some ⟨pc, .tensorStore al sp⟩)
    (hred : sp.reduce = none) {dst : Acc} {bytes : List Byte}
    (hw : X.MemWrites (.async i (.write (.store x y z))) dst bytes) {gl : Loc}
    (hgl : dst.Covers gl) :
    ∃ rec b, X.tensorStores i = some rec ∧ TensorStore.readByte rec x y z = some b ∧
      TensorStore.writeLoc sp x y z = some gl ∧ wbyte dst bytes gl = some b := by
  obtain ⟨rec, addr, b, hrec, -, hwl, hwb, hsz, rfl, -⟩ := hw
  have hspec := store_spec hX hiss hrec
  obtain ⟨-, -, hok⟩ := hX.store i rec hrec
  obtain ⟨hrb, -⟩ := TensorStore.writeByte_read hok (hspec ▸ hred) hwb
  have hloc : dst.loc = gl := covers_one hsz hgl
  refine ⟨rec, b, hrec, hrb, ?_, ?_⟩
  · rw [← hspec, hwl, hloc]
  · simp [wbyte, hloc]

section stores
variable (U : UnionFacts L X T O) (hF : LifeFacts L X T) (hLd : LoadFacts L X)
  (hSt : StoreFacts L X) (hS : StateFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T)
  (hN : NoEvents K X) (hX : Consistent L K A mem0 X) (hb : L.block = 192)
  (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩)
include U hF hLd hSt hS hI hB hN hX hb hrmw

/-- **The source read of a tensor store of a tile returns the byte of the owner's last write of
the tile.** The store is event `i` of the store leader of block `c`, issued in the tile loop
(six `bar.sync 0` before it) after `u + 1` successful polls of `storeFull o`; its slot
`(x, y, z)` reads byte `l` of output buffer `o`; `b` is the byte its record holds as read. -/
theorem UnionFacts.tile_source_byte (hg : SyncGuarded L K X) {c : Nat} (hc : c < L.grid)
    {i pc al x y z : Nat} {sp : TensorStore.Spec}
    (hiss : X.get (storeLeader L c, i) = some ⟨pc, .tensorStore al sp⟩)
    (hbar : bar0Before X (storeLeader L c, i) = 6) {l : Loc}
    (hrl : TensorStore.readLoc sp x y z = some l) {o : Fin 2} (hlo : InOutput L c o.val l)
    {ga : Fin 128} {u iw : Nat} {aw : Acc} {bw : List Byte} (hown : O.out l = ga.val)
    (hlast : OutLast L X c o ga u l iw aw bw)
    (hpolls : okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) = u + 1)
    {rec : TensorStore.Observation} (hrec : X.tensorStores (storeLeader L c, i) = some rec)
    {b : Byte} (hrb : TensorStore.readByte rec x y z = some b) : some b = wbyte aw bw l := by
  have hl' : InUnion L c l := hlo.union o.isLt
  have hcovS := store_covers hiss hrl
  have his : i < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp hiss).1
  have hsl := storeLeader_lt hb hc
  have hsdiv : storeLeader L c / L.block = c := storeLeader_div hb
  obtain ⟨⟨pcw, hwget⟩, hcov, harr, -⟩ := id hlast
  have haccw : X.Access (computeThread L c ga, iw) aw true :=
    .inr (.inl ⟨bw, ⟨pcw, hwget⟩, rfl⟩)
  -- the store is of the class `tile`
  have hgate : arrivals ((Bar.storeEmpty o).loc L c) ((X.tr (storeLeader L c)).take i) + 1 ≤
      okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) := by
    obtain ⟨-, -, hcs⟩ := U.store hiss hrl hl'
    rcases hcs with ⟨o2, -, hlo2, hgate⟩ | hbar8
    · obtain rfl : o = o2 := Fin.ext (output_stage_unique hlo hlo2)
      exact hgate
    · omega
  have hv : modelCausality L X l (.thread (computeThread L c ga, iw))
      (.async (storeLeader L c, i) (.read (.store x y z))) :=
    hSt.publish_output hI hB hN hX hb hc o ga haccw hcov hlo (Nat.le_of_eq harr) his
      (by omega) hcovS
  have hspec := store_spec hX hiss hrec
  obtain ⟨⟨addr, hissue⟩, -⟩ := hX.store _ rec hrec
  have hm : X.MemReads (.async (storeLeader L c, i) (.read (.store x y z)))
      ⟨l, 1, false, false, .cta, 0, false⟩ [some b] :=
    ⟨rec, addr, b, hrec, hissue, hspec ▸ hrl, hrb, rfl, rfl⟩
  have hl0 : (⟨l, 1, false, false, .cta, 0, false⟩ : Acc).loc.at 0 = l := by simp [Loc.at]
  have hres := ConflictsOrdered.read_byte hX (U.ordered hF hLd hSt hS hI hB hN hX hb c) hm
    Nat.one_pos
    (by
      rintro i' acc old new ⟨h1, -⟩
      cases h1)
    (by rw [hl0]; exact hl') (w := .thread (computeThread L c ga, iw)) (.inl ⟨pcw, hwget⟩)
    (by rw [hl0]; exact hcov)
    (by rw [hl0]; exact hv)
    (by
      rw [hl0]
      intro w' dst' bytes hw' hcov' hvis
      refine U.out_others hS hI hB hN hX hb hg hrmw hc hlo hown hlast
        (fun i1 hi1 hp => hSt.release_output hI hB hN hX hb hc o ga hiss hrl hlo (j := u)
          (by omega) hi1 hp hcovS)
        (fun g1 i1 hg1 hgc1 hk1 hb1 => ?_) hw' hcov' hvis
      -- a write of the final state: the leader's group wait before its seventh `bar.sync 0`
      obtain ⟨e, pce, md, he, heq⟩ := hB.peer_bar0 hX hb hsl (hsdiv.trans hgc1.symm) hk1
        (show 6 + 1 ≤ bar0Before X (g1, i1) by omega)
      have hise : i < e := before_bar he hiss rfl (by omega)
      obtain ⟨w, hkw, hwe, hwait⟩ := U.store_bar_wait hiss hise he
      have hel : e < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp he).1
      refine release_of_bar hX (hB.handoff0 hX hb) hwait (by omega)
        ⟨hsl, hg1, hsdiv.trans hgc1.symm⟩ hk1 ?_ hcovS
      have hmn := countP_take_mono (Execution.isBarId 0) (X.tr (storeLeader L c))
        (show w + 1 ≤ e from hwe)
      unfold bar0UpTo
      unfold bar0Before at heq hb1 ⊢
      simp only at heq hb1 ⊢
      omega)
  rw [hl0] at hres
  simpa using hres

omit hrmw in
/-- **The source read of a tensor store of the final state returns the byte of the owner's last
write of the epilogue.** The store is event `i` of the store leader of block `c`, with eight
`bar.sync 0` before it; its slot `(x, y, z)` reads byte `l` of the union region. -/
theorem UnionFacts.final_source_byte (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩)
    {c : Nat} (hc : c < L.grid)
    {i pc al x y z : Nat} {sp : TensorStore.Spec}
    (hiss : X.get (storeLeader L c, i) = some ⟨pc, .tensorStore al sp⟩)
    (hbar : bar0Before X (storeLeader L c, i) = 8) {l : Loc}
    (hrl : TensorStore.readLoc sp x y z = some l) (hl : InUnion L c l)
    {ga : Fin 128} {iw : Nat} {aw : Acc} {bw : List Byte} (hown : O.final l = ga.val)
    (hlast : FinalLast L X c ga l iw aw bw)
    {rec : TensorStore.Observation} (hrec : X.tensorStores (storeLeader L c, i) = some rec)
    {b : Byte} (hrb : TensorStore.readByte rec x y z = some b) : some b = wbyte aw bw l := by
  have hcovS := store_covers hiss hrl
  have his : i < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp hiss).1
  have hsl := storeLeader_lt hb hc
  have hsdiv : storeLeader L c / L.block = c := storeLeader_div hb
  have hgl := computeThread_lt hb hc ga
  have hgdiv : computeThread L c ga / L.block = c := computeThread_div hb ga
  obtain ⟨⟨pcw, hwget⟩, hcov, hb7, hno⟩ := id hlast
  have hb7' : bar0Before X (computeThread L c ga, iw) = 7 := hb7
  have haccw : X.Access (computeThread L c ga, iw) aw true :=
    .inr (.inl ⟨bw, ⟨pcw, hwget⟩, rfl⟩)
  have hkw : iw < (X.tr (computeThread L c ga)).length := (List.getElem?_eq_some_iff.mp hwget).1
  obtain ⟨-, hpollw, -⟩ := U.thread haccw hcov hl
  -- the witness is published by its thread's fence 3774 and the CTA barrier
  have hv : modelCausality L X l (.thread (computeThread L c ga, iw))
      (.async (storeLeader L c, i) (.read (.store x y z))) := by
    obtain ⟨f, pcf, hif, hfget, hlt'⟩ := U.fence_before hB hX hb haccw (.inr rfl) hb7'.le
      (hgdiv.trans hsdiv.symm) his (by omega)
    exact publish_of_bar (hB.handoff0 hX hb) hif hfget ⟨hgl, hsl, hgdiv.trans hsdiv.symm⟩ his
      hlt' hl.1 (hl.2.1.trans hgdiv.symm) hcovS
  have hspec := store_spec hX hiss hrec
  obtain ⟨⟨addr, hissue⟩, -⟩ := hX.store _ rec hrec
  have hm : X.MemReads (.async (storeLeader L c, i) (.read (.store x y z)))
      ⟨l, 1, false, false, .cta, 0, false⟩ [some b] :=
    ⟨rec, addr, b, hrec, hissue, hspec ▸ hrl, hrb, rfl, rfl⟩
  have hl0 : (⟨l, 1, false, false, .cta, 0, false⟩ : Acc).loc.at 0 = l := by simp [Loc.at]
  have hres := ConflictsOrdered.read_byte hX (U.ordered hF hLd hSt hS hI hB hN hX hb c) hm
    Nat.one_pos
    (by
      rintro i' acc old new ⟨h1, -⟩
      cases h1)
    (by rw [hl0]; exact hl) (w := .thread (computeThread L c ga, iw)) (.inl ⟨pcw, hwget⟩)
    (by rw [hl0]; exact hcov)
    (by rw [hl0]; exact hv)
    (by
      rw [hl0]
      intro w' dst' bytes hw' hcov' _
      rcases intent_cases hN hw'.intent hcov' hl with ⟨g1, i1, rfl, hacc1⟩ |
        ⟨g1, i1, pc1, al1, sp1, x1, y1, z1, rfl, -, hiss1, hwl1⟩ |
        ⟨_, _, _, _, _, _, _, _, -, hfalse, -⟩
      · -- a thread write: of a tile (before the epilogue) or the owner's in the epilogue
        obtain ⟨hgc1, -, hcls1⟩ := U.thread hacc1 hcov' hl
        obtain ⟨ev1, hev1, -, -⟩ := access_kind hacc1
        have hg1 := Frame.lt_of_get hX hev1
        rcases hcls1 with ⟨hw1, -⟩ | ⟨_, _, _, hw1, -⟩ | ⟨_, _, _, _, hb1, -⟩ |
          ⟨_, _, hw1, -⟩ | ⟨a1, hg1', hw1, hb1, hown1⟩
        · cases hw1
        · cases hw1
        · exact .inr (bar_before hB hX hb ⟨hg1, hgl, hgc1.trans hgdiv.symm⟩ hkw
            (by rw [bar0UpTo_of_access hacc1]; omega))
        · cases hw1
        · obtain rfl : a1 = ga := Fin.ext (hown1.symm.trans hown)
          subst hg1'
          obtain ⟨pc1, hwr1⟩ :
              ∃ pc1, X.get (computeThread L c a1, i1) = some ⟨pc1, .wr dst' bytes⟩ := by
            rcases hw' with h | ⟨old, pc1, h⟩
            · exact h
            · exact (hrmw _ _ _ _ _ h).elim
          rcases Nat.lt_trichotomy i1 iw with h | h | h
          · exact .inr (same_thread hacc1 haccw h hcov' hcov)
          · exact .inl (by rw [h])
          · exact (hno i1 pc1 dst' bytes h hwr1 hcov' hb1).elim
      · -- a byte write of a load: the owner polled for it before the epilogue
        have hcov1 := load_covers hiss1 hwl1
        have hg1 := Frame.lt_of_get hX hiss1
        rcases U.load hiss1 hwl1 hl with ⟨hm1, -⟩ | ⟨s1, hm1, hbar1, hl1, -⟩
        · obtain ⟨rfl, -, -⟩ := hS.issue hg1 hiss1 hm1
          obtain ⟨jj, pcp, par, acq, sc, hjk, hwp, -⟩ :=
            MbarRing.UnitHandoff.exists_poll (X := X) (c := 0) hpollw
          exact .inr (init_before_thread hS hI hB hN hX hb hc hiss1 hm1 hwp hjk hkw hcov1)
        · obtain ⟨rfl, -, -, -⟩ := hLd.full_issue hg1 hiss1 hm1
          have hp := U.polled s1 ga hc hwget (by omega)
          have h1 := hF.full_issues s1 hc
          have h2 := issues_lt hiss1 hm1
          exact .inr (load_before_thread hLd hI hB hN hX hb hc s1 hiss1 hm1 ga hkw (by omega)
            hcov1)
      · cases hfalse)
  rw [hl0] at hres
  simpa using hres

end stores

/-- **D.2, a tile. The byte a tensor store of a tile writes to global memory.** The store is
event `i` of the store leader of block `c`, a copy store (`hred`) issued in the tile loop
(`hbar`) after `u + 1` successful polls of `storeFull o` (so in tile `2 u + o`); its slot
`(x, y, z)` reads byte `off` of output buffer `o` (`hrl`). `oc` is the content of that byte in
the tile; `hoc`: the owner's last write of the byte in the tile carries `oc`. Then a performed
write of the slot that covers `gl` wrote `oc` there, and `gl` is the slot's global location. -/
theorem UnionFacts.tile_store_write (U : UnionFacts L X T O) (C : StoreCover L X O)
    (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192) (hg : SyncGuarded L K X)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {c : Nat} (hc : c < L.grid)
    {i pc al x y z : Nat} {sp : TensorStore.Spec}
    (hiss : X.get (storeLeader L c, i) = some ⟨pc, .tensorStore al sp⟩)
    (hred : sp.reduce = none) (hbar : bar0Before X (storeLeader L c, i) = 6) (o : Fin 2)
    (u off : Nat) (hoff : off < 4096)
    (hrl : TensorStore.readLoc sp x y z = some (outByte L c o.val off))
    (hpolls : okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) = u + 1)
    (oc : Option Byte)
    (hoc : ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte),
      O.out (outByte L c o.val off) = ga.val →
      OutLast L X c o ga u (outByte L c o.val off) iw aw bw →
        wbyte aw bw (outByte L c o.val off) = oc)
    {dst : Acc} {bytes : List Byte}
    (hw : X.MemWrites (.async (storeLeader L c, i) (.write (.store x y z))) dst bytes)
    {gl : Loc} (hgl : dst.Covers gl) :
    wbyte dst bytes gl = oc ∧ TensorStore.writeLoc sp x y z = some gl := by
  obtain ⟨rec, b, hrec, hrb, hwl, hwb⟩ := store_write_read hX hiss hred hw hgl
  have hlo : InOutput L c o.val (outByte L c o.val off) := outByte_in hoff
  obtain ⟨ga, iw, aw, bw, hown, hlast⟩ :=
    C.out_last hSt hI hB hN hX hb hc o (Nat.le_of_eq hpolls.symm) hlo
  have h := U.tile_source_byte hF hLd hSt hS hI hB hN hX hb hrmw hg hc hiss hbar hrl hlo hown
    hlast hpolls hrec hrb
  exact ⟨by rw [hwb, h, hoc ga iw aw bw hown hlast], hwl⟩

/-- **D.2, the final state. The byte a tensor store of the final state writes to global
memory.** The store is event `i` of the store leader of block `c`, a copy store with eight
`bar.sync 0` before it; its slot `(x, y, z)` reads byte `l`. `fc` is the content of that byte
of the FP32 state buffer after the epilogue; `hfc`: the owner's last write of `l` in the
epilogue carries `fc`. Then a performed write of the slot that covers `gl` wrote `fc` there. -/
theorem UnionFacts.final_store_write (U : UnionFacts L X T O) (C : StoreCover L X O)
    (hF : LifeFacts L X T) (hLd : LoadFacts L X) (hSt : StoreFacts L X) (hS : StateFacts L X)
    (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {c : Nat} (hc : c < L.grid)
    {i pc al x y z : Nat} {sp : TensorStore.Spec}
    (hiss : X.get (storeLeader L c, i) = some ⟨pc, .tensorStore al sp⟩)
    (hred : sp.reduce = none) (hbar : bar0Before X (storeLeader L c, i) = 8) {l : Loc}
    (hrl : TensorStore.readLoc sp x y z = some l) (fc : Option Byte)
    (hfc : ∀ (ga : Fin 128) (iw : Nat) (aw : Acc) (bw : List Byte), O.final l = ga.val →
      FinalLast L X c ga l iw aw bw → wbyte aw bw l = fc)
    {dst : Acc} {bytes : List Byte}
    (hw : X.MemWrites (.async (storeLeader L c, i) (.write (.store x y z))) dst bytes)
    {gl : Loc} (hgl : dst.Covers gl) :
    wbyte dst bytes gl = fc ∧ TensorStore.writeLoc sp x y z = some gl := by
  obtain ⟨rec, b, hrec, hrb, hwl, hwb⟩ := store_write_read hX hiss hred hw hgl
  have hl : InUnion L c l := by
    have := C.store_in hiss hrl
    rwa [storeLeader_div hb] at this
  have his : i < (X.tr (storeLeader L c)).length := (List.getElem?_eq_some_iff.mp hiss).1
  obtain ⟨ga, iw, aw, bw, hown, hlast⟩ := C.final_last hB hX hb hc his (by omega) hl
  have h := U.final_source_byte hF hLd hSt hS hI hB hN hX hb hrmw hc hiss hbar hrl hl hown
    hlast hrec hrb
  exact ⟨by rw [hwb, h, hfc ga iw aw bw hown hlast], hwl⟩

end PTX.Kernels.FlashKdaFwd.Protocol
