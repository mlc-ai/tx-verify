-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Protocol.UnionClass
public import Lemmas.Step.StoreDone

@[expose] public section

/-! # The source bytes of the tensor stores

The progress premise `storeSources` (`Proof/Progress/Progress.lean`) asks, for every byte that
a tensor store reads (`Step.StoreDone.VisibleReadSources`),

1. a write that has been performed, covers the byte and is visible to the store's read of it;
2. that every such write has a defined byte there.

For a store of a full tile the write of (1) is the `stmatrix` write of the byte by the compute
thread that owns it, in the same tile; for a store of the final state it is the owner's
`st.b32` in the epilogue (also with no tile at all: the compute threads then store the
unchanged state). That these writes exist is not a consequence of the classification of the
union region (`UnionFacts` says what an access is, not that it has been made), so it is a
contract of its own:

* `StoreCover L X O`, for the same functions `O : Owners` as `UnionFacts`:
  - `store_in`: every byte a tensor store reads lies in the union region of the issuer's CTA;
  - `out_cover`: at its arrival on `storeFull o` a compute thread has written, since its
    previous arrival on that barrier, every byte of output buffer `o` that it owns;
  - `final_cover`: at its eighth `bar.sync 0` a compute thread has written, after its seventh,
    every byte of the union region that it owns in the final state;
  - `matrix_len`: the write event of a `stmatrix` lane carries 16 bytes;
  - `out_lt`, `final_lt`: the owner of a byte of an output buffer, and the final owner of a
    byte of the union region, is one of the 128 compute threads.
  Each of the first four is about the events of one thread; the last two are about `O` only.
* `UnionFacts.visibleReadSources`: `VisibleReadSources` for every tensor store, from
  `UnionFacts`, `StoreCover`, the store pipeline (`StoreFacts`) and two facts about write
  events (a write event carries as many bytes as its footprint; no atomic). `Export.lean`
  proves them by scans of the code, the first one for every write instruction but the 18
  `stmatrix`, for which it uses `matrix_len`.

Why the writer's event exists when the store is issued: a store of a tile follows the store
leader's successful poll of `storeFull o`, which observed the arrival of every compute thread
(`StoreFacts.full_handoff`), and the owner's arrival follows its writes (`out_cover`); a store
of the final state follows the leader's eighth `bar.sync 0`, so every thread has made its
eighth (`BarFacts.peer_bar0`), after its writes (`final_cover`). The order is
`StoreFacts.publish_output` for a tile and the proxy fence 3774 with the CTA barrier
(`publish_of_bar`) for the final state.

The simulator (`Gen/simulate.py`; the 128 compute threads and the store leader; 0, 1, 16, 17,
37 and 48 tokens, so with no tile, with one partial tile, and with a partial last tile)
confirms the five fields, with `out l = 32 * (x / 1024) + x % 512 / 16` at offset `x` of an
output buffer and `final` the one thread that writes the byte in the epilogue. A partial last
tile issues no tensor store of the output; its bytes leave through the store leader's generic
reads. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow PTX.Frame AsyncCopy MBarrier

/-- The positions of the 18 `stmatrix` instructions (two write an output buffer, sixteen the
bf16 state copy). The write event of a `stmatrix` lane follows its matrix event, and its bytes
are the lane's row as the thread state holds it, so their number is a fact about the thread's
state and not about the instruction alone. -/
def stmatrixPcs : List Nat :=
  [2503, 2505, 2543, 2564, 2593, 2614, 2643, 2664, 2693, 2714, 2743, 2764, 2793, 2814, 2843,
    2864, 2889, 2910]

/-- **The contract for the source bytes of the tensor stores** (see the module comment). -/
structure StoreCover (L : Launch) (X : Execution) (O : Owners) : Prop where
  /-- Every byte a tensor store reads lies in the union region of the issuer's CTA. -/
  store_in : ∀ {g i pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc},
    X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ → TensorStore.readLoc sp x y z = some l →
      InUnion L (g / L.block) l
  /-- At its arrival on `storeFull o` a compute thread has written, since its previous arrival
  on that barrier, every byte of output buffer `o` that it owns. -/
  out_cover : ∀ {c e pce tx cnt : Nat} {rel : Bool} {sc : MbarScope} (a : Fin 128) (o : Fin 2)
    {l : Loc},
    X.get (computeThread L c a, e) =
      some ⟨pce, .arrive ((Bar.storeFull o).loc L c) tx cnt rel sc⟩ →
    InOutput L c o.val l → O.out l = a.val →
      ∃ i pcw aw bs, i < e ∧ X.get (computeThread L c a, i) = some ⟨pcw, .wr aw bs⟩ ∧
        aw.Covers l ∧
        arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c a)).take i) =
          arrivals ((Bar.storeFull o).loc L c) ((X.tr (computeThread L c a)).take e)
  /-- At its eighth `bar.sync 0` a compute thread has written, after its seventh, every byte of
  the union region that it owns in the final state. -/
  final_cover : ∀ {c e pce : Nat} {cnt : Option Nat} {mode : BarMode} (a : Fin 128) {l : Loc},
    X.get (computeThread L c a, e) = some ⟨pce, .bar 0 cnt mode⟩ →
    bar0Before X (computeThread L c a, e) = 7 → InUnion L c l → O.final l = a.val →
      ∃ i pcw aw bs, i < e ∧ X.get (computeThread L c a, i) = some ⟨pcw, .wr aw bs⟩ ∧
        aw.Covers l ∧ bar0Before X (computeThread L c a, i) = 7
  /-- The write event of a `stmatrix` lane carries as many bytes as its footprint (16). For
  every other write instruction this is a property of the instruction (`Export.write_length`). -/
  matrix_len : ∀ {g i pc : Nat} {a : Acc} {bs : List Byte},
    X.get (g, i) = some ⟨pc, .wr a bs⟩ → pc ∈ stmatrixPcs → bs.length = a.size
  /-- The owner of a byte of an output buffer is a compute thread. -/
  out_lt : ∀ {c o : Nat} {l : Loc}, o < 2 → InOutput L c o l → O.out l < 128
  /-- The final owner of a byte of the union region is a compute thread. -/
  final_lt : ∀ {c : Nat} {l : Loc}, InUnion L c l → O.final l < 128

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {T : Nat → Nat} {O : Owners}

/-- **Every performed write has a defined byte at each byte it covers**, when write events
carry as many bytes as their footprint (`hlen`) and there is no atomic (`hrmw`): the two facts
about the code. -/
theorem write_defined (hN : NoEvents K X)
    (hlen : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → bs.length = a.size)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {w : Ref} {a : Acc}
    {bs : List Byte} {l : Loc} (hw : X.MemWrites w a bs) (hc : a.Covers l) :
    ∃ v, wbyte a bs l = some v := by
  have hl : bs.length = a.size → ∃ v, wbyte a bs l = some v := fun h => by
    obtain ⟨-, -, h1, h2⟩ := hc
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  apply hl
  rcases w with ⟨g, k⟩ | ⟨i, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · exact hlen _ _ _ _ he
    · exact (hrmw _ _ _ _ _ he).elim
  · cases part
    case async.writeStore x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeLoad x y z =>
      obtain ⟨_, _, b, -, -, -, -, hs, rfl, -⟩ := hw
      rw [hs]; rfl
    case async.writeCopy =>
      obtain ⟨s, hcp, -⟩ := hw
      exact (hN.copy _ _ hcp).elim
    case async.writeElem j =>
      obtain ⟨s, hcp, -⟩ := hw
      exact (hN.copy _ _ hcp).elim
    case async.writeCta c =>
      obtain ⟨_, _, hi, -⟩ := hw
      exact (hN.clc _ _ _ hi).elim
    all_goals exact hw.elim

/-- **Every byte a tensor store reads has a performed visible source write, and every visible
write of it has a defined byte** (`Step.StoreDone.VisibleReadSources`). -/
theorem UnionFacts.visibleReadSources (U : UnionFacts L X T O) (C : StoreCover L X O)
    (hSt : StoreFacts L X) (hI : InitFacts L X) (hB : BarFacts L X T) (hN : NoEvents K X)
    (hX : Consistent L K A mem0 X) (hb : L.block = 192)
    (hlen : ∀ e pc a bs, X.get e = some ⟨pc, .wr a bs⟩ → bs.length = a.size)
    (hrmw : ∀ e pc a o n, X.get e ≠ some ⟨pc, .rmw a o n⟩) {g i pc al : Nat}
    {sp : TensorStore.Spec} (hiss : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩) :
    Step.StoreDone.VisibleReadSources L X (g, i) sp := by
  intro slot loc _
  refine ⟨?_, fun w a' bs hw hcov' _ => write_defined hN hlen hrmw hw hcov'⟩
  have hslotAt : TensorTransfer.slotAt sp.descriptor slot.1.val slot.2.1.val slot.2.2.val =
      some slot := by
    simp only [TensorTransfer.slotAt, dite_eq_left slot.1.isLt, dite_eq_left slot.2.1.isLt,
      dite_eq_left slot.2.2.isLt]
  have hrl : TensorStore.readLoc sp slot.1.val slot.2.1.val slot.2.2.val =
      some (sp.sharedLoc slot) := by
    simp only [TensorStore.readLoc, hslotAt, Option.map_some]
  have hin := C.store_in hiss hrl
  have hcov := store_covers hiss hrl
  have hg := Frame.lt_of_get hX hiss
  have hc := cta_lt hb hg
  have his : i < (X.tr g).length := (List.getElem?_eq_some_iff.mp hiss).1
  change ∃ w a bs, X.MemWrites w a bs ∧ a.Covers (sp.sharedLoc slot) ∧
    ByteCausality L X (sp.sharedLoc slot) w
      (.async (g, i) (.read (.store slot.1.val slot.2.1.val slot.2.2.val)))
  generalize sp.sharedLoc slot = l at hrl hin hcov ⊢
  generalize hcc : g / L.block = c at hin hc
  obtain ⟨rfl, hpollS, hcs⟩ := U.store hiss hrl hin
  have hsdiv : storeLeader L c / L.block = c := hcc
  rcases hcs with ⟨o, hbar, hlo, hgate⟩ | hbar8
  · -- a store of a full tile: the owner's write of the tile, before its arrival
    obtain ⟨j, pcj, par, acq, sc, hji, hw, hq⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
      (m := (Bar.storeFull o).loc L c) (h := storeLeader L c) (f := i)
      (c := okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) - 1)
      (by omega)
    obtain ⟨xa, hxa, hs⟩ := hSt.full_handoff hI hB hN hX hb hc o (storeLeader L c) j pcj par
      acq sc (okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) - 1)
      ⟨0, rfl⟩ hw hq (computeThread L c ⟨O.out l, C.out_lt o.isLt hlo⟩) ⟨_, rfl⟩
    obtain ⟨rs, ⟨tx, cnt, pcx, hxget⟩, -⟩ := id hs
    obtain ⟨iw, pcw, aw, bs, hiw, hwget, hwcov, harr⟩ :=
      C.out_cover ⟨O.out l, C.out_lt o.isLt hlo⟩ o hxget hlo rfl
    have hj : arrivals ((Bar.storeFull o).loc L c)
        ((X.tr (computeThread L c ⟨O.out l, C.out_lt o.isLt hlo⟩)).take iw) ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) - 1 :=
      (harr.trans hxa).le
    have hp : okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) - 1 + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr (storeLeader L c)).take i) := by omega
    exact ⟨.thread (_, iw), aw, bs, .inl ⟨pcw, hwget⟩, hwcov,
      .direct (hSt.publish_output hI hB hN hX hb hc o ⟨O.out l, C.out_lt o.isLt hlo⟩
        (.inr (.inl ⟨bs, ⟨pcw, hwget⟩, rfl⟩)) hwcov hlo hj his hp hcov)⟩
  · -- a store of the final state: the owner's write of the epilogue, before its fence 3774
    have hlt := computeThread_lt hb hc ⟨O.final l, C.final_lt hin⟩
    have hdiv : computeThread L c ⟨O.final l, C.final_lt hin⟩ / L.block = c :=
      computeThread_div hb _
    obtain ⟨e, pce, md, he, heq⟩ := hB.peer_bar0 hX hb hlt (hdiv.trans hsdiv.symm) his
      (show 7 + 1 ≤ bar0Before X (storeLeader L c, i) by omega)
    obtain ⟨iw, pcw, aw, bs, hiw, hwget, hwcov, hb7⟩ :=
      C.final_cover ⟨O.final l, C.final_lt hin⟩ he heq hin rfl
    have hacc : X.Access (computeThread L c ⟨O.final l, C.final_lt hin⟩, iw) aw true :=
      .inr (.inl ⟨bs, ⟨pcw, hwget⟩, rfl⟩)
    obtain ⟨f, pcf, hif, hfget, hlt'⟩ := U.fence_before hB hX hb hacc (.inr rfl) hb7.le
      (hdiv.trans hsdiv.symm) his (by omega)
    exact ⟨.thread (_, iw), aw, bs, .inl ⟨pcw, hwget⟩, hwcov,
      .direct (publish_of_bar (hB.handoff0 hX hb) hif hfget ⟨hlt, hg, hdiv.trans hsdiv.symm⟩
        his hlt' hin.1 (hin.2.1.trans hdiv.symm) hcov)⟩

end PTX.Kernels.FlashKdaFwd.Protocol
