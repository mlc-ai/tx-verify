-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsArrives
public import Kernels.FlashAttn4Fwd.Proof.Protocol.BaseWord
public import Kernels.FlashAttn4Fwd.Proof.Protocol.RingOrdered
public import Kernels.FlashAttn4Fwd.Proof.Protocol.SmemElementsLoad
public import Kernels.FlashAttn4Fwd.Proof.Protocol.FloatsLoad
public import Kernels.FlashAttn4Fwd.Proof.Safety.Memory
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcLoads
public import Kernels.FlashAttn4Fwd.Proof.Result.Final
public import Kernels.FlashAttn4Fwd.Proof.ResultFacts
public import Lemmas.Tensor.BoxRead

@[expose] public section

/-! # The memory regions' and the loads' protocol inputs

This file sits at the top of the proof tree, outside the layer order (as `SafeFacts.lean` does):
it builds, from the thread layer's interface structures and the protocols' exports, the inputs of
the memory and Tensor Memory load branches.

* **The base word** (`baseOrdered'`, `BaseWord.baseRead`): the base word's region is the one
  `BaseWord.baseOrdered` orders.
* **The rings** (`qOrdered`, `kvOrdered`): a Q stage's and a KV slot's bytes are bytes of a ring
  region (`Rings.ring_ordered`).
* **The output** (`outputOrdered`): every access of a byte of O is a tensor store's slot write
  (`o_access`): a thread accesses only shared memory (`OlderFacts.access_shared`), a ring copy
  reads its input (Q, K or V), outside O (`load_outside`: `SmemElements.copy_readLoc`,
  `input_outside`), a tensor store's source read is of a staging buffer and none reduces
  (`OutputFacts.store_tma`), and the MMAs and the ring copies' writes are of shared memory. Two
  slot writes of one byte of O are the same slot of two stores of one item with one specification,
  by two lanes of the store warp (`stores_same`, as `Result.output_writers`), so they write the
  same byte (`Output.item_bytes_eq`): writes of the same bytes with the same value, which
  ERR-DATA-RACE does not count as a race (`SameValueWrites`).
* **The loads' sources** (`softLoads`, `corrLoads`): each register of a softmax or correction
  load has a source with a written value, by `Floats.LoadSources`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy Result

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The base word and the rings -/

/-- **The base word's conflicts are ordered.** -/
theorem baseOrdered' (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hr : RingFacts L X) (hout : OutputFacts L X) (htm : TmemFacts L X)
    (hmma : MmaReadsRings L X) (hst : StatsFacts L X) (hl : TmemLifeFacts L X)
    (has : AsyncFacts P L X) (ho : OlderFacts P L X) : ConflictsOrdered L X (Safety.InBase L) :=
  BaseWord.baseOrdered hpre hX hr hout htm hmma hst hl has ho

/-- A byte of a Q stage is a byte of a ring region. -/
theorem q_rings {l : Loc} (h : Safety.InQRing L l) : Rings.InRings L l := by
  obtain ⟨hs, h1, h2⟩ := h
  refine ⟨l.cta, .qFull ⟨(l.addr - (L.sharedBase + 68608)) / 32768, by omega⟩, rfl,
    hs, rfl, ?_, ?_⟩ <;> simp only [FBar.regionOff, FBar.regionSize] <;> omega

/-- A byte of a KV slot is a byte of a ring region. -/
theorem kv_rings {l : Loc} (h : Safety.InKvRing L l) : Rings.InRings L l := by
  obtain ⟨hs, h1, h2⟩ := h
  unfold sharedBytes at h2
  refine ⟨l.cta, .kvFull ⟨(l.addr - (L.sharedBase + 134144)) / 16384, by omega⟩, rfl,
    hs, rfl, ?_, ?_⟩ <;> simp only [FBar.regionOff, FBar.regionSize] <;> omega

/-! ### The output -/

/-- **A slot write of a tensor store**, from its footprint (as `Result.slot_write`). -/
theorem store_slot (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hX : Consistent L kernel asms mem0 X) (hs : StoreFacts P L X) {i : EvId} {x y k : Nat}
    {a : Acc} {w : Bool} (h : X.Intent (.async i (.write (.store x y k))) a w) :
    ∃ pc j, ∃ st hh : Fin 2, i.1 < L.threads ∧
      X.get i = some ⟨pc, .tensorStore P.oMap (oSpec P L i.1 j st hh)⟩ ∧ warpOf L i.1 = 13 ∧
      StoreSrc L X i.1 i.2 pc (oSpec P L i.1 j st hh) st ∧ pc = Store.Site.pc (.tma st hh) ∧
      arrivals (freeBar L (ctaOf L i.1) st) ((X.tr i.1).take i.2) = j ∧
      workOf L i.1 j < totOf L ∧ x < 64 ∧ y < 128 ∧ k < 2 ∧ a.size = 1 ∧
      a.loc = (elementLoc P P.oBase P.sq (tileBatch L i.1 j) (tileHead L i.1 j)
        (tileRow L i.1 j st + y) (64 * hh + x)).at k := by
  obtain ⟨-, s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := h
  have hg := event_thread_lt hX hget
  obtain ⟨st, hh, h13, hsrc, hpc, rfl, hj, hspec⟩ := hs.spec hg hget
  rw [hspec] at hloc hget hsrc
  obtain ⟨hx, hy, hk⟩ := oSpec_slot hloc
  obtain ⟨hb, hhd, -⟩ := tile_lt hpre hco hj
  rw [oSpec_writeLoc hx hy hk hh.isLt (row_lt hpre hco hj st.isLt hy) hhd hb] at hloc
  exact ⟨pc, _, st, hh, hg, hget, h13, hsrc, hpc, rfl, hj, hx, hy, hk, hsz,
    (Option.some.inj hloc).symm⟩

/-- **Two slot writes of one byte are the same slot of two stores of one item**, with one
specification, by two lanes of the store warp of one CTA. -/
theorem stores_same (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : StoreFacts P L X) {i i' : EvId} {x y z x' y' z' : Nat} {a a' : Acc} {w w' : Bool}
    {l : Loc} (h : X.Intent (.async i (.write (.store x y z))) a w)
    (h' : X.Intent (.async i' (.write (.store x' y' z'))) a' w') (hc : a.Covers l)
    (hc' : a'.Covers l) :
    x = x' ∧ y = y' ∧ z = z' ∧ ∃ c st jj pc s, st < 2 ∧ Output.rd L X c st jj i (x, y, z) ∧
      Output.rd L X c st jj i' (x, y, z) ∧ X.get i = some ⟨pc, .tensorStore P.oMap s⟩ ∧
      X.get i' = some ⟨pc, .tensorStore P.oMap s⟩ := by
  have hco := itemCoords hpre
  obtain ⟨g, kk⟩ := i
  obtain ⟨g', kk'⟩ := i'
  obtain ⟨pc, j, st, hh, hgt, hget, hwarp, hsrc, rfl, harr, hj, hx, hy, hz, hsz, hloc⟩ :=
    store_slot hpre hco hX hs h
  obtain ⟨pc', j', st', hh', hgt', hget', hwarp', hsrc', hpc', harr', hj', hx', hy', hz', hsz',
    hloc'⟩ := store_slot hpre hco hX hs h'
  dsimp only at hgt hget hwarp hsrc harr hj hloc hgt' hget' hwarp' hsrc' harr' hj' hloc'
  rw [Rings.covers_one hc hsz] at hloc
  rw [Rings.covers_one hc' hsz', hloc] at hloc'
  obtain ⟨hb, hhd, -⟩ := tile_lt hpre hco hj
  obtain ⟨hb', hhd', -⟩ := tile_lt hpre hco hj'
  obtain ⟨e1, e2, e3, e4, rfl⟩ := element_inj hhd (row_lt hpre hco hj st.isLt hy) (by omega) hz
    hhd' (row_lt hpre hco hj' st'.isLt hy') (by omega) hz' hloc'
  obtain ⟨htot, hG, hcs⟩ := hco
  have hW := hcs _ (htot ▸ hj)
  have hW' := hcs _ (htot ▸ hj')
  simp only [tileBatch, tileHead, tileRow, tileBlock, hW, hW'] at e1 e2 e3
  have hr := rankOf_eq hpre g
  have hr' := rankOf_eq hpre g'
  have hrl : ctaOf L g % 2 < 2 := Nat.mod_lt _ (by decide)
  have hrl' : ctaOf L g' % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [hr] at e3
  rw [hr'] at e3
  generalize hmw : workOf L g j % P.blocks = m at e3
  generalize hmw' : workOf L g' j' % P.blocks = m' at e3
  have hst : st = st' := Fin.ext (by omega)
  have hyy : y = y' := by omega
  have hrk : ctaOf L g % 2 = ctaOf L g' % 2 := by omega
  have hmm : m = m' := by omega
  have hhh : hh = hh' := Fin.ext (by omega)
  have hxx : x = x' := by omega
  subst hst hyy hhh hxx
  have hww : workOf L g j = workOf L g' j' := work_eq e1 e2 (by rw [hmw, hmw', hmm])
  have hcl := clusterOf_lt hpre hgt
  have hcl' := clusterOf_lt hpre hgt'
  simp only [workOf, hG] at hww
  obtain ⟨rfl, hcc⟩ := Nat.digits_of_eq hcl hcl' (by rw [Nat.add_comm, hww, Nat.add_comm])
  rw [clusterOf_eq hpre, clusterOf_eq hpre] at hcc
  have hcta : ctaOf L g = ctaOf L g' := by omega
  subst hpc'
  rw [oSpec_cta hcta.symm] at hget' hsrc'
  refine ⟨rfl, rfl, rfl, ctaOf L g, st, j, _, oSpec P L g j st hh, st.isLt,
    ⟨⟨hgt, rfl, hwarp⟩, ⟨_, _, _, hget, hsrc⟩, harr⟩,
    ⟨⟨hgt', hcta.symm, hwarp'⟩, ⟨_, _, _, hget', hsrc'⟩, hcta ▸ harr'⟩, hget, hget'⟩

/-- **A ring copy reads outside O**: its source byte is a byte of its input, Q, K or V. -/
theorem load_outside (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (has : AsyncFacts P L X) (hcp : RingCopies P L X) {i : EvId}
    {x y z : Nat} {a : Acc} {w : Bool} {l : Loc} (h : X.Intent (.async i (.read (.load x y z))) a w)
    (hc : a.Covers l) : ¬ Safety.InTensor P P.oBase P.sq l := by
  obtain ⟨g, k⟩ := i
  obtain ⟨-, s, addr, ⟨pc, hget⟩, hloc, hsz⟩ := h
  obtain ⟨b, c, hring, hm⟩ := has.copy_ring hget
  have hg := event_thread_lt hX hget
  obtain ⟨hfull, -⟩ := ht.issue hg hget hm hring
  have hsp := hcp.copy hg hget hm hfull
  have hw := has.copy_started hg hget hm hfull
  dsimp only at hsp hw
  rw [hsp] at hloc
  obtain ⟨hx, hy, hz⟩ := TensorCopy.readLoc_bounds hloc
  obtain ⟨h0, hR, hf, -⟩ := Rings.copyMap_geom (P := P) hfull
  set cnt := ((X.tr g).take k).countP (issuesTo (b.loc L c))
  have hx' : x < 64 := by
    have : TensorTile.count (copySpec P L g b cnt).descriptor.box 0 = 64 := h0
    omega
  have hy' : y < b.copyBytes / 128 := by
    have : TensorTile.rows (copySpec P L g b cnt).descriptor.box = b.copyBytes / 128 := hR
    omega
  have hz' : z < 2 := by
    have : (copySpec P L g b cnt).descriptor.format.bytes = 2 := by
      change (copyMap P b).format.bytes = 2; rw [hf]; rfl
    omega
  obtain ⟨hbt, hhd, hr, hd, hrl⟩ := SmemElements.copy_readLoc hpre hfull _ hw hx' hy' hz'
  rw [hrl, Option.some.injEq] at hloc
  rw [← Rings.covers_one hc hsz, ← hloc]
  rintro ⟨-, h1, h2, h3⟩
  exact SmemElements.input_outside hpre hfull hbt hhd hr hd hz' ⟨h1, h2, h3⟩

/-- **Every access of a byte of O is a tensor store's slot write.** -/
theorem o_access (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (has : AsyncFacts P L X)
    (hcp : RingCopies P L X) (hout : OutputFacts L X) (ho : OlderFacts P L X) {ref : Ref}
    {a : Acc} {w : Bool} {l : Loc} (h : X.Intent ref a w) (hc : a.Covers l)
    (hl : Safety.InTensor P P.oBase P.sq l) :
    ∃ i x y z, ref = .async i (.write (.store x y z)) := by
  have hg : l.space = .global := hl.1
  have hsh : a.loc.space = .shared → False := fun hs => by
    rw [hc.1, hs] at hg
    cases hg
  rcases ref with ⟨g, k⟩ | ⟨i, p⟩
  · exact (hsh (ho.access_shared h)).elim
  cases p with
  | writeStore x y z => exact ⟨i, x, y, z, rfl⟩
  | mmaRead isB idx => exact (hsh (Execution.mmaFootprint_shared h.2.2)).elim
  | readStore x y k =>
    obtain ⟨-, s, addr, ⟨pc, hget⟩, hloc, -⟩ := h
    obtain ⟨-, st, -, hsrc⟩ := hout.store_tma (event_thread_lt hX hget) hget
    exact (hsh (hsrc.2.1 x y k a.loc hloc).1).elim
  | oldStore x y k =>
    obtain ⟨-, s, addr, ⟨pc, hget⟩, hred, -⟩ := h
    obtain ⟨-, st, -, hsrc⟩ := hout.store_tma (event_thread_lt hX hget) hget
    rw [hsrc.1] at hred
    cases hred
  | readLoad x y z => exact (load_outside hpre hX ht has hcp h hc hl).elim
  | writeLoad x y z =>
    obtain ⟨-, -, -, b, -, -, -, hreg⟩ := ht.write (g := i.1) (k := i.2) ⟨a, w, h, hc⟩
    rw [hreg.1] at hg
    cases hg
  | readPrefetch x y z =>
    obtain ⟨-, s, addr, ⟨pc, hget⟩, -⟩ := h
    exact (has.no_prefetch hget).elim
  | writeCta c =>
    obtain ⟨-, s, tg, ⟨pc, hci⟩, -⟩ := h
    exact (htm.no_clc hci).elim
  | readCopy =>
    rcases h.2 with ⟨s, ⟨pc, hbk⟩, -⟩ | ⟨pc, hpf⟩
    · exact (htm.no_bulk hbk).elim
    · exact (htm.no_prefetch hpf).elim
  | writeCopy =>
    obtain ⟨s, ⟨pc, hbk⟩, -⟩ := h.2
    exact (htm.no_bulk hbk).elim
  | writeElem j =>
    obtain ⟨s, ⟨pc, hbk⟩, -⟩ := h.2
    exact (htm.no_bulk hbk).elim
  | oldElem j =>
    obtain ⟨s, r, ⟨pc, hbk⟩, -⟩ := h.2
    exact (htm.no_bulk hbk).elim
  | _ => exact h.2.elim

/-- **O's conflicts are ordered but for identical-value write pairs**: every conflict on O is a
pair of the store warp's slot writes of one element, which write the same byte. -/
theorem outputOrdered (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : RingFacts L X) (htm : TmemFacts L X) (has : AsyncFacts P L X)
    (hcp : RingCopies P L X) (hout : OutputFacts L X) (hs : StoreFacts P L X)
    (ho : OlderFacts P L X) (hH : Output.OutputHandoff L X)
    (hsa : ∀ i p a w l, X.Intent (.async i p) a w → a.Covers l → InStaging L l →
      ∃ x y k, p = .read (.store x y k)) :
    ConflictsOrderedExcept L X (Safety.InTensor P P.oBase P.sq) := by
  intro e f a b l hcon ha hb hl hE
  exfalso
  obtain ⟨-, we, wf, he, hf, -, -⟩ := hcon
  obtain ⟨i, x, y, z, rfl⟩ := o_access hpre hX ht htm has hcp hout ho he ha hl
  obtain ⟨i', x', y', z', rfl⟩ := o_access hpre hX ht htm has hcp hout ho hf hb hl
  obtain ⟨rfl, rfl, rfl, c, st, jj, pc, s, hst, hri, hri', hgi, hgi'⟩ :=
    stores_same hpre hX hs he hf ha hb
  obtain rfl : we = true := he.1
  obtain rfl : wf = true := hf.1
  have hsz : ∀ {i : EvId} {x y z : Nat} {c : Acc} {w : Bool},
      X.Intent (.async i (.write (.store x y z))) c w → c.size = 1 := by
    rintro i x y z c w ⟨-, -, -, -, -, h⟩
    exact h
  refine hE ⟨he, hf, ⟨(Acc.loc_of_one ha (hsz he)).trans (Acc.loc_of_one hb (hsz hf)).symm,
    (hsz he).trans (hsz hf).symm⟩, fun bs bs' hw hw' => ?_⟩
  obtain ⟨o, -, v, ho1, -, -, hv, -, rfl, -⟩ := hw
  obtain ⟨o', -, v', ho1', -, -, hv', -, rfl, -⟩ := hw'
  rw [Output.item_bytes_eq hpre hX hout hH hsa hst hri hri' hgi hgi' ho1 ho1' hv hv']

/-! ### The loads' sources -/

/-- Each register of a softmax load has a source of its cell, with a written value. -/
theorem softLoads (h : Floats.LoadSources L X) : Safety.SoftLoadSources L X :=
  fun _ _ _ _ _ hh _ hld hj =>
    let ⟨src, value, hr, hw, _⟩ := h hh hld hj
    ⟨src, value, hr, hw⟩

/-- Each register of a correction load has a source of its cell, with a written value. -/
theorem corrLoads (h : Floats.LoadSources L X) : Safety.CorrLoadSources L X :=
  fun _ _ _ _ _ hh _ _ hld hj =>
    let ⟨src, value, hr, hw, _⟩ := h hh hld hj
    ⟨src, value, hr, hw⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
