-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.MmaAll
public import Kernels.InklingRelDecode.Proof.Interface.WzAll

@[expose] public section

/-!
# `OperandSourcesT`: the MMAs' shared operand bytes have ordered sources

`OperandSourcesT L X` (`Lemmas/Step/MmaDrainTmemA.lean`) is asked of every maximal execution, so
of executions in which an MMA may be issued and not yet started. It has three parts.

* `TcMma.WarpIssuerUnique`: every MMA of a CTA is issued by the handshake package's committing
  lane (`Sr.Lane.mma_thread`), so two MMAs of one warp have one thread.
* `TcMma.Valid` of each MMA's instruction descriptor: `qkDesc` or `pvDesc`
  (`Result.Mma.mma_event_cases`, `Ring.Foot.qkDesc_valid`, `pvDesc_valid`).
* A source for each byte of each footprint. Operand index `idx` of a QK or PV MMA is element
  `(idx / 32, idx / 2 % 16)`, byte `idx % 2` (`qk_b_idx`, `qk_a_idx`, `pv_b_idx`); a PV MMA's A
  operand is in Tensor Memory and has no shared byte (`Ring.Foot.pv_a_none`).
  - B of QK MMA `j` of block `i`, B of PV MMA `j` of block `i` (iteration `i + 1`): the byte is
    element `(n, e)` of the K or V tile of slot `i % 3` (`qk_b_loc_eq`, `pv_b_loc_eq`); the copy
    of block `i` of the box `(isV, n / 64, e / 64)` (premise `KvCopiesF`) writes it
    (`copy_loc_kv`), and `Wz.kvOrderF` orders it against the MMA's read stage and every other
    write.
  - A of QK MMA `j`: the byte is byte `z` of element `(r, 16 j + kk)` of the query tile
    (`qk_a_loc_eq`), whose store and its order are the premise `QTileF`.

The two premises are the forms of `Result.Mma.KvCopies` and `Result.Mma.QTile` for an execution
that need not be complete: `KvCopies` names the copies of every block below `num_iters` and
`QTile` the query stores, both proved from `Complete L X` (`Lp.kvCopies_of`, `Lp.qTile_of`);
here a copy or a store is asked for only when an MMA that reads it has been issued. Both hold on
every consistent execution: `qTileF_of` (below) and `kvCopiesF_of` (`WzKvCopies.lean`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Wz
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof AsyncCopy
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Ring.Foot (qkDesc pvDesc qkDesc_valid pvDesc_valid)
open PTX.Kernels.InklingRelDecode.Proof.EvW (kvCopySpec)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The premises -/

/-- **The K/V copies of a block an issued MMA reads.** For an MMA event `m` of block `i` and each
box `(isV, slab, hh)`, a tensor copy of block `i` of the CTA, with an observation, whose spec
is `kvCopySpec` with the box's destination in ring slot `i % 3`. -/
structure KvCopiesF (Q : Params) (L : Launch) (X : Execution) : Prop where
  exists_copy : ∀ {m : EvId} {dm : Mma.D} {i : Nat} (isV slab hh : Nat), m.1 < L.threads →
    (∃ d sp acc mask, X.MmaIssue m d sp acc mask) → AtMma Q L X m dm → MmaBlock dm i → isV ≤ 1 →
    slab ≤ 1 → hh ≤ 1 → ∃ (c : EvId) (o : TensorCopy.Observation) (a col row : Nat) (bar : Loc),
      X.TensorIssue c a o.spec ∧ X.tensor c = some o ∧ CopyBlock Q L X c i ∧
      o.spec = kvCopySpec Q (m.1 / L.block) col row
        (L.sharedBase + 32768 * (i % 3) + 98304 * isV + 8192 * slab + 16384 * hh) bar

/-- **The query store of a byte an issued QK MMA reads.** For a QK MMA event `m` and byte `z` of
element `(r, e)` of the query tile (`r < 64`), a thread write `w` covers the byte, it is before
the MMA's read stage of every operand index at the byte, and every other write covering the byte
is `w`, before it, or after the read stage. -/
structure QTileF (Q : Params) (L : Launch) (X : Execution) : Prop where
  tile : ∀ {m : EvId} {dm : Mma.D} {j : Fin 8} {r e z : Nat}, m.1 < L.threads →
    (∃ ev, X.get m = some ev) → AtMma Q L X m dm → dm.site = .qk j → r < 64 → e < 128 →
    z < 2 → ∃ (w : EvId) (a : Acc) (bs : List Byte), (∃ pc, X.get w = some ⟨pc, .wr a bs⟩) ∧
      a.Covers ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩ ∧
      ∀ {idx : Nat},
        X.MmaFootprint m false idx ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩ →
        modelCausality L X ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩ (.thread w)
          (.async m (.mmaRead false idx)) ∧
        ∀ other fp bytes, X.MemWrites other fp bytes →
          fp.Covers ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩ →
          other = .thread w ∨
          modelCausality L X ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩ other
            (.thread w) ∨
          modelCausality L X ⟨.shared, m.1 / L.block, qAddr L.sharedBase r e z⟩
            (.async m (.mmaRead false idx)) other

/-! ### Operand indices -/

/-- A byte of the B operand of a QK MMA has an index below 4096 (128 rows of 32 bytes). -/
theorem qk_b_idx {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {idx : Nat} {l : Loc}
    (h : s.byteLoc .b idx = some l) : idx < 4096 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv] at h
  omega

/-- A byte of the A operand of a QK MMA has an index below 2048 (64 rows of 32 bytes). -/
theorem qk_a_idx {s : TcMma.OperandSpec} (hD : s.descriptor = qkDesc) {idx : Nat} {l : Loc}
    (h : s.byteLoc .a idx = some l) : idx < 2048 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, qkDesc, TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := qkDesc_valid
  simp only [qkDesc] at hv
  simp [hv] at h
  omega

/-- A byte of the B operand of a PV MMA has an index below 4096. -/
theorem pv_b_idx {s : TcMma.OperandSpec} (hD : s.descriptor = pvDesc) {idx : Nat} {l : Loc}
    (h : s.byteLoc .b idx = some l) : idx < 4096 := by
  unfold TcMma.OperandSpec.byteLoc at h
  simp only [hD, pvDesc, TcMma.Operand.extent, TcMma.Kind.k, TcMma.Kind.width] at h
  have hv := pvDesc_valid
  simp only [pvDesc] at hv
  simp [hv] at h
  omega

theorem idx_split (idx : Nat) : idx = 32 * (idx / 32) + 2 * (idx / 2 % 16) + idx % 2 := by
  omega

/-! ### `QTileF` -/

/-- **`QTileF` on every consistent execution.** The MMA event is past the MMA warp's first
barrier-1 event, so the store's thread has made its first barrier-1 event (`bar1_has`); its
store, the order through the fence and the uniqueness of the writer follow from that event
(`Lp.bar1_of_mma`, `Lp.qtile_writer`, `Lp.qtile_other`). -/
theorem qTileF_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk)
    (hR : RoleReads L X) (hE : Bar1Exits L X) : QTileF Q L X := by
  refine ⟨fun {m dm j r e z} hm hev hAt _ hr he hz => ?_⟩
  obtain ⟨gm, km⟩ := m
  obtain ⟨P, hσm⟩ := hAt
  obtain ⟨ev, hget⟩ := hev
  have hn : km < (X.tr gm).length := len_of_get hget
  have hb1 := Lp.mma_b1 hpre hX hf hR hn.le hσm
  have hb : L.block = 256 := hpre.block
  have hth : L.threads = L.grid * L.block := rfl
  have hq := Lp.qThread_lt (r := r) (d := e)
  have hm' : gm < L.threads := hm
  set t := gm / L.block * L.block + Lp.qThread r e with ht
  have htl : t < L.threads := by
    have h1 := ProA.grid_lt hm'
    have h2 : t < (gm / L.block + 1) * L.block := by rw [ht, hb]; omega
    rw [hth]
    exact lt_of_lt_of_le h2 (Nat.mul_le_mul_right _ h1)
  have htc : t / L.block = gm / L.block := by rw [ht, hb]; omega
  obtain ⟨i0, pc', hfi, hc0⟩ := Lp.bar1_of_mma hpre hX hf hR hE (m := (gm, km)) hn hσm htc
  obtain ⟨k, j1, pc, dt, a, v, hgw, hcz, -, hσ1, hkj, hj1, hfence, hσk⟩ :=
    Lp.qtile_writer hpre hX hf hT hm he hr hfi hc0
  have hcov := (hcz z hz).1
  refine ⟨(t, k), a, v.toBytes, ⟨pc, hgw⟩, hcov, fun {idx} hfp => ⟨?_, ?_⟩⟩
  · refine ⟨⟨{ loc := _, size := 1 }, false, ⟨rfl, rfl, hfp⟩,
      ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩, .inl ?_⟩
    exact Lp.stq_proxyBefore hpre hX hE htl hfi hc0 hj1 hkj hfence hm' htc.symm hn hb1 rfl
      htc.symm
  · intro other fp bytes hw hcv
    left
    rw [Lp.qtile_other hpre hX hf he hz hr hfi hc0 hσk hw hcv]

/-! ### The assembly -/

/-- **One thread issues the MMAs of a warp**: every MMA of a CTA is the committing lane's. -/
theorem warpIssuerUnique_of (G : Sr.SrPkg L kernel asms mem0 X) :
    TcMma.WarpIssuerUnique L X := by
  intro i j hi hj hw
  obtain ⟨⟨hgi, -, hc⟩, -⟩ := hw
  have hci : i.1 / L.block < L.grid := ProA.grid_lt hgi
  rw [(G.lane _ hci).mma_thread (x := i) hi rfl, (G.lane _ hci).mma_thread (x := j) hj hc.symm]

/-- The footprint of an MMA event is its spec's (the kernel has no `tcgen05.cp`). -/
theorem foot_loc (hX : Consistent L kernel asms mem0 X) {i : EvId} {pc d : Nat}
    {sp : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : X.get i = some ⟨pc, .tc (.mma d sp acc mask)⟩) {isB : Bool} {idx : Nat} {l : Loc}
    (h : X.MmaFootprint i isB idx l) : sp.byteLoc (if isB then .b else .a) idx = some l := by
  rcases h with ⟨d', s', acc', mask', ⟨pc', he'⟩, hb⟩ | ⟨c, -, -, hcp, -⟩
  · rw [he] at he'
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at he'
    rw [he'.2.2.1]
    exact hb
  · exact absurd hcp (Tmem1.no_cp hX _ _)

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hR : RoleReads L X) (hE : Bar1Exits L X)
    (hp : NumPreRead Q L X) (hbox : Safety.BoxInBounds X) (G : Sr.SrPkg L kernel asms mem0 X)
include hpre hX hf hT hR hE hp hbox G

/-- **A byte of a K or V slot that an MMA of block `i` reads has an ordered source**: the copy of
the box (premise `KvCopiesF`) writes it at the slot coordinates `(e % 64, n % 64, z)`. -/
theorem kv_source (hMB : Mma.MmaBcast L X) (hk : KvCopiesF Q L X) {m : EvId} {dm : Mma.D} {i : Nat}
    (hm : m.1 < L.threads) (hev : ∃ d sp acc mask, X.MmaIssue m d sp acc mask)
    (hAt : AtMma Q L X m dm) (hblk : MmaBlock dm i) {isV n e z : Nat} (hV : isV ≤ 1) (hn : n < 128)
    (he : e < 128) (hz : z < 2) {isB : Bool} {idx : Nat}
    (hfp : X.MmaFootprint m isB idx ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩)
    :
    ∃ src : MmaSources.ByteSource X,
      src.loc = ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ ∧
      ∀ w a bs, X.MemWrites w a bs →
        a.Covers ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ →
        w = src.ref ∨
        modelCausality L X ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ w
          src.ref ∨
        modelCausality L X ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩
          (.async m (.mmaRead isB idx)) w := by
  obtain ⟨c, o, a, col, row, bar, hTI, hobs, hcb, hspec⟩ :=
    hk.exists_copy isV (n / 64) (e / 64) hm hev hAt hblk hV (by omega) (by omega)
  have hsb : L.sharedBase % 128 = 0 := by have := hpre.sharedAlignment; omega
  have hwl : TensorCopy.writeLoc o.spec (e % 64) (n % 64) z =
      some ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩ := by
    rw [hspec]
    exact copy_loc_kv Q _ _ isV _ _ _ bar hsb hn he hz
  obtain ⟨⟨b, hwb⟩, -, hoth⟩ := kvOrderF hpre hX hf hT hR hE hp hbox G hMB hAt hblk hcb hobs hTI
    hwl hfp
  refine ⟨⟨_, .async c (.write (.load (e % 64) (n % 64) z)),
    { loc := ⟨.shared, m.1 / L.block, kvAddr L.sharedBase (i % 3) isV n e z⟩, size := 1 }, [b],
    ⟨o, a, b, hobs, hTI, hwl, hwb, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, le_refl _, Nat.lt_succ_self _⟩⟩, rfl, hoth⟩

/-- **`OperandSourcesT`** for every consistent execution, from the premises `QTileF` and
`KvCopiesF`. -/
theorem operandSources_of (hMB : Mma.MmaBcast L X) (hq : QTileF Q L X) (hk : KvCopiesF Q L X)
    : OperandSourcesT L X := by
  refine ⟨warpIssuerUnique_of G, ?_⟩
  intro ⟨g, k⟩ dst sp acc mask ⟨pc, he⟩
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hev : ∃ ev, X.get (g, k) = some ev := ⟨_, he⟩
  have hmi : ∃ d sp acc mask, X.MmaIssue (g, k) d sp acc mask := ⟨_, _, _, _, pc, he⟩
  have hE' := EvW.mmEnv_of_pre hpre
  rcases mma_event_cases hpre hX hf hg he with
    ⟨dm, P, j, hσ, hI, hs, hqo, -, -, -⟩ | ⟨dm, P, j, hσ, hI, hs, hqo, -, -, -⟩
  · -- a QK MMA
    refine ⟨hqo.desc ▸ qkDesc_valid, fun isB idx l hfp => ?_⟩
    have hbl := foot_loc hX he hfp
    cases isB
    · -- A: the query tile
      simp only [Bool.false_eq_true, ↓reduceIte] at hbl
      have hidx := qk_a_idx hqo.desc hbl
      rw [idx_split idx, qk_a_loc_eq hE' hqo.desc j.isLt hqo.a hqo.aTmem (by omega)
        (by omega) (by omega), hqo.low] at hbl
      obtain rfl := (Option.some.inj hbl).symm
      obtain ⟨w, a, bs, hwr, hcov, hord⟩ := hq.tile (m := (g, k)) hg hev ⟨P, hσ⟩ hs
        (r := idx / 32) (e := 16 * j.val + idx / 2 % 16) (z := idx % 2) (by omega) (by omega)
        (by omega)
      exact ⟨⟨_, .thread w, a, bs, Or.inl hwr, hcov⟩, rfl, (hord hfp).2⟩
    · -- B: the K tile of slot `i % 3`
      simp only [↓reduceIte] at hbl
      have hidx := qk_b_idx hqo.desc hbl
      rw [idx_split idx, qk_b_loc_eq hE' hqo.desc (Nat.mod_lt _ (by omega)) j.isLt hqo.b
        (by omega) (by omega) (by omega), hqo.low] at hbl
      obtain rfl := (Option.some.inj hbl).symm
      exact kv_source hpre hX hf hT hR hE hp hbox G hMB hk (m := (g, k)) hg hmi ⟨P, hσ⟩
        (Or.inl ⟨j, hs, rfl⟩) (isV := 0) (by omega) (by omega) (by omega) (by omega) hfp
  · -- a PV MMA
    refine ⟨hqo.desc ▸ pvDesc_valid, fun isB idx l hfp => ?_⟩
    have hbl := foot_loc hX he hfp
    cases isB
    · -- A is in Tensor Memory
      simp only [Bool.false_eq_true, ↓reduceIte] at hbl
      exfalso
      obtain ⟨-, dm', P', -, -, ⟨j', -, da, db, dsc, hdc, -, -, -, hsp⟩ |
        ⟨j', -, db, dsc, hdc, -, -, hsp⟩⟩ := Tmem1.mma_cases hpre hX hf he
      · have h1 := hqo.desc
        rw [hsp, Ring.Foot.qkDesc_eq hdc] at h1
        exact absurd h1 (by simp [qkDesc, pvDesc])
      · rw [hsp, Ring.Foot.pv_a_none rfl] at hbl
        cases hbl
    · -- B: the V tile of slot `(i - 1) % 3`
      simp only [↓reduceIte] at hbl
      have hidx := pv_b_idx hqo.desc hbl
      obtain ⟨h1, -, -⟩ := hI.pv (by simp [Mma.PvSite, hs])
      rw [idx_split idx, pv_b_loc_eq hE' hqo.desc (Nat.mod_lt _ (by omega)) j.isLt hqo.b
        (by omega) (by omega) (by omega), hqo.low] at hbl
      obtain rfl := (Option.some.inj hbl).symm
      exact kv_source hpre hX hf hT hR hE hp hbox G hMB hk (m := (g, k)) hg hmi ⟨P, hσ⟩
        (Or.inr ⟨j, hs, by omega⟩) (isV := 1) (le_refl _) (by omega) (by omega) (by omega) hfp

end
end PTX.Kernels.InklingRelDecode.Proof.Wz
