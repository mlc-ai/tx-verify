-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputSlotSource
public import Kernels.TmlFa4Fwd.Proof.EpilogueWriteback
public import Lemmas.TensorStore.StoreWrite
public import Lemmas.TensorStore.SourceBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Epilogue

noncomputable section

/-- Every output store in the successful writeback sequence is an actual issue in the
thread trace. The index counts failed ready polls as well as successful events. -/
theorem writebackIssue {p : Params} {l : Launch} {X : Execution} {g start batch head tile : Nat}
    {written suffix : List Event} (hTrace : (X.tr g).drop start = written ++ suffix)
    (hEvents : written.filter (fun e => writebackSucceeded e.kind) =
      writebackRemaining p l g batch head tile (some (.ready 0)))
    (stage : Fin 2) (subbox : Fin 4) :
    ∃ n < written.length,
      X.get (g, start + n) = some ⟨storePc stage subbox,
        .tensorStore p.oMapAddress (writebackStoreSpec p l g batch head tile stage subbox)⟩ := by
  let site := WritebackSite.store stage subbox
  let e : Event := ⟨storePc stage subbox,
    .tensorStore p.oMapAddress (writebackStoreSpec p l g batch head tile stage subbox)⟩
  have hSite : site ∈ writebackSites := by
    fin_cases stage <;> fin_cases subbox <;> simp [site, writebackSites]
  have hMem : e ∈ written.filter (fun e => writebackSucceeded e.kind) := by
    rw [hEvents]
    change e ∈ writebackSites.map (fun s =>
      ⟨writebackPc (some s), writebackKind p l g batch head tile s true⟩)
    exact List.mem_map.mpr ⟨site, hSite, rfl⟩
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp (List.mem_filter.mp hMem).1
  have hn' : n < written.length := List.getElem?_eq_some_iff.mp hn |>.1
  refine ⟨n, hn', ?_⟩
  change (X.tr g)[start + n]? = some e
  rw [← List.getElem?_drop, hTrace, List.getElem?_append_left hn', hn]

variable {p : Params} {l : Launch} {m : Mem0}

/-- A completed output issue writes every byte in its valid request-local rows. The
observation identifies the byte whose shared-memory provenance is proved separately. -/
theorem writebackIssuedByte {X : Execution} {A : List Assumption} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) (hComplete : Complete l X) {i : EvId}
    {batch head tile x y k : Nat} (stage : Fin 2) (subbox : Fin 4)
    (hi : X.TensorStoreIssue i p.oMapAddress
      (writebackStoreSpec p l i.1 batch head tile stage subbox)) (hb : batch < p.batch)
    (hh : head < p.heads) (hx : x < 32) (hy : y < 128) (hk : k < 4)
    (hr : stageRow tile stage + y < p.qLength batch) :
    let dst := (p.oLoc (p.qOffset batch + stageRow tile stage + y) head (32 * subbox.val + x)).at k
    ∃ o b, X.tensorStores i = some o ∧ TensorStore.writeByte o x y k = some b ∧
      X.MemWrites (.async i (.write (.store x y k)))
        ⟨dst, 1, false, false, .cta, 0, false⟩ [b] := by
  dsimp only
  apply hComplete.store_write hX hi
  rw [writebackWriteLoc hp stage subbox x y k hb hh]
  simp [hx, hy, hk, hr, Nat.add_assoc]

/-- Every legal O byte of the tile is written in a complete execution with its associated
writeback trace. The witness uses the subbox and stage containing that byte. -/
theorem writebackTileByte {X : Execution} {A : List Assumption} (hp : Pre p l m)
    (hX : Consistent l kernel A m X) (hComplete : Complete l X) {g start batch head row col k : Nat}
    {written suffix : List Event} (hTrace : (X.tr g).drop start = written ++ suffix)
    (hEvents : written.filter (fun e => writebackSucceeded e.kind) =
      writebackRemaining p l g batch head (row / 256) (some (.ready 0))) (hb : batch < p.batch)
    (hh : head < p.heads) (hr : row < p.qLength batch) (hc : col < 128) (hk : k < 4) :
    ∃ (stage : Fin 2) (subbox : Fin 4), ∃ n < written.length, ∃ o b,
      X.get (g, start + n) = some ⟨storePc stage subbox, .tensorStore p.oMapAddress
        (writebackStoreSpec p l g batch head (row / 256) stage subbox)⟩ ∧
      X.tensorStores (g, start + n) = some o ∧
      TensorStore.writeByte o (col % 32) (row % 128) k = some b ∧
      X.MemWrites (.async (g, start + n) (.write (.store (col % 32) (row % 128) k)))
        ⟨(p.oLoc (p.qOffset batch + row) head col).at k, 1, false, false, .cta, 0, false⟩ [b] := by
  let stage : Fin 2 := ⟨row % 256 / 128, by omega⟩
  let subbox : Fin 4 := ⟨col / 32, by omega⟩
  have hRow : stageRow (row / 256) stage + row % 128 = row := by
    dsimp [stageRow, stage]
    omega
  have hCol : 32 * subbox.val + col % 32 = col := by dsimp [subbox]; omega
  obtain ⟨n, hn, hi⟩ := writebackIssue hTrace hEvents stage subbox
  have hIssue : X.TensorStoreIssue (g, start + n) p.oMapAddress
      (writebackStoreSpec p l g batch head (row / 256) stage subbox) := ⟨_, hi⟩
  obtain ⟨o, b, ho, hByte, hWrite⟩ := writebackIssuedByte hp hX hComplete stage subbox hIssue
    hb hh (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hk (hRow ▸ hr)
  rw [Nat.add_assoc, hRow, hCol] at hWrite
  exact ⟨stage, subbox, n, hn, o, b, hi, ho, hByte, hWrite⟩

/-- An issued O store has no effect for a row past the selected request's end, even when
a following request occupies the next packed row. -/
theorem writebackIssuedTail {X : Execution} (hp : Pre p l m) {i : EvId}
    {batch head tile x y k : Nat} (stage : Fin 2) (subbox : Fin 4)
    (hi : X.TensorStoreIssue i p.oMapAddress
      (writebackStoreSpec p l i.1 batch head tile stage subbox)) (hb : batch < p.batch)
    (hh : head < p.heads) (hr : p.qLength batch ≤ stageRow tile stage + y) :
    ∀ a bs, ¬ X.MemWrites (.async i (.write (.store x y k))) a bs := by
  intro a bs hw
  obtain ⟨o, addr, b, _, ⟨pc, he⟩, hl, -⟩ := hw
  obtain ⟨pc', he'⟩ := hi
  rw [he'] at he
  have hSpec := (Kind.tensorStore.inj (Event.mk.inj (Option.some.inj he)).2).2
  rw [← hSpec, writebackWriteLoc hp stage subbox x y k hb hh] at hl
  simp [Nat.not_lt.mpr hr] at hl

/-- Once the matching correction write is ordered before the source read, the completed
non-reducing O store writes that correction byte. -/
theorem writebackByteOfSource {X : Execution} {A : List Assumption} (hX : Consistent l kernel A m X)
    {i : EvId} {batch head tile x y k : Nat} (stage : Fin 2) (subbox : Fin 4)
    (hi : X.TensorStoreIssue i p.oMapAddress
      (writebackStoreSpec p l i.1 batch head tile stage subbox)) {o : TensorStore.Observation}
    {b : Byte} {src : Loc} {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (ho : X.tensorStores i = some o) (hw : TensorStore.writeByte o x y k = some b)
    (hl : TensorStore.readLoc (writebackStoreSpec p l i.1 batch head tile stage subbox) x y k =
      some src) (hSrc : SourceOrdered l X (.async i (.read (.store x y k))) src w a bs) :
    some b = wbyte a bs src := by
  obtain ⟨⟨addr, pc, he⟩, -⟩ := hX.store i o ho
  obtain ⟨pc', he'⟩ := hi
  rw [he'] at he
  have hSpec := (Kind.tensorStore.inj (Event.mk.inj (Option.some.inj he)).2).2
  exact hX.store_read_byte ho (by rw [← hSpec]; rfl) hw (hSpec ▸ hl) hSrc

end
end PTX.Kernels.TmlFa4Fwd.Epilogue
