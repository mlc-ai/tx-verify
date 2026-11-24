-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2ReadTracking
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.CacheGatherPayload
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg2Events

@[expose] public section

/-! # Finite inputs from the raw gather ring -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2

open PTX PTX.Proof PTX.Flow PTX.AsyncCopy

/-- One byte of a gathered row, retaining the tensor map's typed zero-fill representation. -/
def gatheredInput (P : Params) (L : Launch) (issuer block pos off : Nat) : Option Byte :=
  let batch := Wg1Tma.eOf L issuer
  let query := Wg1Tma.qOf L issuer
  let extra := FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen batch)
  let slot := slotPos (P.topkLen batch) block (pos / 2) (pos % 2)
  if Wg1Tma.validBit P L issuer block (pos / 2) (pos % 2) then
    inputByte (rowBytes P batch query extra slot off)
  else some (b32 0, off % 4)

private theorem assembled {bs : List (Option Byte)} {size : Nat} {bytes : Nat → Option Byte}
    (hlen : bs.length = size) (hread : ∀ k < size, bs[k]? = some (bytes k)) :
    bs = List.ofFn (fun k : Fin size => bytes k.val) := by
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_ofFn]
  by_cases hk : k < size
  · rw [dite_eq_left hk]
    exact hread k hk
  · rw [dite_eq_right hk, List.getElem?_eq_none (by omega)]

private theorem assembled_valid {bs : List (Option Byte)} {size : Nat} {row : Nat → Nat}
    (hlen : bs.length = size) (hread : ∀ k < size, bs[k]? = some (inputByte (row k))) :
    bs = (List.ofFn fun k : Fin size => row k.val).map inputByte := by
  rw [assembled hlen hread]
  apply List.ext_getElem?
  intro k
  rw [List.getElem?_map, List.getElem?_ofFn, List.getElem?_ofFn]
  split <;> rfl

private theorem assembled_zero {bs : List (Option Byte)} {size off : Nat}
    (hlen : bs.length = size) (halign : off % 4 = 0)
    (hread : ∀ k < size, bs[k]? = some (some (b32 0, (off + k) % 4))) :
    bs = List.ofFn (fun k : Fin size => some (b32 0, k.val % 4)) := by
  apply assembled (bytes := fun k => some (b32 0, k % 4)) hlen
  intro k hk
  rw [hread k hk, Nat.add_mod, halign, Nat.zero_add, Nat.mod_mod]

private theorem rowBytes_lt {P : Params} (batch query : Nat) (extra : Bool) (slot off : Nat) :
    rowBytes P batch query extra slot off < 256 := by
  unfold rowBytes
  split
  · exact Fin.isLt _
  · exact Fin.isLt _

variable {P : Params} {L : Launch}

/-- A scale word supplied by one gathered row has four finite ue8m0 bytes. -/
theorem finite_scale_of_gathered {mem0 : Mem0} {issuer block pos : Nat} {bs : List (Option Byte)}
    {j : Fin 4} (hpre : Pre P L mem0) (hb : Wg1Tma.eOf L issuer < P.b)
    (hq : Wg1Tma.qOf L issuer < P.s_q) (hlen : bs.length = 4)
    (hread : ∀ k < 4, bs[k]? = some (gatheredInput P L issuer block pos (512 + 4 * j.val + k))) :
    (∃ ns : List Nat, ns.length = 4 ∧ (∀ b ∈ ns, b < 255) ∧ bs = ns.map inputByte) ∨
      bs = zeroWord := by
  cases hv : Wg1Tma.validBit P L issuer block (pos / 2) (pos % 2)
  · right
    have hz := assembled_zero hlen (off := 512 + 4 * j.val) (by omega)
      (fun k hk => by simpa [gatheredInput, hv] using hread k hk)
    exact hz.trans (show (List.ofFn fun k : Fin 4 => some (b32 0, k.val % 4)) = zeroWord
      from by decide)
  · left
    let batch := Wg1Tma.eOf L issuer
    let query := Wg1Tma.qOf L issuer
    let extra := FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen batch)
    let slot := slotPos (P.topkLen batch) block (pos / 2) (pos % 2)
    let row := rowBytes P batch query extra slot
    have hvalid : slotValid P batch query extra slot := Result.RawGather.coord_valid_slot hv
    have hvalues : ∀ k < 4, bs[k]? = some (inputByte (row (512 + 4 * j.val + k))) := by
      intro k hk
      simpa [gatheredInput, hv, row, batch, query, extra, slot] using hread k hk
    refine ⟨List.ofFn (fun k : Fin 4 => row (512 + 4 * j.val + k.val)), by simp, ?_,
      assembled_valid (row := fun k => row (512 + 4 * j.val + k)) hlen hvalues⟩
    intro n hn
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hn
    have ho : 4 * j.val + k.val < 16 := by have := j.isLt; have := k.isLt; omega
    have ht : (32 * (4 * j.val + k.val)) / 32 = 4 * j.val + k.val := by omega
    have hne := hpre.ue8m0Ok _ hb _ hq _ _ hvalid (32 * (4 * j.val + k.val)) (by omega)
    rw [ht, ← Nat.add_assoc] at hne
    have hlt := rowBytes_lt (P := P) batch query extra slot (512 + 4 * j.val + k.val)
    change row (512 + 4 * j.val + k.val) < 256 at hlt
    change row (512 + 4 * j.val + k.val) ≠ 255 at hne
    omega

/-- An eight-byte value word supplied by one gathered row has finite e4m3 bytes. -/
theorem finite_raw_of_gathered {mem0 : Mem0} {issuer block pos off : Nat} {bs : List (Option Byte)}
    (hpre : Pre P L mem0) (hb : Wg1Tma.eOf L issuer < P.b) (hq : Wg1Tma.qOf L issuer < P.s_q)
    (hlen : bs.length = 8) (halign : off % 4 = 0) (hbound : off + 8 ≤ 512)
    (hread : ∀ k < 8, bs[k]? = some (gatheredInput P L issuer block pos (off + k))) :
    (∃ ns : List Nat, ns.length = 8 ∧ (∀ b ∈ ns, b < 256 ∧ b ≠ 127 ∧ b ≠ 255) ∧
      bs = ns.map inputByte) ∨ bs = zeroWord ++ zeroWord := by
  cases hv : Wg1Tma.validBit P L issuer block (pos / 2) (pos % 2)
  · right
    have hz := assembled_zero hlen halign
      (fun k hk => by simpa [gatheredInput, hv] using hread k hk)
    exact hz.trans (show (List.ofFn fun k : Fin 8 => some (b32 0, k.val % 4)) =
      zeroWord ++ zeroWord from by decide)
  · left
    let batch := Wg1Tma.eOf L issuer
    let query := Wg1Tma.qOf L issuer
    let extra := FlashMlaSparseDecodeH64.isExtraBlock block (P.topkLen batch)
    let slot := slotPos (P.topkLen batch) block (pos / 2) (pos % 2)
    let row := rowBytes P batch query extra slot
    have hvalid : slotValid P batch query extra slot := Result.RawGather.coord_valid_slot hv
    have hvalues : ∀ k < 8, bs[k]? = some (inputByte (row (off + k))) := by
      intro k hk
      simpa [gatheredInput, hv, row, batch, query, extra, slot] using hread k hk
    refine ⟨List.ofFn (fun k : Fin 8 => row (off + k.val)), by simp, ?_,
      assembled_valid (row := fun k => row (off + k)) hlen hvalues⟩
    intro n hn
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hn
    have := k.isLt
    exact ⟨rowBytes_lt batch query extra slot _, hpre.e4m3Ok _ hb _ hq _ _ hvalid _ (by omega)⟩

/-- Reading from the recorded byte of a gather recovers the selected cache byte or typed fill. -/
theorem gathered_read_byte {mem0 : Mem0} {X : Execution} {g i : Nat} {d : Wg1Tma.D} {tile : Fin 16}
    {load : EvId} {a : Acc} {bs : List (Option Byte)} {k : Nat} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d)))
    (hSite : d.site = .issue tile) (hread : X.Reads load a bs) (hk : k < a.size) (row : Fin 4)
    (off : Fin 528)
    (hsrc : X.rf (.thread load) k =
      some (.async (g, i) (.write (.load (off.val / 4) row.val (off.val % 4))))) :
    bs[k]? = some (gatheredInput P L g d.block (Wg1Tma.coordPos tile.val row.val) off.val) := by
  let col : Fin 144 := ⟨off.val / 4, by have := off.isLt; omega⟩
  let byte : Fin 4 := ⟨off.val % 4, Nat.mod_lt _ (by decide)⟩
  have hrf := (hX.rf (.thread load) a bs (.inl hread)).2 k hk
  rw [hsrc] at hrf
  obtain ⟨a', _, ⟨o, address, value, ho, hi, _, hw, hsiz, rfl, _⟩, hc, hv⟩ := hrf
  have hzero : (a.loc.at k).addr - a'.loc.addr = 0 := by
    unfold Acc.Covers Loc.InRange at hc
    omega
  have hcol : col.val < 132 := by
    have := off.isLt
    dsimp [col]
    omega
  have hp := Result.RawGather.gathered_byte hpre hX hs hState hSite ho hi row col byte hcol hw
  have hOff : 4 * col.val + byte.val = off.val := by dsimp [col, byte]; omega
  rw [hOff] at hp
  simp only [wbyte, hzero, List.getElem?_cons_zero] at hv
  rw [hv]
  congr 1
  unfold gatheredInput
  dsimp only at hp ⊢
  split_ifs at hp ⊢ with h
  · exact congrArg some hp
  · exact congrArg some hp

/-- The exact trace write supplying every byte of the word in the dequantizer's raw slot. -/
def GatherSources (P : Params) (L : Launch) (X : Execution) (load : EvId)
    (issuer block : Nat) (row : Fin 4) (off width : Nat) : Prop :=
  let pos := rawRow L load.1 row.val
  let tile : Fin 16 := ⟨pos / 4, by
    have hb := rawRow_lt (L := L) (g := load.1) (lr := row.val) row.isLt
    change pos < 64 at hb
    omega⟩
  ∃ (i : Nat) (d : Wg1Tma.D),
    Frame.stateAt (Machine.code P L) X issuer i = some (some (.tma d)) ∧
    d.site = .issue tile ∧ d.block = block ∧
    ∀ k < width, X.rf (.thread load) k =
      some (.async (issuer, i) (.write (.load ((off + k) / 4) (pos % 4) ((off + k) % 4))))

/-- Exact gather sources determine every returned byte of the load window. -/
theorem gather_window_bytes {mem0 : Mem0} {X : Execution} {load : EvId} {issuer block off : Nat}
    {row : Fin 4} {a : Acc} {bs : List (Option Byte)} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hread : X.Reads load a bs)
    (hsources : GatherSources P L X load issuer block row off a.size) (hend : off + a.size ≤ 528) :
    ∀ k < a.size,
      bs[k]? = some (gatheredInput P L issuer block (rawRow L load.1 row.val) (off + k)) := by
  intro k hk
  let pos := rawRow L load.1 row.val
  let fourRow : Fin 4 := ⟨pos % 4, Nat.mod_lt _ (by decide)⟩
  let offset : Fin 528 := ⟨off + k, by omega⟩
  obtain ⟨i, d, hState, hSite, rfl, hsrc⟩ := hsources
  have h := gathered_read_byte hpre hX hs hState hSite hread hk fourRow offset (hsrc k hk)
  have hpos : Wg1Tma.coordPos (pos / 4) (pos % 4) = pos := by
    unfold Wg1Tma.coordPos
    omega
  change bs[k]? = some (gatheredInput P L issuer d.block
    (Wg1Tma.coordPos (pos / 4) (pos % 4)) (off + k)) at h
  rwa [hpos] at h

/-- Exact current-generation raw-ring sources discharge the finite-input obligation for the
actual dequantizer load, with no additional assumptions about the loaded byte values. -/
theorem finiteInput_of_gather_sources {mem0 : Mem0} {X : Execution} {g i issuer : Nat} {d : D}
    {e : Event} {u : TState} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hb : Wg1Tma.eOf L issuer < P.b)
    (hq : Wg1Tma.qOf L issuer < P.s_q) (he : X.get (g, i) = some e)
    (hf : (Machine.machine P L g).Fired (some (.wg2 d)) e (some u))
    (hscale : ∀ r j, d.site = .scale r j →
      GatherSources P L X (g, i) issuer d.block r (512 + 4 * j.val) 4)
    (hraw : ∀ r s, d.site = .raw r s →
      GatherSources P L X (g, i) issuer d.block r (elemByte L g s.val 0) 8) :
    FiniteInput d e := by
  have hread (a : Acc) (bs : List (Option Byte)) (hr : e.kind = .rd a bs) :
      X.Reads (g, i) a bs := by
    obtain ⟨tag, kd⟩ := e
    cases hr
    exact ⟨tag, he⟩
  have hf' : (machine P L g).Fired (some (.inr d)) e (some u) := hf
  cases hd : d.site
  case scale r j =>
    simp only [FiniteInput, hd]
    intro a bs hk
    obtain ⟨a', bs', hk', _, hsize⟩ := fired_scale_event hpre hd hf'
    obtain ⟨rfl, rfl⟩ := Kind.rd.inj (hk.symm.trans hk')
    have hr := hread a bs hk
    have hlen := (hX.rf (.thread (g, i)) a bs (.inl hr)).1.trans hsize
    have hs' : GatherSources P L X (g, i) issuer d.block r (512 + 4 * j.val) a.size := by
      simpa only [hsize] using hscale r j hd
    have bh : 512 + 4 * j.val + a.size ≤ 528 := by have := j.isLt; omega
    exact finite_scale_of_gathered hpre hb hq hlen
      (fun k h => gather_window_bytes hpre hX hs hr hs' bh k (by omega))
  case raw r s =>
    simp only [FiniteInput, hd]
    intro a bs hk
    obtain ⟨a', bs', hk', _, hsize⟩ := fired_raw_event hpre hd hf'
    obtain ⟨rfl, rfl⟩ := Kind.rd.inj (hk.symm.trans hk')
    have hr := hread a bs hk
    have hlen := (hX.rf (.thread (g, i)) a bs (.inl hr)).1.trans hsize
    have hs' : GatherSources P L X (g, i) issuer d.block r (elemByte L g s.val 0) a.size := by
      simpa only [hsize] using hraw r s hd
    have hlim := elemByte_lt (L := L) (g := g) (s := s.val) (e := 7) s.isLt (by decide)
    have bh : elemByte L g s.val 0 + 8 ≤ 512 := by
      simp only [elemByte, quantBytes, Nat.add_zero] at hlim ⊢
      omega
    have halign : elemByte L g s.val 0 % 4 = 0 := by
      simp only [elemByte, elemsPerStep, rawBytesPerThread]
      omega
    exact finite_raw_of_gathered hpre hb hq hlen halign bh
      (fun k h => gather_window_bytes hpre hX hs hr hs' (by omega) k (by omega))
  all_goals simp [FiniteInput, hd]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg2
