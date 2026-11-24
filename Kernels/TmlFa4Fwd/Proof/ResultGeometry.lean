-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputGeometry
public import Lemmas.Arith.MixedRadix
public import Lemmas.Kernel.Memory
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd

/-- A valid row in a request is in the packed query allocation. -/
theorem Pre.packedRow_lt {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {b row : Nat} (hb : b < p.batch) (hr : row < p.qLength b) :
    p.qOffset b + row < p.totalQ := by
  have h := hp.qOffset_le_total (b := b + 1) (by omega)
  unfold Params.qLength at hr
  omega

variable {p : Params}

/-- A packed row has one valid request and request-local row. -/
theorem Pre.packedRow_inj {l : Launch} {m : Mem0} (hp : Pre p l m) {b b' row row' : Nat}
    (hb : b < p.batch) (hb' : b' < p.batch) (hr : row < p.qLength b) (hr' : row' < p.qLength b')
    (he : p.qOffset b + row = p.qOffset b' + row') : b = b' ∧ row = row' := by
  have hBefore {x x' r : Nat} (h : x < x') (hx' : x' < p.batch)
      (hr : r < p.qLength x) : p.qOffset x + r < p.qOffset x' := by
    have hOffset : p.qOffset (x + 1) ≤ p.qOffset x' :=
      hp.qOffset_mono (by omega) (Nat.le_of_lt hx')
    unfold Params.qLength at hr
    omega
  rcases Nat.lt_trichotomy b b' with h | rfl | h
  · have := hBefore h hb' hr
    omega
  · exact ⟨rfl, by omega⟩
  · have := hBefore h hb hr'
    omega

/-- Every valid O byte lies in the packed output region. -/
theorem outputByte_in {q h d k : Nat} (hq : q < p.totalQ) (hh : h < p.heads) (hd : d < 128)
    (hk : k < 4) :
    p.oRegion.Contains ((p.oLoc q h d).at k) := by
  have hrow : q * p.heads + h < p.totalQ * p.heads := by
    have hmul := Nat.mul_le_mul_right p.heads (show q + 1 ≤ p.totalQ by omega)
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  change Space.global = Space.global ∧ 0 = 0 ∧
    p.oBase ≤ p.oBase + 4 * ((q * p.heads + h) * 128 + d) + k ∧
    p.oBase + 4 * ((q * p.heads + h) * 128 + d) + k <
      p.oBase + 512 * p.heads * p.totalQ
  rw [show 512 * p.heads * p.totalQ = 512 * (p.totalQ * p.heads) by ring]
  exact ⟨rfl, rfl, by omega, by omega⟩

/-- The LSE stride may include padding. Only the first `totalQ` rows of each head are outputs. -/
theorem lseByte_in {q h k : Nat} (hq : q < p.totalQ) (hh : h < p.heads) (hk : k < 4) :
    p.lseRegion.Contains ((p.lseLoc q h).at k) := by
  have hmul := Nat.mul_le_mul_right p.lseStride (show h ≤ p.heads - 1 by omega)
  exact ⟨rfl, rfl, by simp only [Params.lseRegion, Params.lseLoc, globalLoc, Loc.at]; omega,
    by simp only [Params.lseRegion, Params.lseLoc, globalLoc, Loc.at]; omega⟩

/-- Distinct packed row, head, column or byte coordinates select distinct O bytes. -/
theorem outputByte_inj {q h d k q' h' d' k' : Nat} (hh : h < p.heads) (hh' : h' < p.heads)
    (hd : d < 128) (hd' : d' < 128) (hk : k < 4) (hk' : k' < 4)
    (eq : (p.oLoc q h d).at k = (p.oLoc q' h' d').at k') :
    q = q' ∧ h = h' ∧ d = d' ∧ k = k' := by
  have he := congrArg Loc.addr eq
  simp only [Params.oLoc, globalLoc, Loc.at] at he
  have hpack : q * p.heads + h = q' * p.heads + h' := by omega
  obtain ⟨hq, -⟩ := Nat.digits_of_eq hh hh' hpack
  subst q'
  exact ⟨rfl, by omega, by omega, by omega⟩

/-- Distinct in-range LSE coordinates, including the byte coordinate, do not alias. -/
theorem lseByte_inj {q h k q' h' k' : Nat} (hq : q < p.totalQ) (hq' : q' < p.totalQ)
    (hs : p.totalQ ≤ p.lseStride) (hk : k < 4) (hk' : k' < 4)
    (eq : (p.lseLoc q h).at k = (p.lseLoc q' h').at k') :
    q = q' ∧ h = h' ∧ k = k' := by
  have he := congrArg Loc.addr eq
  simp only [Params.lseLoc, globalLoc, Loc.at] at he
  have hpack : h * p.lseStride + q = h' * p.lseStride + q' := by omega
  obtain ⟨hh, -⟩ := Nat.digits_of_eq (by omega : q < p.lseStride)
    (by omega : q' < p.lseStride) hpack
  subst h'
  exact ⟨by omega, rfl, by omega⟩

/-- A valid LSE byte cannot alias any O byte. -/
theorem lseByte_apart_output {l : Launch} {m : Mem0} (hp : Pre p l m) {q h k : Nat}
    (hq : q < p.totalQ) (hh : h < p.heads) (hk : k < 4) :
    ¬ p.oRegion.Contains ((p.lseLoc q h).at k) := by
  intro ho
  have hl := lseByte_in hq hh hk
  rcases hp.separate.1 with h | h
  · exact (Nat.not_lt_of_ge (Nat.le_trans h hl.2.2.1)) ho.2.2.2
  · exact (Nat.not_lt_of_ge (Nat.le_trans h ho.2.2.1)) hl.2.2.2

/-- Writes confined to O and LSE cannot cover bytes of an input allocation. -/
theorem Pre.inputByte_unwritten {l : Launch} {m : Mem0} (hp : Pre p l m) {X : Execution}
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {region : Region}
    (hr : region ∈ p.inputRegions) {loc : Loc} (hLoc : region.Contains loc) {w : AsyncCopy.Ref}
    {a : Acc} {bytes : List Byte} (hWrite : X.MemWrites w a bytes) :
    ¬ a.Covers loc := by
  intro hCover
  rcases writes w a bytes loc hWrite hCover hLoc.1 with ho | hl
  · rcases (hp.separate.2 region hr).1 with h | h
    · exact (Nat.not_lt_of_ge (h.trans hLoc.2.2.1)) ho.2.2.2
    · exact (Nat.not_lt_of_ge (h.trans ho.2.2.1)) hLoc.2.2.2
  · rcases (hp.separate.2 region hr).2 with h | h
    · exact (Nat.not_lt_of_ge (h.trans hLoc.2.2.1)) hl.2.2.2
    · exact (Nat.not_lt_of_ge (h.trans hl.2.2.1)) hLoc.2.2.2

/-- The only scheduler reads are within cuQ, including its terminating sentinel. -/
theorem Pre.cuQ_protected {l : Launch} {m : Mem0} (hp : Pre p l m) {X : Execution}
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bytes, X.MemWrites w a bytes →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k) := by
  intro i hi k hk w a bs hw
  have hReg : ⟨p.cuQBase, 4 * (p.batch + 1)⟩ ∈ p.inputRegions := by
    simp [Params.inputRegions]
  have hLoc : Region.Contains ⟨p.cuQBase, 4 * (p.batch + 1)⟩
      ((globalLoc (p.cuQBase + 4 * i)).at k) := by
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [globalLoc, Loc.at] <;> omega
  exact hp.inputByte_unwritten writes hReg hLoc hw

/-- Any global byte outside the packed O region and the actual LSE elements is preserved. -/
theorem outputFrame {l : Launch} {m0 : Mem0} {x : Execution} {m : FinalMem} (hf : IsFinal l m0 x m)
    (writes : ∀ w a bs addr, x.MemWrites w a bs → a.Covers addr → addr.space = .global →
      p.oRegion.Contains addr ∨
        ∃ q < p.totalQ, ∃ h < p.heads, ∃ k < 4, addr = (p.lseLoc q h).at k) {addr : Loc}
    (hGlobal : addr.space = .global) (hO : ¬ p.oRegion.Contains addr)
    (hLse : ∀ q < p.totalQ, ∀ h < p.heads, ∀ k < 4, addr ≠ (p.lseLoc q h).at k) :
    m addr = m0 addr := by
  apply hf.unwritten
  intro w a bs hw hc
  rcases writes w a bs addr hw hc hGlobal with ho | ⟨q, hq, h, hh, k, hk, eq⟩
  · exact hO ho
  · exact hLse q hq h hh k hk eq

/-- Interpret the final output bytes as FP32 and apply the global memory frame. -/
theorem post_of_bytes {l : Launch} {m0 : Mem0} {x : Execution} {m : FinalMem}
    (hf : IsFinal l m0 x m)
    (writes : ∀ w a bs addr, x.MemWrites w a bs → a.Covers addr → addr.space = .global →
      p.oRegion.Contains addr ∨
        ∃ q < p.totalQ, ∃ h < p.heads, ∃ k < 4, addr = (p.lseLoc q h).at k)
    (o : ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ d < 128, ∀ k < 4,
      m ((p.oLoc (p.qOffset b + row) h d).at k) =
        some (some (.float .f32 (attention p b h row d), k)))
    (lseBytes : ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ k < 4,
      m ((p.lseLoc (p.qOffset b + row) h).at k) = some (some (.float .f32 (lse p b h row), k))) :
    Post p m0 m := by
  refine ⟨?_, fun _ => outputFrame hf writes⟩
  intro b hb h hh row hr
  exact ⟨fun d hd => memFloat_float (o b hb h hh row hr d hd),
    memFloat_float (lseBytes b hb h hh row hr)⟩

end PTX.Kernels.TmlFa4Fwd
