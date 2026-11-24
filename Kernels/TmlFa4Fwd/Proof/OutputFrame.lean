-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.EpilogueComplete
public import Kernels.TmlFa4Fwd.Proof.EpilogueOutputWrites
public import Kernels.TmlFa4Fwd.Proof.Thread.GlobalWrites
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
public import Kernels.TmlFa4Fwd.Proof.OutputPinned
public import Lemmas.Step.ReadSource
public import Lemmas.TensorStore.StoreWrite

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX

noncomputable section

/-- Every global write covers a packed O byte or an actual LSE element byte. -/
def OutputFootprint (p : Params) (X : Execution) : Prop :=
  ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
    p.oRegion.Contains loc ∨
      ∃ q < p.totalQ, ∃ h < p.heads, ∃ k < 4, loc = (p.lseLoc q h).at k

/-- The output footprint protects every input allocation, regardless of when a write occurs. -/
theorem OutputFootprint.input_unwritten {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (h : OutputFootprint p X)
    {region : Region} (hr : region ∈ p.inputRegions) {loc : Loc} (hl : region.Contains loc)
    {w : AsyncCopy.Ref} {a : Acc} {bytes : List Byte} (hw : X.MemWrites w a bytes) :
    ¬ a.Covers loc := by
  apply hp.inputByte_unwritten _ hr hl hw
  intro w a bs loc hw hCover hSpace
  rcases h w a bs loc hw hCover hSpace with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
  · exact .inl ho
  · exact .inr (lseByte_in hq hh hk)

/-- The footprints of pending global output writes obey the same frame. -/
def OutputIntentFootprint (p : Params) (X : Execution) : Prop :=
  ∀ w a loc, X.Intent w a true → a.Covers loc → loc.space = .global →
    p.oRegion.Contains loc ∨
      ∃ q < p.totalQ, ∃ h < p.heads, ∃ k < 4, loc = (p.lseLoc q h).at k

theorem OutputIntentFootprint.performed {p : Params} {X : Execution}
    (h : OutputIntentFootprint p X) : OutputFootprint p X :=
  fun w a _ loc hw => h w a loc hw.intent

private theorem Region.Apart.not_both {a b : Region} {loc : Loc} (h : a.Apart b)
    (ha : a.Contains loc) (hb : b.Contains loc) : False := by
  rcases h with h | h
  · exact (Nat.not_lt_of_ge (h.trans hb.2.2.1)) ha.2.2.2
  · exact (Nat.not_lt_of_ge (h.trans ha.2.2.1)) hb.2.2.2

/-- **The write frame excludes the input assumption's undefined behaviour**: every global
write is in the O or LSE region, which every parameter set of the launch keeps apart from its
input arrays. -/
theorem OutputIntentFootprint.noInputWrite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (h : OutputIntentFootprint p X) :
    ¬ Assumptions.inputReadOnly.ub l m X := by
  rintro ⟨w, a, loc, hw, hc, P, hP, r, hr, hl⟩
  obtain ⟨hO, hL⟩ := hp.outputs_pinned hP
  rcases h w a loc hw hc hl.1 with ho | ⟨q, hq, head, hh, k, hk, rfl⟩
  · exact (hP.separate.2 r hr).1.not_both (hO ▸ ho) hl
  · exact (hP.separate.2 r hr).2.not_both (hL ▸ lseByte_in hq hh hk) hl

/-- Physical output boxes described by the selected work item. -/
def OutputBoxSpec (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∀ i addr s, X.TensorStoreIssue i addr s →
    ∃ batch < p.batch, ∃ head < p.heads, ∃ (tile : Nat) (stage : Fin 2) (box : Fin 4),
      s = Epilogue.writebackStoreSpec p l i.1 batch head tile stage box

/-- Scalar global output writes address a whole LSE word. -/
def LseWriteSpec (p : Params) (X : Execution) : Prop :=
  ∀ i a bytes, X.Writes i a bytes → a.loc.space = .global →
    ∃ row < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc row head ∧ a.size = 4

private theorem coveredLseByte {p : Params} {a : Acc} {loc : Loc} {q head : Nat}
    (hAt : a.loc = p.lseLoc q head) (hSize : a.size = 4) (hc : a.Covers loc) :
    ∃ k < 4, loc = (p.lseLoc q head).at k := by
  let k := loc.addr - a.loc.addr
  have hk : k < 4 := by
    have hb := hc.2.2.2
    dsimp [k]
    omega
  have heq : loc = a.loc.at k := by
    obtain ⟨sp, cta, addr⟩ := loc
    rcases a with ⟨⟨baseSpace, baseCTA, baseAddr⟩, _, _, _, _, _, _⟩
    obtain ⟨h₁, h₂, h₃, _⟩ := hc
    change Loc.mk sp cta addr = Loc.mk baseSpace baseCTA (baseAddr + k)
    change baseAddr ≤ addr at h₃
    have hK : k = addr - baseAddr := rfl
    rw [Loc.mk.injEq]
    exact ⟨h₁, h₂, by omega⟩
  exact ⟨k, hk, heq.trans (congrArg (fun a => a.at k) hAt)⟩

/-- Each global write covers a word of LSE or individual bytes of O. -/
theorem outputIntentShape {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hLse : LseWriteSpec p X) (hTensor : OutputBoxSpec p l X)
    {w : AsyncCopy.Ref} {a : Acc} (hw : X.Intent w a true) (hs : a.loc.space = .global) :
    (∃ q < p.totalQ, ∃ head < p.heads, a.loc = p.lseLoc q head ∧ a.size = 4) ∨
      (a.size = 1 ∧ p.oRegion.Contains a.loc) := by
  rcases Thread.globalWriteSource hX hw hs with
      ⟨i, bytes, _, he⟩ | ⟨i, x, y, k, addr, s, _, he, hLoc, hSize⟩
  · exact .inl (hLse i a bytes he hs)
  · obtain ⟨batch, hb, head, hh, tile, stage, box, rfl⟩ := hTensor i addr s he
    have hDest := Epilogue.writebackWriteLoc hp (g := i.1) (tile := tile) stage box x y k hb hh
    simp only at hDest
    rw [hDest] at hLoc
    by_cases h : x < 32 ∧ y < 128 ∧ k < 4 ∧ Epilogue.stageRow tile stage + y < p.qLength batch
    · rw [ite_eq_left h, Option.some.injEq] at hLoc
      have hRow := hp.packedRow_lt hb h.2.2.2
      have hCol : 32 * box.val + x < 128 := by have := box.isLt; omega
      exact .inr ⟨hSize, hLoc ▸ outputByte_in hRow hh hCol h.2.2.1⟩
    · simp [h] at hLoc

/-- The observed output descriptors and LSE addresses determine the global write frame. -/
theorem outputIntentFootprint_of_sites {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hLse : LseWriteSpec p X) (hTensor : OutputBoxSpec p l X) :
    OutputIntentFootprint p X := by
  intro w a loc hw hc hs
  have hSpace : a.loc.space = .global := hc.1.symm.trans hs
  rcases outputIntentShape hp hX hLse hTensor hw hSpace with
    ⟨q, hq, head, hh, hAt, hSize⟩ | ⟨hSize, ho⟩
  · exact .inr ⟨q, hq, head, hh, coveredLseByte hAt hSize hc⟩
  · exact .inl (Acc.loc_of_one hc hSize ▸ ho)

/-- Global output write footprints are either disjoint or exactly equal, even before completion. -/
theorem outputWrites_sameFootprint {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l Decoded.kernel A m X)
    (hLse : LseWriteSpec p X) (hTensor : OutputBoxSpec p l X)
    {w f : AsyncCopy.Ref} {a b : Acc} (hw : X.Intent w a true) (hf : X.Intent f b true)
    (hs : a.loc.space = .global) (hOverlap : a.Overlap b) : a.SameFootprint b := by
  obtain ⟨loc, ha, hb⟩ := hOverlap
  have hGlobal : b.loc.space = .global := hb.1.symm.trans (ha.1.trans hs)
  rcases outputIntentShape hp hX hLse hTensor hw hs with
    ⟨q, hq, h, hh, hAt, hSize⟩ | ⟨hSize, ho⟩
  · obtain ⟨k, hk, hLoc⟩ := coveredLseByte hAt hSize ha
    rcases outputIntentShape hp hX hLse hTensor hf hGlobal with
      ⟨q', hq', h', hh', hAt', hSize'⟩ | ⟨hSize', ho⟩
    · obtain ⟨k', hk', hLoc'⟩ := coveredLseByte hAt' hSize' hb
      obtain ⟨rfl, rfl, _⟩ := lseByte_inj hq hq' hp.lseStride hk hk' (hLoc.symm.trans hLoc')
      exact ⟨hAt.trans hAt'.symm, hSize.trans hSize'.symm⟩
    · have ho' : p.oRegion.Contains ((p.lseLoc q h).at k) :=
        hLoc ▸ (Acc.loc_of_one hb hSize' ▸ ho)
      exact (lseByte_apart_output hp hq hh hk ho').elim
  · have ho' : p.oRegion.Contains loc := Acc.loc_of_one ha hSize ▸ ho
    rcases outputIntentShape hp hX hLse hTensor hf hGlobal with
      ⟨q, hq, h, hh, hAt, hSize'⟩ | ⟨hSize', _⟩
    · obtain ⟨k, hk, hLoc⟩ := coveredLseByte hAt hSize' hb
      exact (lseByte_apart_output hp hq hh hk (hLoc ▸ ho')).elim
    · exact ⟨(Acc.loc_of_one ha hSize).trans (Acc.loc_of_one hb hSize').symm,
        hSize.trans hSize'.symm⟩

/-- The scheduled CTA's completed store writes every byte of each legal O element. -/
theorem outputHasWriter {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hComplete : Complete l X) (hFrame : OutputFootprint p X)
    {batch head row col k : Nat}
    (hb : batch < p.batch) (hh : head < p.heads)
    (hr : row < p.qLength batch) (hc : col < 128) (hk : k < 4) :
    ∃ w a bytes, X.MemWrites w a bytes ∧
      a.Covers ((p.oLoc (p.qOffset batch + row) head col).at k) := by
  let cta := workItem p batch (row / 256) head
  let g := cta * l.block + 416
  obtain ⟨hCta, hLow, hHigh, hCoords⟩ := hp.row_workItem hb hr hh
  have hThread : g < l.threads := by
    change cta * l.block + 416 < l.grid * l.block
    rw [hp.block]
    omega
  have hDiv : g / l.block = cta := by
    dsimp [g]
    rw [hp.block]
    omega
  have hWarp : Prologue.warpIndex l g = 13 := by
    dsimp [Prologue.warpIndex, g]
    rw [hp.block]
    omega
  have hWork : g / l.block < tilePrefix p p.batch * p.heads := by
    rw [hDiv]
    exact hHigh.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  have hProtected : Epilogue.DrainCuQProtected p X := hp.cuQ_protected (by
    intro w a bs loc hw hc hl
    rcases hFrame w a bs loc hw hc hl with ho | ⟨q, hq, h, hh, k, hk, rfl⟩
    · exact .inl ho
    · exact .inr (lseByte_in hq hh hk))
  have hProgram := Epilogue.warp13Program hp hX hComplete hThread hWarp hProtected
  obtain ⟨selected, hSelected, hStart, hEnd, hTrace⟩ := hProgram.1 hWork
  rw [hDiv] at hStart hEnd hTrace
  obtain ⟨chosen, _, hUnique⟩ := tileBatch_existsUnique p (hDiv ▸ hWork)
  have hBatch := (hUnique selected ⟨hSelected, hStart, hEnd⟩).trans
    (hUnique batch ⟨hb, hLow, hHigh⟩).symm
  subst selected
  have hAssigned : Epilogue.assignedCoordinates p batch cta = (row / 256, head) := hCoords
  obtain ⟨j, written, suffix, hDrop, _, hEvents⟩ := hTrace 0 (by decide)
  change written.filter (fun e => Epilogue.writebackSucceeded e.kind) =
    Epilogue.writebackRemaining p l (warpLane l g 0) batch
      (Epilogue.assignedCoordinates p batch cta).2
      (Epilogue.assignedCoordinates p batch cta).1 (some (.ready 0)) at hEvents
  rw [hAssigned] at hEvents
  obtain ⟨stage, box, n, hn, o, byte, hi, ho, hByte, hWrite⟩ :=
    Epilogue.writebackTileByte hp hX hComplete hDrop hEvents hb hh hr hc hk
  refine ⟨_, _, _, hWrite, ?_⟩
  exact ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩

/-- A completed byte value has at least one writer, and every covering writer agrees with it. -/
def OutputByte (X : Execution) (loc : Loc) (value : Byte) : Prop :=
  (∃ w a bytes, X.MemWrites w a bytes ∧ a.Covers loc) ∧
    ∀ w a bytes, X.MemWrites w a bytes → a.Covers loc → wbyte a bytes loc = some value

/-- The final byte uses the agreed value even when several lanes issued the same output box. -/
theorem OutputByte.in_final {K : Kernel} {A : List Assumption} {l : Launch} {m : Mem0}
    {X : Execution} {out : FinalMem} (hX : Consistent l K A m X)
    (hf : IsFinal l m X out) {loc : Loc} {value : Byte} (h : OutputByte X loc value) :
    out loc = some (some value) := by
  obtain ⟨ws, hws⟩ := Step.writers_finite hX
  obtain ⟨⟨w, a, bs, hw, hc⟩, hv⟩ := h
  exact hf.of_agree (fun w a b hw _ => hws w a b hw) hw hc hv

/-- The per-byte output facts and write frame assemble into the declared kernel result. -/
theorem postOfOutputBytes {p : Params} {l : Launch} {m : Mem0} {A : List Assumption}
    {X : Execution} {out : FinalMem} (hX : Consistent l Decoded.kernel A m X)
    (hf : IsFinal l m X out) (hFrame : OutputFootprint p X)
    (hO : ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ d < 128, ∀ k < 4,
      OutputByte X ((p.oLoc (p.qOffset b + row) h d).at k)
        ((Value.float .f32 (attention p b h row d)).byteAt k))
    (hLse : ∀ b < p.batch, ∀ h < p.heads, ∀ row < p.qLength b, ∀ k < 4,
      OutputByte X ((p.lseLoc (p.qOffset b + row) h).at k)
        ((Value.float .f32 (lse p b h row)).byteAt k)) :
    Post p m out := by
  exact post_of_bytes hf hFrame
    (fun b hb h hh row hr d hd k hk => (hO b hb h hh row hr d hd k hk).in_final hX hf)
    (fun b hb h hh row hr k hk => (hLse b hb h hh row hr k hk).in_final hX hf)

end
end PTX.Kernels.TmlFa4Fwd
