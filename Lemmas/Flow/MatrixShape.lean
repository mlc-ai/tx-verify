-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Matrix
public import Lemmas.Flow.Step.SiteShape

@[expose] public section

/-! # Shapes of the events of warp matrix instructions (`site_shape`)

A proof tool. Inversion lemmas in the form `site_shape` applies (`P e` from `P` of the event the
instruction fires, `Step/SiteShape.lean`), for `mma.sync`, `movmatrix`, `ldmatrix` and
`stmatrix`. `site_shape` has no class for `Op.matrix`: a kernel registers the lemmas through the
hook `shape_inv`, e.g.

```
macro_rules
  | `(tactic| shape_inv $hf) => `(tactic| first
      | refine PTX.Flow.shape_mma $hf rfl rfl ?_ ?_ ?_
      | refine PTX.Flow.shape_ldmatrix_rd $hf hat.2.1 rfl rfl ?_ rfl ?_ ?_ ?_
      | refine PTX.Flow.shape_ldmatrix_mx $hf hat.2.1 rfl rfl ?_ rfl ?_ hat.2.2.1 ?_ ?_)
```

As for `tcgen05.alloc`, the sub-step selects the lemma of a two-event instruction, so it is the
argument after `hf` (`hat.2.1` at a site).

* `shape_mma`, `shape_movmatrix`: the matrix event with the bytes the lane contributes (`hown`,
  from the register facts by `mmaOwn_srcs`, `mmaOwn_regs`, `regBytes_srcs`, `regBytes_regs`).
* `shape_ldmatrix_rd` (sub-step 0): the read of the 16-byte row at the location `matrixRowLoc`
  gives (`matrixRowLoc_b32` for a 32-bit address register); `shape_ldmatrix_rdM` keeps the
  condition of its undefined behaviour instead. `shape_ldmatrix_mx` (sub-step 1): the matrix
  event contributing the bytes read.
* `shape_stmatrix_mx` (sub-step 0): the matrix event with the bytes of the source registers.
  `shape_stmatrix_wr` (sub-step 1): the write of the received bytes to the 16-byte row;
  `shape_stmatrix_wrM` keeps the condition of its undefined behaviour.
* `regs_of_live`: the register reads of these lemmas from a `factsFrom` table.

The hypotheses `hrule` (`MatrixInstr.rule`, by `rfl` for a literal instruction) and `hblk` (the
CTA size is a multiple of 32) exclude the instruction's `noRule` behaviour. -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat} {e : Event}
  {o : Option TState} {P : Event → Prop}

/-- The registers `rs`, all live in a `factsFrom` table that holds, have the table's values: the
register hypothesis of `mmaOwn_regs`, `mmaOwn_srcs`, `regBytes_regs` and `regBytes_srcs`. -/
theorem regs_of_live {R : Nat → Option Value} {live : List Nat} {val : Nat → Value}
    {rs : List Nat} (hF : Holds R (factsFrom live val)) (hlive : ∀ r ∈ rs, r ∈ live) :
    ∀ r ∈ rs, R r = some (val r) :=
  fun r hr => regs_of_factsFrom hF (hlive r hr)

/-- `mma.sync` whose A, B and C registers contribute the bytes `own`: its matrix event with
those bytes and any received bytes. -/
theorem shape_mma {i : MatrixInstr} {s : MmaSpec} {own : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hop : i.op = .mma s)
    (hrule : i.rule = some .threadMma) (hblk : L.block % 32 = 0)
    (hown : mmaOwn L g t s i.srcs = .ok own)
    (hP : ∀ recv, P ⟨pc, .matrix (.mma s) own recv⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [matrixTmpl_mma hblk hrule hop, hown] at hf'
  obtain ⟨recv, rfl, -⟩ := hf'
  exact hP recv

/-- `movmatrix d, a` whose source contributes the bytes `own`: its matrix event with those bytes
and any received bytes. -/
theorem shape_movmatrix {i : MatrixInstr} {d : Nat} {a : Opnd} {own : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hop : i.op = .transpose)
    (hd : i.dsts = [d]) (hs : i.srcs = [a]) (hblk : L.block % 32 = 0)
    (hown : regBytes L g t 32 i.srcs = .ok own)
    (hP : ∀ recv, P ⟨pc, .matrix .transpose own recv⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [hs] at hown
  rw [matrixTmpl_transpose hblk hop hd hs, hown] at hf'
  obtain ⟨recv, rfl, -⟩ := hf'
  exact hP recv

/-- `ldmatrix`, sub-step 0 of a lane that supplies a row, with the condition of its undefined
behaviour kept: the read of the 16-byte row `matrixRowLoc` gives, or undefined behaviour when it
gives none (an address outside the thread's shared window, or not a multiple of 16). -/
theorem shape_ldmatrix_rdM {i : MatrixInstr} {m : MatrixMove}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 0)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = false) (hsup : laneOf L g < m.num * m.rows)
    (hP : ∀ loc (bs : List (Option Byte)), matrixRowLoc L g t i = .ok loc → bs.length = 16 →
      P ⟨pc, .rd { loc := loc, size := 16 } bs⟩)
    (hub : ∀ f, matrixRowLoc L g t i = .error f → P ⟨pc, .ub f⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [matrixTmpl_move hblk hrule hop, matrixMoveTmpl_load_rd hst hsup hs] at hf'
  cases hloc : matrixRowLoc L g t i with
  | error f =>
    rw [hloc] at hf'
    rw [hf'.1]
    exact hub f hloc
  | ok loc =>
    rw [hloc] at hf'
    obtain ⟨bs, hl, rfl, -⟩ := hf'
    exact hP loc bs hloc hl

/-- `ldmatrix`, sub-step 0 of a lane that supplies a row at `loc`: a read of the 16 bytes at
`loc`. -/
theorem shape_ldmatrix_rd {i : MatrixInstr} {m : MatrixMove} {loc : Loc}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 0)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = false) (hsup : laneOf L g < m.num * m.rows)
    (hloc : matrixRowLoc L g t i = .ok loc)
    (hP : ∀ bs : List (Option Byte), bs.length = 16 →
      P ⟨pc, .rd { loc := loc, size := 16 } bs⟩) : P e :=
  shape_ldmatrix_rdM hf hs hop hrule hblk hst hsup
    (fun loc' bs h hl => by
      rw [hloc] at h
      cases h
      exact hP bs hl)
    (fun f h => by rw [hloc] at h; cases h)

/-- `ldmatrix`, sub-step 1 of a lane that read the known bytes `bs` of its row (its accumulator
is `rowVals bs`): the matrix event contributing `bs`, with any received bytes. -/
theorem shape_ldmatrix_mx {i : MatrixInstr} {m : MatrixMove} {bs : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 1)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = false) (hsup : laneOf L g < m.num * m.rows) (hacc : t.acc = rowVals bs)
    (hall : bs.all Option.isSome = true)
    (hP : ∀ recv, P ⟨pc, .matrix (.move m) bs recv⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [matrixTmpl_move hblk hrule hop,
    matrixMoveTmpl_load_mx hst (fun h => by rw [hs] at h; exact absurd h.2 (by decide)),
    ite_eq_left hsup, hacc, rowVals_own hall] at hf'
  obtain ⟨recv, rfl, -⟩ := hf'
  exact hP recv

/-- `stmatrix`, sub-step 0, whose source registers contribute the bytes `own`: its matrix event
with those bytes and any received bytes. -/
theorem shape_stmatrix_mx {i : MatrixInstr} {m : MatrixMove} {own : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 0)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = true) (hown : regBytes L g t 32 i.srcs = .ok own)
    (hP : ∀ recv, P ⟨pc, .matrix (.move m) own recv⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [matrixTmpl_move hblk hrule hop, matrixMoveTmpl_store_mx hst hs, hown] at hf'
  obtain ⟨recv, rfl, -⟩ := hf'
  exact hP recv

/-- `stmatrix`, sub-step 1 of a lane that received the bytes `bs` (its accumulator is
`rowVals bs`), with the condition of its undefined behaviour kept: the write of the known bytes
of `bs` to the 16-byte row `matrixRowLoc` gives, or undefined behaviour when it gives none. -/
theorem shape_stmatrix_wrM {i : MatrixInstr} {m : MatrixMove} {bs : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 1)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = true) (hacc : t.acc = rowVals bs)
    (hP : ∀ loc, matrixRowLoc L g t i = .ok loc →
      P ⟨pc, .wr { loc := loc, size := 16 } bs.reduceOption⟩)
    (hub : ∀ f, matrixRowLoc L g t i = .error f → P ⟨pc, .ub f⟩) : P e := by
  have hf' : Fires pc (matrixTmpl L g t i) e o := hf
  rw [matrixTmpl_move hblk hrule hop,
    matrixMoveTmpl_store_wr hst (by rw [hs]; decide), hacc, rowVals_bytes] at hf'
  cases hloc : matrixRowLoc L g t i with
  | error f =>
    rw [hloc] at hf'
    rw [hf'.1]
    exact hub f hloc
  | ok loc =>
    rw [hloc] at hf'
    rw [hf'.1]
    exact hP loc hloc

/-- `stmatrix`, sub-step 1 of a lane that received the bytes `bs` and supplies the row at `loc`:
a write of the known bytes of `bs` (all 16, by the first sub-step) to the 16 bytes at `loc`. -/
theorem shape_stmatrix_wr {i : MatrixInstr} {m : MatrixMove} {loc : Loc}
    {bs : List (Option Byte)}
    (hf : Fires pc (eventTmpl A L g t (.matrix i)) e o) (hs : t.sub = 1)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hblk : L.block % 32 = 0)
    (hst : m.store = true) (hacc : t.acc = rowVals bs)
    (hloc : matrixRowLoc L g t i = .ok loc)
    (hP : P ⟨pc, .wr { loc := loc, size := 16 } bs.reduceOption⟩) : P e :=
  shape_stmatrix_wrM hf hs hop hrule hblk hst hacc
    (fun loc' h => by
      rw [hloc] at h
      cases h
      exact hP)
    (fun f h => by rw [hloc] at h; cases h)

end
end PTX.Flow
