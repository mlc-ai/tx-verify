-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Contract
public import Lemmas.Flow.MatrixShape

@[expose] public section

/-!
# Steps of the value induction, over the generated thread machine

The lemmas the generated per-site steps (`Proof/Values/Gen/Steps.lean`) apply. A compute warp
is given by its first thread `w0` (`laneOf L w0 = 0`); its lanes are the threads `w0 + l`,
`l < 32`. `N` is the number of matrix events a lane has made; the event it makes next is its
matrix event of ordinal `N` (`X.MatrixK (w0 + l, k) N`: position `k` of the lane's trace).

**The cross-lane closure** (`mma_event`, `load_event`). A matrix event that exists has returned,
so every lane of the warp has made its event of the same ordinal or has exited short of it
(`WarpMatrix.lanes_of_event`); a compute lane does not exit short (`ComputeRef.count`,
`no_short_exit`). Each lane's machine is, before that event, at the matrix site of the ordinal
(`ComputeRef.site`), where its event contributes the bytes of its source registers
(`mma_shape`) or of the row it read (`loadMx_shape`). When the registers of all 32 lanes hold
their forms, the contributions are those the library's value lemmas ask for, the 32 events are
the warp's instance, and each lane received the closed form (`WarpMatrix.mma_recv`,
`ld4_event`). The statements hold in every consistent execution, complete or not: they speak
only about the events that exist.

**The machine's successor** (`stateAt_next`, and the generated `next_<site>` equations): the
state after an event is `next L g d e`; at a matrix site it is alive exactly when the received
bytes rebuild into values (`matrixVals`), which the closed forms do
(`matrixVals_mma`, `LoadSrc.vals_ok`).
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The multiply-accumulate of the kernel is read by the ideal-real assumption `idealArith`,
the first of the list. -/
theorem idealMma : IdealMma Assumptions.all :=
  IdealMma.cons_idealReal _ _ (by simp [bfTypes]) _

/-! ## The machine along a trace -/

/-- The state after an event is the machine's successor of the state before it. -/
theorem stateAt_next {g k : ℕ} {e : Event} {d : D} (he : X.get (g, k) = some e)
    (hσ : stateAt (code L) X g k = some (some d)) :
    stateAt (code L) X g (k + 1) = Thread.next L g d e := by
  rw [stateAt_succ (C := code L) he, hσ]
  rfl

/-- A matrix event is not undefined behaviour. -/
theorem not_ub_of_isMatrix {e : Event} (h : isMatrix e = true) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  cases h

/-- Before a matrix event the machine follows the lane. -/
theorem state_of_matrixK (F : Followed L mem0 X) {g k N : ℕ} (hk : X.MatrixK (g, k) N) :
    ∃ e d, X.get (g, k) = some e ∧ isMatrix e = true ∧
      stateAt (code L) X g k = some (some d) := by
  obtain ⟨⟨e, he, hm⟩, -⟩ := id hk
  obtain ⟨d, hd⟩ := event_state F.sound F.consistent F.tracked he (not_ub_of_isMatrix hm)
  exact ⟨e, d, he, hm, hd⟩

/-! ## The warp -/

/-- A compute warp: its first thread has lane 0 and its 32 lanes are compute threads. -/
structure Warp (L : Launch) (w0 : ℕ) : Prop where
  lane0 : laneOf L w0 = 0
  compute : ∀ l < 32, (w0 + l) % L.block < 128

/-- The lanes of a warp are in one thread block. -/
theorem Warp.block (F : Followed L mem0 X) {w0 l l' : ℕ} (W : Warp L w0) (hl : l < 32)
    (hl' : l' < 32) (hg : w0 + l < L.threads) : (w0 + l) / L.block = (w0 + l') / L.block :=
  (sameWarp_lanes F.block W.lane0 hg hl hl').1.2.2

/-- **No lane of a compute warp exits short of a matrix event that one of them makes**: a lane
that exits has made all `182 * tiles` matrix events of its block's sequence, and the lane that
makes the event of ordinal `N` has `N` below that number. -/
theorem no_short_exit (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 l k N : ℕ}
    (W : Warp L w0) (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∀ l' < 32, ∀ j, ¬ X.ExitedShort isMatrix (w0 + l', j) N := by
  rintro l' hl' j ⟨⟨pc, hex⟩, hle⟩
  obtain ⟨⟨e, he, -⟩, -⟩ := id hk
  have hg : w0 + l < L.threads := lt_of_get F.consistent he
  have h1 := matrixK_lt_countP hk
  have h2 := (R.count (w0 + l) (W.compute l hl)).1
  have h3 := (R.count (w0 + l') (W.compute l' hl')).2 j pc hex
  have h4 : tileCount P L (w0 + l) = tileCount P L (w0 + l') := by
    unfold tileCount seqOf
    rw [W.block F hl hl' hg]
  simp only at hle
  omega

/-! ## The events of a lane at a matrix site -/

/-- **The event of a lane at an `mma.sync`**: a matrix event that contributes the bytes of the
ten source registers, when each holds four bytes. -/
theorem mma_shape (F : Followed L mem0 X) {g k : ℕ} {e : Event} {d : D}
    (he : X.get (g, k) = some e) (hσ : stateAt (code L) X g k = some (some d))
    {ins : Instr} {i : MatrixInstr} {s : MmaSpec} {rs : List ℕ}
    (hcode : kernel.code[d.site.pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .mma s) (hrule : i.rule = some .threadMma) (hsrcs : i.srcs = rs.map .reg)
    (ha : MmaSpec.regBits s.types.a = 32) (hc : MmaSpec.regBits s.types.c = 32)
    (hlive : ∀ r ∈ rs, r ∈ Flow.live d.site.pc) (hb4 : ∀ r ∈ rs, (valueOf d r).bytes = 4) :
    ∃ recv, e = ⟨d.site.pc, .matrix (.mma s) (ownBytes (rs.map (valueOf d))) recv⟩ := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  have hreg : ∀ r ∈ rs, t.regs r = some (valueOf d r) := regs_of_live hat.2.2.2.2 hlive
  exact shape_mma (P := fun e => ∃ recv, e = ⟨d.site.pc, .matrix (.mma s)
      (ownBytes (rs.map (valueOf d))) recv⟩) hf hop hrule F.block
    (by rw [hsrcs]; exact mmaOwn_regs ha hc hreg hb4) fun recv => ⟨recv, rfl⟩

/-- **The matrix event of a lane at an `ldmatrix`** (its second event): it contributes the
sixteen bytes of the row it read. -/
theorem loadMx_shape (F : Followed L mem0 X) {g k : ℕ} {e : Event} {d : D}
    (he : X.get (g, k) = some e) (hσ : stateAt (code L) X g k = some (some d))
    {ins : Instr} {i : MatrixInstr} {m : MatrixMove} {bs : List (Option Byte)}
    (hcode : kernel.code[d.site.pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hst : m.store = false)
    (hrows : m.num * m.rows = 32) (hsub : d.site.sub = 1) (hacc : d.site.acc = rowVals bs)
    (hall : bs.all Option.isSome = true) :
    ∃ recv, e = ⟨d.site.pc, .matrix (.move m) bs recv⟩ := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  exact shape_ldmatrix_mx (P := fun e => ∃ recv, e = ⟨d.site.pc, .matrix (.move m) bs recv⟩) hf
    (hat.2.1.trans hsub) hop hrule F.block hst (laneOf_lt_rows hrows) (hat.2.2.1.trans hacc) hall
    fun recv => ⟨recv, rfl⟩

/-! ## What a lane receives -/

/-- **A multiply-accumulate across the warp.** `N` is an ordinal whose site is the `mma.sync` at
`pc` with the source registers `a0 … c3`. If, for every lane that is at its matrix event of
ordinal `N`, the registers hold the operands `Am`, `Bm` (packed pairs of bfloat16 payloads, in
the layout of the instruction) and `rc` (values that read as `Cm`), then a lane that makes the
event receives the bytes of `mmaReal Am Bm Cm` at its positions. -/
theorem mma_event (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 N pc : ℕ} (W : Warp L w0)
    {jj : Fin 104} (hord : ordSite (N % 182) = .mma jj) (hpc : (Site.warpMma jj).pc = pc)
    {ins : Instr} {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins)
    (hins : ins.op = .matrix i) (hop : i.op = .mma mma16) (hrule : i.rule = some .threadMma)
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ}
    (hsrcs : i.srcs = [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map .reg)
    (hlive : ([a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].all fun r =>
      (Flow.live pc).contains r) = true)
    {Am Bm Cm : ℕ → ℕ → ℝ} {rc : ℕ → ℕ → Value}
    (hops : Operands (regA Am) (regB Bm) rc Am Bm Cm)
    (hval : ∀ l < 32, ∀ k d, X.MatrixK (w0 + l, k) N →
      stateAt (code L) X (w0 + l) k = some (some d) → d.site = .warpMma jj →
      [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map (valueOf d) =
        [regA Am l 0, regA Am l 1, regA Am l 2, regA Am l 3, regB Bm l 0, regB Bm l 1,
          rc l 0, rc l 1, rc l 2, rc l 3])
    {l k : ℕ} (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∃ own, X.get (w0 + l, k) =
      some ⟨pc, .matrix (.mma mma16) own (outParts (mmaReal Am Bm Cm) l)⟩ := by
  have hshape : ∀ l' < 32, ∀ j, X.MatrixK (w0 + l', j) N → ∃ recv, X.get (w0 + l', j) =
      some ⟨pc, .matrix (.mma mma16) (mmaParts (regA Am) (regB Bm) rc l') recv⟩ := by
    intro l' hl' j hj
    obtain ⟨e, d, he, -, hσ⟩ := state_of_matrixK F hj
    have hs := R.site (w0 + l') j N d (W.compute l' hl') hj hσ
    rw [hord] at hs
    have hs' : d.site = .warpMma jj := hs
    have hv := hval l' hl' j d hj hσ hs'
    have hpc' : d.site.pc = pc := by rw [hs']; exact hpc
    have hb4 : ∀ r ∈ [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3], (valueOf d r).bytes = 4 := by
      have hall : ∀ v ∈ [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map (valueOf d),
          v.bytes = 4 := by
        rw [hv]
        intro v hv'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv'
        rcases hv' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · exact (hops.c l' hl' 0 (by omega)).bytes
        · exact (hops.c l' hl' 1 (by omega)).bytes
        · exact (hops.c l' hl' 2 (by omega)).bytes
        · exact (hops.c l' hl' 3 (by omega)).bytes
      exact fun r hr => hall _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hlive' : ∀ r ∈ [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3], r ∈ Flow.live d.site.pc := by
      intro r hr
      rw [hpc']
      simpa using List.all_eq_true.mp hlive r hr
    obtain ⟨recv, hrecv⟩ := mma_shape F he hσ (by rw [hpc']; exact hcode) hins hop hrule hsrcs
      rfl rfl hlive' hb4
    refine ⟨recv, ?_⟩
    rw [he, hrecv, hpc', hv, ownBytes_mma]
  have hI := WarpInstance.of_lanes F.consistent F.block W.lane0 hl hk
    (no_short_exit F R W hl hk) hshape
  obtain ⟨recv, he⟩ := hshape l hl k hk
  have := mma_recv F.consistent idealMma F.block W.lane0 hI hops hl he hk
  exact ⟨_, this ▸ he⟩

/-- **A load across the warp.** `N` is an ordinal whose site is the `j`-th `ldmatrix`, with
the transposition flag `tr`. If every lane that is at its matrix event of ordinal `N` holds the
row `rowPart rows l` it read (all bytes known), then a lane that makes the event receives the
register bytes `ldByte tr rows l`. -/
theorem load_event (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 N : ℕ} (W : Warp L w0)
    {j : Fin 44} (hord : ordSite (N % 182) = .load j)
    {ins : Instr} {i : MatrixInstr} {tr : Bool}
    (hcode : kernel.code[(Site.matrixLoad j).pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (ld4 tr)) (hrule : i.rule = some .threadMatrix)
    {rows : ℕ → ℕ → Option Byte}
    (hrow : ∀ l < 32, ∀ k d row, X.MatrixK (w0 + l, k) N →
      stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixLoadMx j row →
      row = rowPart rows l)
    (hall : ∀ l < 32, (rowPart rows l).all Option.isSome = true)
    {l k : ℕ} (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∃ own, X.get (w0 + l, k) = some ⟨(Site.matrixLoad j).pc,
      .matrix (.move (ld4 tr)) own (regPart (ldByte tr rows) l)⟩ := by
  have hshape : ∀ l' < 32, ∀ k', X.MatrixK (w0 + l', k') N → ∃ recv, X.get (w0 + l', k') =
      some ⟨(Site.matrixLoad j).pc, .matrix (.move (ld4 tr)) (rowPart rows l') recv⟩ := by
    intro l' hl' k' hk'
    obtain ⟨e, d, he, -, hσ⟩ := state_of_matrixK F hk'
    have hs := R.site (w0 + l') k' N d (W.compute l' hl') hk' hσ
    rw [hord] at hs
    obtain ⟨row, hs'⟩ : ∃ row, d.site = .matrixLoadMx j row := hs
    have hr := hrow l' hl' k' d row hk' hσ hs'
    have hpc' : d.site.pc = (Site.matrixLoad j).pc := by rw [hs']; rfl
    obtain ⟨recv, hrecv⟩ := loadMx_shape (bs := rowPart rows l') F he hσ
      (by rw [hpc']; exact hcode) hins hop hrule rfl rfl (by rw [hs']; rfl)
      (by rw [hs', hr]; rfl) (hall l' hl')
    exact ⟨recv, by rw [he, hrecv, hpc']⟩
  have hI := WarpInstance.of_lanes F.consistent F.block W.lane0 hl hk
    (no_short_exit F R W hl hk) hshape
  obtain ⟨recv, he⟩ := hshape l hl k hk
  have := ld4_event F.consistent F.block W.lane0 hI hl he hk
  exact ⟨_, this ▸ he⟩

/-! ## `movmatrix` and `stmatrix` across the warp -/

/-- **The event of a lane at a `movmatrix`**: a matrix event that contributes the four bytes of
its source register. -/
theorem move_shape (F : Followed L mem0 X) {g k : ℕ} {e : Event} {d : D}
    (he : X.get (g, k) = some e) (hσ : stateAt (code L) X g k = some (some d))
    {ins : Instr} {i : MatrixInstr} {dst src : ℕ}
    (hcode : kernel.code[d.site.pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .transpose) (hd : i.dsts = [dst]) (hs : i.srcs = [.reg src])
    (hlive : src ∈ Flow.live d.site.pc) (hb4 : (valueOf d src).bytes = 4) :
    ∃ recv, e = ⟨d.site.pc, .matrix .transpose (ownBytes [valueOf d src]) recv⟩ := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  have hreg : ∀ r ∈ [src], t.regs r = some (valueOf d r) :=
    regs_of_live hat.2.2.2.2 (by simpa using hlive)
  exact shape_movmatrix (P := fun e => ∃ recv, e = ⟨d.site.pc, .matrix .transpose
      (ownBytes [valueOf d src]) recv⟩) hf hop hd hs F.block
    (by rw [hs]; exact regBytes_regs (rs := [src]) hreg (by simpa using hb4))
    fun recv => ⟨recv, rfl⟩

/-- **The matrix event of a lane at an `stmatrix`** (its first event): it contributes the bytes
of its four source registers. -/
theorem store_shape (F : Followed L mem0 X) {g k : ℕ} {e : Event} {d : D}
    (he : X.get (g, k) = some e) (hσ : stateAt (code L) X g k = some (some d))
    {ins : Instr} {i : MatrixInstr} {m : MatrixMove} {rs : List ℕ}
    (hcode : kernel.code[d.site.pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hst : m.store = true)
    (hsrcs : i.srcs = rs.map .reg) (hsub : d.site.sub = 0)
    (hlive : ∀ r ∈ rs, r ∈ Flow.live d.site.pc) (hb4 : ∀ r ∈ rs, (valueOf d r).bytes = 4) :
    ∃ recv, e = ⟨d.site.pc, .matrix (.move m) (ownBytes (rs.map (valueOf d))) recv⟩ := by
  obtain ⟨t, ins', o, hat, -, hc', hf⟩ := fired_site F.sound F.consistent he hσ
  have hi : ins' = ins := Option.some.inj (hc'.symm.trans hcode)
  subst hi
  rw [hins] at hf
  have hreg : ∀ r ∈ rs, t.regs r = some (valueOf d r) := regs_of_live hat.2.2.2.2 hlive
  exact shape_stmatrix_mx (P := fun e => ∃ recv, e = ⟨d.site.pc, .matrix (.move m)
      (ownBytes (rs.map (valueOf d))) recv⟩) hf (hat.2.1.trans hsub) hop hrule F.block hst
    (by rw [hsrcs]; exact regBytes_regs hreg hb4) fun recv => ⟨recv, rfl⟩

/-- **A `movmatrix` across the warp.** If the source register of every lane that is at its
matrix event of ordinal `N` contributes the register bytes of the fragments of the 8 × 8 matrix
`S`, a lane that makes the event receives the register bytes of the transposed fragments. -/
theorem move_event (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 N pc : ℕ} (W : Warp L w0)
    {j : Fin 16} (hord : ordSite (N % 182) = .move j) (hpc : (Site.matrixMove j).pc = pc)
    {ins : Instr} {i : MatrixInstr} {dst src : ℕ} (hcode : kernel.code[pc]? = some ins)
    (hins : ins.op = .matrix i) (hop : i.op = .transpose) (hd : i.dsts = [dst])
    (hs : i.srcs = [.reg src]) (hlive : (Flow.live pc).contains src = true)
    {S : ℕ → ℕ → ℝ}
    (hval : ∀ l < 32, ∀ k d, X.MatrixK (w0 + l, k) N →
      stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixMove j →
      ownBytes [valueOf d src] = reg1Part (fragReg1 bf16Enc (toFrag1 S)) l ∧
        (valueOf d src).bytes = 4)
    {l k : ℕ} (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∃ own, X.get (w0 + l, k) = some ⟨pc, .matrix .transpose own
      (reg1Part (movByte (fragReg1 bf16Enc (toFrag1 S))) l)⟩ := by
  have hshape : ∀ l' < 32, ∀ k', X.MatrixK (w0 + l', k') N → ∃ recv, X.get (w0 + l', k') =
      some ⟨pc, .matrix .transpose (reg1Part (fragReg1 bf16Enc (toFrag1 S)) l') recv⟩ := by
    intro l' hl' k' hk'
    obtain ⟨e, d, he, -, hσ⟩ := state_of_matrixK F hk'
    have hs' := R.site (w0 + l') k' N d (W.compute l' hl') hk' hσ
    rw [hord] at hs'
    have hs'' : d.site = .matrixMove j := hs'
    obtain ⟨hv, hb4⟩ := hval l' hl' k' d hk' hσ hs''
    have hpc' : d.site.pc = pc := by rw [hs'']; exact hpc
    obtain ⟨recv, hrecv⟩ := move_shape F he hσ (by rw [hpc']; exact hcode) hins hop hd hs
      (by rw [hpc']; simpa using hlive) hb4
    exact ⟨recv, by rw [he, hrecv, hpc', hv]⟩
  have hI := WarpInstance.of_lanes F.consistent F.block W.lane0 hl hk
    (no_short_exit F R W hl hk) hshape
  obtain ⟨recv, he⟩ := hshape l hl k hk
  have := mov_event F.consistent F.block W.lane0 hI hl he hk
  exact ⟨_, this ▸ he⟩

/-- **A store across the warp.** If the four source registers of every lane that is at its
matrix event of ordinal `N` contribute the register bytes `regPart regs l`, a lane that makes
the event receives the row bytes `stByte tr regs l` (which it then writes to its row). -/
theorem store_event (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 N pc : ℕ} (W : Warp L w0)
    {j : Fin 18} (hord : ordSite (N % 182) = .store j) (hpc : (Site.matrixStore j).pc = pc)
    {ins : Instr} {i : MatrixInstr} {tr : Bool} {rs : List ℕ}
    (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (st4 tr)) (hrule : i.rule = some .threadMatrix)
    (hsrcs : i.srcs = rs.map .reg)
    (hlive : (rs.all fun r => (Flow.live pc).contains r) = true)
    {regs : ℕ → ℕ → ℕ → Option Byte}
    (hval : ∀ l < 32, ∀ k d, X.MatrixK (w0 + l, k) N →
      stateAt (code L) X (w0 + l) k = some (some d) → d.site = .matrixStore j →
      ownBytes (rs.map (valueOf d)) = regPart regs l ∧ ∀ r ∈ rs, (valueOf d r).bytes = 4)
    {l k : ℕ} (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∃ own, X.get (w0 + l, k) = some ⟨pc, .matrix (.move (st4 tr)) own
      (rowPart (stByte tr regs) l)⟩ := by
  have hshape : ∀ l' < 32, ∀ k', X.MatrixK (w0 + l', k') N → ∃ recv, X.get (w0 + l', k') =
      some ⟨pc, .matrix (.move (st4 tr)) (regPart regs l') recv⟩ := by
    intro l' hl' k' hk'
    obtain ⟨e, d, he, -, hσ⟩ := state_of_matrixK F hk'
    have hs' := R.site (w0 + l') k' N d (W.compute l' hl') hk' hσ
    rw [hord] at hs'
    have hs'' : d.site = .matrixStore j := hs'
    obtain ⟨hv, hb4⟩ := hval l' hl' k' d hk' hσ hs''
    have hpc' : d.site.pc = pc := by rw [hs'']; exact hpc
    obtain ⟨recv, hrecv⟩ := store_shape F he hσ (by rw [hpc']; exact hcode) hins hop hrule rfl
      hsrcs (by rw [hs'']; rfl)
      (fun r hr => by rw [hpc']; simpa using List.all_eq_true.mp hlive r hr) hb4
    exact ⟨recv, by rw [he, hrecv, hpc', hv]⟩
  have hI := WarpInstance.of_lanes F.consistent F.block W.lane0 hl hk
    (no_short_exit F R W hl hk) hshape
  obtain ⟨recv, he⟩ := hshape l hl k hk
  have := st4_event F.consistent F.block W.lane0 hI hl he hk
  exact ⟨_, this ▸ he⟩

/-! ## Reading the source registers of a multiply-accumulate off a table -/

/-- The source registers of a multiply-accumulate are listed in the table `T` with the forms of
its operands: the four A registers `regA A`, the two B registers `regB B`, and the four C
registers `regC C`, or, for a cleared accumulator (`C = none`), all the zero register 1168. All
listed registers are opaque. One Boolean check on literal tables. -/
def mmaCheck (T : Table) (srcs : List ℕ) (A B : Mat) (C : Option Mat) : Bool :=
  srcs.length == 10 &&
  ((List.range 4).all fun r => T.has (srcs.getD r 0) (.regA A r) && isOpaque (srcs.getD r 0)) &&
  ((List.range 2).all fun r =>
    T.has (srcs.getD (4 + r) 0) (.regB B r) && isOpaque (srcs.getD (4 + r) 0)) &&
  match C with
  | some Cm => (List.range 4).all fun r =>
      T.has (srcs.getD (6 + r) 0) (.regC Cm r) && isOpaque (srcs.getD (6 + r) 0)
  | none => (List.range 4).all fun r => srcs.getD (6 + r) 0 == 1168

/-- The real accumulator a C operand denotes: the matrix, or zero for a cleared accumulator. -/
def accEval (x : Inputs) (w : ℕ) : Option Mat → ℕ → ℕ → ℝ
  | some Cm => Cm.eval x w
  | none => fun _ _ => 0

/-- The values of the C registers: FP32 payloads, or the zero word. -/
def accRegs (x : Inputs) (w : ℕ) : Option Mat → ℕ → ℕ → Value
  | some Cm => regC (Cm.eval x w)
  | none => fun _ _ => .bits 32 (BitVec.ofNat 64 0)

/-- The registers hold the operands. -/
theorem accOperands (x : Inputs) (w : ℕ) (A B : Mat) (C : Option Mat) :
    Operands (regA (A.eval x w)) (regB (B.eval x w)) (accRegs x w C) (A.eval x w) (B.eval x w)
      (accEval x w C) := by
  cases C with
  | some Cm => exact operands_float _ _ _
  | none => exact operands_zero _ _

/-- The zero register's word, as a value. -/
theorem valueOf_zero {d : D} (h : d.w 1168 = Arith32.i32 0) :
    valueOf d 1168 = .bits 32 (BitVec.ofNat 64 0) := by
  have hk : valueOf d 1168 = .bits 32 (d.w 1168) := rfl
  rw [hk, h]
  rfl

/-- **The source values of a multiply-accumulate from the table**: with `mmaCheck`, a state
whose slots satisfy the table (and whose zero register holds zero) has the ten source values
the library's `Operands` asks for. -/
theorem mma_values {T : Table} {x : Inputs} {w l : ℕ} {d : D}
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ} {A B : Mat} {C : Option Mat}
    (hchk : mmaCheck T [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3] A B C = true)
    (hT : T.Holds x w l d.x) (hz : d.w 1168 = Arith32.i32 0) :
    [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map (valueOf d) =
      [regA (A.eval x w) l 0, regA (A.eval x w) l 1, regA (A.eval x w) l 2,
        regA (A.eval x w) l 3, regB (B.eval x w) l 0, regB (B.eval x w) l 1,
        accRegs x w C l 0, accRegs x w C l 1, accRegs x w C l 2, accRegs x w C l 3] := by
  simp only [mmaCheck, List.length_cons, List.length_nil, Bool.and_eq_true, List.all_eq_true,
    List.mem_range, beq_iff_eq] at hchk
  obtain ⟨⟨⟨-, hA⟩, hB⟩, hC⟩ := hchk
  have vo : ∀ {r : ℕ} {f : Form}, T.has r f = true → isOpaque r = true →
      f.Holds x w l (valueOf d r) := fun hm ho => by
    rw [valueOf_opaque ho]
    exact hT.get hm
  have a0' := vo (hA 0 (by omega)).1 (hA 0 (by omega)).2
  have a1' := vo (hA 1 (by omega)).1 (hA 1 (by omega)).2
  have a2' := vo (hA 2 (by omega)).1 (hA 2 (by omega)).2
  have a3' := vo (hA 3 (by omega)).1 (hA 3 (by omega)).2
  have b0' := vo (hB 0 (by omega)).1 (hB 0 (by omega)).2
  have b1' := vo (hB 1 (by omega)).1 (hB 1 (by omega)).2
  simp only [List.getD_cons_zero, List.getD_cons_succ, Form.Holds] at a0' a1' a2' a3' b0' b1'
  cases C with
  | some Cm =>
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hC
    have c0' := vo (hC 0 (by omega)).1 (hC 0 (by omega)).2
    have c1' := vo (hC 1 (by omega)).1 (hC 1 (by omega)).2
    have c2' := vo (hC 2 (by omega)).1 (hC 2 (by omega)).2
    have c3' := vo (hC 3 (by omega)).1 (hC 3 (by omega)).2
    simp only [List.getD_cons_zero, List.getD_cons_succ, Form.Holds] at c0' c1' c2' c3'
    simp only [List.map_cons, List.map_nil, a0', a1', a2', a3', b0', b1', c0', c1', c2', c3',
      accRegs]
  | none =>
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hC
    have c0' := hC 0 (by omega)
    have c1' := hC 1 (by omega)
    have c2' := hC 2 (by omega)
    have c3' := hC 3 (by omega)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at c0' c1' c2' c3'
    subst c0' c1' c2' c3'
    simp only [List.map_cons, List.map_nil, a0', a1', a2', a3', b0', b1', valueOf_zero hz,
      accRegs]

/-! ## The destination registers of a multiply-accumulate -/

/-- The forms of the four destination registers of a multiply-accumulate with result `D`. -/
def accForms (D : Mat) : List Form := [.regC D 0, .regC D 1, .regC D 2, .regC D 3]

/-- The values the machine records for them satisfy the forms. -/
theorem accForms_hold {x : Inputs} {w l : ℕ} {D : Mat} {Dm : ℕ → ℕ → ℝ}
    (hD : D.eval x w = Dm) (r : ℕ) (h : r < 4) :
    ((accForms D)[r]'h).Holds x w l
      (((List.range 4).map fun r => Value.float .f32 (Dm (cRow l r) (cCol l r)))[r]'(by
        simpa using h)) := by
  subst hD
  interval_cases r <;> rfl

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
