-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsValuesAccess
public import Kernels.FlashKdaFwd.Proof.Top.Wire

@[expose] public section

/-! # Exports of the Compute phase: the value layer's contract and the direct safety facts

What the value layer (`Proof/Values`) and the safety facts (`Proof/Top/Wire.lean`) read off
the reference invariant of the Compute phase (instructions 2106 to 2944: the tile loop of the
128 compute threads of a block). Every theorem is about a compute thread `g` and a *followed
state* `s` of its machine before its event `k` (`hσ : At (code L) X g k s`, that is
`Frame.stateAt (code L) X g k = some (some s)`) that satisfies the phase invariant
(`hI : Inv P L X g j0 k s`: the thread was at the phase's entry before its event `j0`). The
phase theorem (`Trace.lean: inv_at`) gives the invariant at every followed state from the entry
to the exit; the assembly supplies it and does the case split over the phases. Hypotheses
besides these: the precondition `hpre`, consistency `hX`, and for three theorems `g <
L.threads` or the entry facts (`In P L X g j0 s0` at a followed state).

**Words.** A *position* is the phase's entry or a pair of a tile `t` and an index `n < 268` in
the straight line of the tile's events (`Inv.lean`). The *ordinal* `WarpMatrix.ordinal X g k`
is the number of warp matrix events among the first `k` events of the thread; the invariant
makes it `182 * t + matOf n` at position `n` of tile `t`. `T = tilesOf P g` is the number of
tiles of the sequence of the thread's block; the value layer writes it `Values.tileCount P L
g` and the top layer `Top.tilesOf P L g` (`tileCount_eq`, `matrixTotal_eq`: the same number
under the precondition). An *accessing* position is one whose event reads or writes memory
(`ExportsValuesAccess.lean`).

## The contract `Values.ComputeRef` (`Proof/Values/Contract.lean`)

| field | theorem here |
|---|---|
| `site` | `site_compute` |
| `count` | `count_compute`, `count_le` (the bound), `count_out` (the exit), `not_exit_compute` |
| `zero` | `zero_compute` |
| `polled` | `polled_compute` |
| `loadRow` | `loadRow_compute` |
| `storeRow` | `storeRow_compute` |
| `scalarLoad` | `scalarLoad_compute` |

`count`: the bound holds at every state of the invariant (`count_le`), the pending state
included (`count_compute`); the equality holds at the phase's exit state (`count_out`); no
`exit` event is fired at a state of the invariant (`not_exit_compute`), so the clause "if the
lane exits" is the Epilogue's, which makes no matrix event.

and the three hypotheses of `Proof/Values/Hyps.lean`: `tileBound_compute` (`TileBound`),
`loopExit_out` and `loopExit_compute` (`LoopExit`: at the exit state of the phase; at a later
state at `bar_7` given that no state in between is at a matrix site, which is the Epilogue's
share), `firstLoad_compute` (`FirstLoad`, with the entry facts of the phase as premises).

What the assembly adds for the fields that quantify over every state of a compute thread: a
followed state of a compute thread outside the phase is at no site of the tile loop (no matrix
site, no `matrixLoad`, no `matrixStoreWr`, no load site 159 to 176), and the count of matrix
events is 0 before the phase's entry and unchanged after its exit (`Ref/Kinds/Count.lean`).

One remark on `storeRow`: at the row write of the LAST `stmatrix` of a tile (store 17,
position 263) the instruction's own matrix event is already counted, so `ordinal / 182` is the
tile plus one there. The field holds because the address of that row does not depend on the
tile (`st_stage`).

## The fields of `Top.DirectFacts`

| field | theorem here |
|---|---|
| `memSpaces` | `memSpaces_compute` (every operation of the phase is on shared memory) |
| `sharedFrame` | `sharedFrame_compute` |
| `globalReadFrame`, `writeFrame`, `globalWriteOnce` | vacuous: `memSpaces_compute` |
| `loadFill`, `loadBounds`, `storeBounds` | vacuous: `no_tensor_compute` |
| `matrixShape` | `matrixShape_compute` |
| `matrixCount` | `matrixCount_compute` (the bound), `matrixCount_out` (the exit) |
| `computeNoUb`, control half | `ub_compute`, `next_control` |

`memTouches_compute` says what an operation issued in the phase touches (`Touch`: the footprint
of an accessing position of a tile of the sequence); the phase issues no asynchronous
operation and touches no global byte.

**The control half of `computeNoUb`.** `ub_compute`: an undefined-behaviour event at a state of
the invariant is at an `mma.sync`, at a `movmatrix` or at the first event of an `stmatrix`: the
138 positions of a tile whose instruction reads data registers to build its matrix event (the
template is undefined behaviour exactly when a source register does not hold a 32-bit value:
the value layer's part). It is excluded outright at the other 130 positions and at the entry:
the two polls, the 44 row reads and the 44 matrix events of the `ldmatrix`, the 18 row writes
of the `stmatrix`, the 18 scalar loads, the named barrier, the proxy fence and the two
arrivals. `next_control`: at the entry, the two polls, the named barrier, the fence and the two
arrivals the state after the event is a followed state again (no dead state on the control
side). At the 262 other positions the successor function is dead only on a data condition: an
unknown byte in a row or in a scalar that was read, received bytes that do not rebuild into
values, or the condition of a floating-point run.

The declarations are in the namespace `Ref.Compute.Vals` (the other export files of the phase
have theorems of the same names for their own contracts). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Vals
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Frame (AccessOf AsyncOf)
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g j0 k : Nat} {s : D}
  {e : Event}

/-! ### The names of the other layers, under the precondition -/

/-- The value layer's tile count is the reference layer's. -/
theorem tileCount_eq (hpre : Pre P L mem0) (g : Nat) : Values.tileCount P L g = tilesOf P g := by
  simp only [Values.tileCount, Values.seqOf, tilesOf, seqOf, hpre.block]

/-- The value layer's position of the first gate logit is the reference layer's. -/
theorem gate_eq (hpre : Pre P L mem0) (g : Nat) : Values.gateOff P L g = gate P g := by
  simp only [Values.gateOff, Values.headOf, Values.seqOf, gate, headOf, seqOf, hpre.block]

/-- The top layer's total of matrix events of a compute thread: 182 per tile. -/
theorem matrixTotal_eq (hpre : Pre P L mem0) (hc : tid g < 128) :
    Top.matrixTotal P L g = 182 * tilesOf P g := by
  have hb : g % 192 < 128 := hc
  simp only [Top.matrixTotal, Top.tilesOf, Top.seqOf, tilesOf, seqOf, hpre.block, hb, ↓reduceIte]

/-! ### Tables -/

/-- The value layer's name (`Values.MSite`) of a matrix site of the phase: the second event of
an `ldmatrix`, an `mma.sync`, a `movmatrix`, the first event of an `stmatrix`. -/
def msOf : SK → Option Values.MSite
  | .ldMx j => some (.load j)
  | .mma j => some (.mma j)
  | .mv j => some (.move j)
  | .st j => some (.store j)
  | _ => none

/-- A site of a matrix kind is at the value layer's matrix site of that kind. -/
theorem msOf_at {q : SK} {m : Values.MSite} {site : Site} (h : msOf q = some m)
    (hat : q.At site) : m.At site := by
  cases q <;> simp only [msOf, Option.some.injEq, reduceCtorEq] at h <;> subst h <;> exact hat

/-- **A matrix position** has made fewer than 182 matrix events of its tile, and its site is
the one the value layer's table `ordSites` gives for that number. -/
theorem mat_table : ∀ n < 268, (msOf (skOf n)).isSome = true →
    matOf n < 182 ∧ Values.Gen.ordSites[matOf n]? = msOf (skOf n) := by
  decide +kernel

/-- A tile has 182 matrix events. -/
theorem mat_le : ∀ n < 268, matOf n ≤ 182 := by decide +kernel

/-- **A row read or a scalar load** comes after the tile's two polls and before the tile's last
matrix event. -/
theorem rd_table : ∀ n < 268, kindOf (skOf n) = .matrixLoad ∨ kindOf (skOf n) = .load →
    2 ≤ n ∧ matOf n < 182 := by
  decide +kernel

/-- At an `mma.sync` the register `%r862` (id 1168) is among the registers assigned. -/
theorem mma_table : ∀ n < 268, kindOf (skOf n) = .warpMma → 1168 ∈ regKeys.take (cntOf n) := by
  decide +kernel

/-- **The row write of an `stmatrix`** comes before the tile's last matrix event, or its
address does not depend on the output stage (the last `stmatrix` writes a row of the state
copy after the 182nd matrix event of the tile). -/
theorem st_stage : ∀ j : Fin 18, matOf (skTab.idxOf (.stWr j)) < 182 ∨
    (Values.Gen.storeForms[j.val]?).map (·.2.1) = some 0 := by
  decide +kernel

/-- **The positions by the kind of their event**: an accessing position, one of the six
control positions (the two polls, the named barrier, the fence, the two arrivals), or a matrix
position. -/
theorem kind_table : ∀ n < 268,
    n ∈ accPos ∨ n ∈ [0, 1, 264, 265, 266, 267] ∨ (msOf (skOf n)).isSome = true := by
  decide +kernel

/-- The kinds of the sites of the control positions. -/
def ctlKinds : List SiteKind := [.bar, .mbarWait, .fenceProxy, .mbarArrive]

/-- A position whose site is a barrier, a poll, a fence or an arrival is a control position. -/
theorem ctl_table : ∀ n < 268, kindOf (skOf n) ∈ ctlKinds → n ≤ 1 ∨ 264 ≤ n := by decide +kernel

/-- The second event of the first `ldmatrix` is position 3; position 2 is its first event. -/
theorem first_load : skTab.idxOf (.ldMx 0) = 3 ∧ skOf 2 = .ld 0 := by decide +kernel

/-! ### Readouts of the invariant -/

/-- The site kind of a position, from its site. -/
theorem skOf_of_at {n : Nat} {site : Site} {q : SK} (h : (skOf n).At site)
    (hq : SK.ofSite site = some q) : skOf n = q :=
  Option.some.inj ((SK.at_iff.mp h).symm.trans hq)

/-- **A state of the invariant that is not at the entry's site is at a position of a tile.** -/
theorem tile_of (hI : Inv P L X g j0 k s) (hne : s.site ≠ .bar 5) :
    ∃ t n, n < 268 ∧ t < tilesOf P g ∧ tid g < 128 ∧ RefAt P L g (.tile t n) s ∧
      ledOf L (g / L.block) ((X.tr g).take k) = led (.tile t n) ∧
      counted X g j0 k = 1 + 268 * t + n := by
  obtain ⟨pos, hR, hled, -, hcnt⟩ := hI
  cases pos with
  | entry => exact absurd hR.site hne
  | tile t n => exact ⟨t, n, hR.facts.pos, hR.facts.lt, hR.facts.compute, hR, hled, hcnt⟩

/-- **The matrix events before a position**: 182 per earlier tile and those of the tile. -/
theorem mats_tile {t n : Nat}
    (hled : ledOf L (g / L.block) ((X.tr g).take k) = led (.tile t n)) :
    WarpMatrix.ordinal X g k = 182 * t + matOf n :=
  congrArg Led.mats hled

/-- **The count of matrix events at a state of the invariant** is at most 182 per tile. -/
theorem count_le (hI : Inv P L X g j0 k s) : WarpMatrix.ordinal X g k ≤ 182 * tilesOf P g := by
  obtain ⟨pos, hR, hled, -, -⟩ := hI
  cases pos with
  | entry =>
    have hm : WarpMatrix.ordinal X g k = 0 := congrArg Led.mats hled
    rw [hm]
    exact Nat.zero_le _
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    have ht : t < tilesOf P g := hR.facts.lt
    have h1 := mat_le n hn
    have h2 := mats_tile hled
    omega

/-- **The count of matrix events at the exit of the phase**: 182 per tile. -/
theorem count_out {j : Nat} {s1 : D} (hO : Out P L X g j0 j s1) :
    WarpMatrix.ordinal X g j = 182 * tilesOf P g :=
  congrArg Led.mats hO.2.1

/-- **A row read or a scalar load of tile `t`**: the tile is the ordinal divided by 182, and
the thread has polled the "full" mbarrier of the tile's input stage successfully `t / 3 + 1`
times (once for each earlier tile of the stage, and for this tile). -/
theorem read_tile {t n : Nat} (hn : n < 268)
    (hq : kindOf (skOf n) = .matrixLoad ∨ kindOf (skOf n) = .load)
    (hled : ledOf L (g / L.block) ((X.tr g).take k) = led (.tile t n)) :
    WarpMatrix.ordinal X g k / 182 = t ∧
      okPolls (Values.fullBar L g t) ((X.tr g).take k) = t / 3 + 1 := by
  obtain ⟨h2, hm⟩ := rd_table n hn hq
  have hmat := mats_tile hled
  refine ⟨by omega, ?_⟩
  have hi : ind 2 n = 1 := by simp only [ind, h2, ↓reduceIte]
  obtain h0 | h1 | h2' : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
  · have hf : (⟨t % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 0 := Fin.ext h0
    have hp : okPolls ((Bar.loadFull 0).loc L (g / L.block)) ((X.tr g).take k) =
        uses 3 (t + ind 2 n) 0 := congrArg Led.pf0 hled
    rw [Values.fullBar, hf, hp, hi]
    unfold uses
    omega
  · have hf : (⟨t % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 1 := Fin.ext h1
    have hp : okPolls ((Bar.loadFull 1).loc L (g / L.block)) ((X.tr g).take k) =
        uses 3 (t + ind 2 n) 1 := congrArg Led.pf1 hled
    rw [Values.fullBar, hf, hp, hi]
    unfold uses
    omega
  · have hf : (⟨t % 3, Nat.mod_lt _ (by decide)⟩ : Fin 3) = 2 := Fin.ext h2'
    have hp : okPolls ((Bar.loadFull 2).loc L (g / L.block)) ((X.tr g).take k) =
        uses 3 (t + ind 2 n) 2 := congrArg Led.pf2 hled
    rw [Values.fullBar, hf, hp, hi]
    unfold uses
    omega

/-- **A state of the invariant at a read of the tile loop** (the first event of an `ldmatrix`,
a scalar load site, or the instruction of an entry of the value layer's `scalarForms`) is at a
position of a tile whose site is a row read or a scalar load. -/
theorem read_site (hI : Inv P L X g j0 k s)
    (hs : (∃ j : Fin 44, s.site = .matrixLoad j) ∨ (∃ i : Fin 178, s.site = .load i) ∨
      ∃ q ∈ Values.Gen.scalarForms, s.site.pc = q.1) :
    ∃ t n, n < 268 ∧ t < tilesOf P g ∧ tid g < 128 ∧ RefAt P L g (.tile t n) s ∧
      ledOf L (g / L.block) ((X.tr g).take k) = led (.tile t n) ∧
      (kindOf (skOf n) = .matrixLoad ∨ kindOf (skOf n) = .load) := by
  have hne : s.site ≠ .bar 5 := by
    intro h5
    rcases hs with ⟨j, h⟩ | ⟨i, h⟩ | ⟨q, hq, h⟩
    · rw [h5] at h
      cases h
    · rw [h5] at h
      cases h
    · rw [h5] at h
      exact sc_entry q hq h.symm
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hne
  have hat : (skOf n).At s.site := hR.site
  refine ⟨t, n, hn, ht, hc, hR, hled, ?_⟩
  rcases hs with ⟨j, h⟩ | ⟨i, h⟩ | ⟨q, hq, h⟩
  · left
    rw [← kind_of_at hat, h]
    rfl
  · right
    rw [← kind_of_at hat, h]
    rfl
  · exact .inr (sc_table q hq n hn ((pc_of_at hat).symm.trans h)).1

/-! ### `ComputeRef.count`, `zero`, `polled`; `TileBound` -/

/-- **`ComputeRef.count`, the bound**: a compute lane whose pending state (the state after its
last event) satisfies the invariant has made at most 182 matrix events per tile. -/
theorem count_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 (X.tr g).length s) :
    (X.tr g).countP isMatrix ≤ 182 * Values.tileCount P L g := by
  have h := count_le hI
  unfold WarpMatrix.ordinal at h
  rw [List.take_length] at h
  rw [tileCount_eq hpre]
  exact h

/-- **`ComputeRef.zero`**: at an `mma.sync` the register `%r862` (id 1168), cleared once per
tile, holds the zero word. -/
theorem zero_compute (hI : Inv P L X g j0 k s) {j : Fin 104} (hs : s.site = .warpMma j) :
    s.w 1168 = Arith32.i32 0 := by
  have hne : s.site ≠ .bar 5 := by
    rw [hs]
    exact fun h => by cases h
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hne
  have hat : (skOf n).At s.site := hR.site
  have hq : kindOf (skOf n) = .warpMma := by
    rw [← kind_of_at hat, hs]
    rfl
  have h := hR.facts.regs 1168 (mma_table n hn hq)
  rw [h, rv_1168]
  rfl

/-- **`ComputeRef.polled`**: at a read of the input stage in the tile loop the lane has polled
the "full" mbarrier of its tile's stage successfully `b / 3 + 1` times, `b` its tile. -/
theorem polled_compute (hI : Inv P L X g j0 k s)
    (hs : (∃ j : Fin 44, s.site = .matrixLoad j) ∨
      ∃ sz c ck ws, (s.site.pc, sz, c, ck, ws) ∈ Values.Gen.scalarForms) :
    okPolls (Values.fullBar L g (WarpMatrix.ordinal X g k / 182)) ((X.tr g).take k) =
      WarpMatrix.ordinal X g k / 182 / 3 + 1 := by
  have hs' : (∃ j : Fin 44, s.site = .matrixLoad j) ∨ (∃ i : Fin 178, s.site = .load i) ∨
      ∃ q ∈ Values.Gen.scalarForms, s.site.pc = q.1 := by
    rcases hs with h | ⟨sz, c, ck, ws, h⟩
    · exact .inl h
    · exact .inr (.inr ⟨_, h, rfl⟩)
  obtain ⟨t, n, hn, ht, hc, hR, hled, hq⟩ := read_site hI hs'
  obtain ⟨h1, h2⟩ := read_tile hn hq hled
  rw [h1]
  exact h2

/-- **`Values.TileBound`**: at the first event of an `ldmatrix` and at a scalar load of the
tile loop the lane's tile is below the tile count. -/
theorem tileBound_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s)
    (hs : (∃ j : Fin 44, s.site = .matrixLoad j) ∨
      ∃ i : Fin 178, 159 ≤ i.val ∧ i.val < 177 ∧ s.site = .load i) :
    WarpMatrix.ordinal X g k / 182 < Values.tileCount P L g := by
  have hs' : (∃ j : Fin 44, s.site = .matrixLoad j) ∨ (∃ i : Fin 178, s.site = .load i) ∨
      ∃ q ∈ Values.Gen.scalarForms, s.site.pc = q.1 := by
    rcases hs with h | ⟨i, -, -, h⟩
    · exact .inl h
    · exact .inr (.inl ⟨i, h⟩)
  obtain ⟨t, n, hn, ht, hc, hR, hled, hq⟩ := read_site hI hs'
  obtain ⟨h1, -⟩ := read_tile hn hq hled
  rw [h1, tileCount_eq hpre]
  exact ht

/-- **`Values.LoopExit` at the exit state**: a compute lane at the exit of the phase (the site
`bar_7`, with the exit condition) has made 182 matrix events per tile. -/
theorem loopExit_out (hpre : Pre P L mem0) {j : Nat} {s1 : D} (hO : Out P L X g j0 j s1) :
    WarpMatrix.ordinal X g j = 182 * Values.tileCount P L g := by
  rw [tileCount_eq hpre]
  exact count_out hO

/-! ### Events at a followed state -/

/-- A matrix event has the kind `.matrix`. -/
theorem isMatrix_kind {e : Event} (h : isMatrix e = true) :
    ∃ op own recv, e.kind = .matrix op own recv := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first
    | exact ⟨_, _, _, rfl⟩
    | cases h

/-- **A thread access or an issued operation is fired at a read, a write or a tensor copy.** -/
theorem access_kind {a : Acc} {κ : SiteKind} (ha : AccessOf e a ∨ AsyncOf e a)
    (hf : firedAt e.kind κ = true) : κ ∈ accKinds := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first
    | (rcases ha with ha | ha <;> exact ha.elim)
    | (cases κ <;> first
        | decide
        | cases hf)

/-- An event fired at the second event of an `ldmatrix` or at a matrix instruction counts (it
is no failed poll). -/
theorem counts_of_fired {κ : SiteKind} (hf : firedAt e.kind κ = true)
    (hκ : κ ≠ .mbarWait) : e.counts = true := by
  obtain ⟨pc, kd⟩ := e
  cases kd <;> first
    | rfl
    | (cases κ <;> first
        | exact absurd rfl hκ
        | cases hf)

/-- An `ldmatrix` with the rule THREAD-MATRIX. -/
def isLd (ins : Instr) : Bool :=
  match ins.op with
  | .matrix i =>
    match i.op with
    | .move m => !m.store && decide (i.rule = some .threadMatrix)
    | _ => false
  | _ => false

/-- What `isLd` says of an instruction. -/
theorem isLd_spec {ins : Instr} (h : isLd ins = true) :
    ∃ i m, ins.op = .matrix i ∧ i.op = .move m ∧ m.store = false ∧
      i.rule = some .threadMatrix := by
  unfold isLd at h
  split at h
  · rename_i i hop
    split at h
    · rename_i m hm
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
      exact ⟨i, m, hop, hm, h.1, h.2⟩
    · cases h
  · cases h

/-- The instruction at the second event of each `ldmatrix` of a tile is an `ldmatrix` with the
rule THREAD-MATRIX. -/
theorem ldMx_table : ∀ n < 268, kindOf (skOf n) = .matrixLoadMx →
    (kernel.code[(siteOf (skOf n)).pc]?).any isLd = true := by
  decide +kernel

/-- **The second event of an `ldmatrix`** is the matrix event, whatever the registers hold: the
instruction contributes the bytes of the row it read. -/
theorem ev_ldMx {tt : TState} {o : Option TState} {i : MatrixInstr} {m : MatrixMove} {pc : Nat}
    (hb : L.block % 32 = 0) (hrule : i.rule = some .threadMatrix) (hop : i.op = .move m)
    (hst : m.store = false) (hs : tt.sub ≠ 0)
    (hf : Fires pc (eventTmpl Assumptions.all L g tt (.matrix i)) e o) :
    ∃ own recv, e = ⟨pc, .matrix (.move m) own recv⟩ := by
  have hf' : Fires pc (matrixTmpl L g tt i) e o := hf
  rw [matrixTmpl_move hb hrule hop, matrixMoveTmpl_load_mx hst (fun h => hs h.2)] at hf'
  obtain ⟨recv, rfl, -⟩ := hf'
  exact ⟨_, recv, rfl⟩

/-- The instruction indices of the 182 matrix positions of a tile, in order. -/
def matPcs : List Nat :=
  (List.range 268).filterMap fun n =>
    if (msOf (skOf n)).isSome then some (siteOf (skOf n)).pc else none

/-- The matrix positions of a tile are at the matrix instructions of the code, in code order
(`Top.matrixSites`). -/
theorem matPcs_eq : Top.matrixSites.map Prod.fst = matPcs := by decide +kernel

/-- The matrix position with `m` earlier matrix events of the tile is at the `m`-th matrix
instruction. -/
theorem matPc_table : ∀ n < 268, (msOf (skOf n)).isSome = true →
    matPcs[matOf n]? = some (siteOf (skOf n)).pc := by
  decide +kernel

/-- An entry of `Top.matrixSites` is a matrix instruction of the code with its operation. -/
theorem matrixSites_get {m pc : Nat} {op : MatrixOp} (h : Top.matrixSites[m]? = some (pc, op)) :
    ∃ ins i, kernel.code[pc]? = some ins ∧ ins.op = .matrix i ∧ i.op = op := by
  have hmem := List.mem_of_getElem? h
  unfold Top.matrixSites at hmem
  obtain ⟨⟨ins, idx⟩, hx, hy⟩ := List.mem_filterMap.mp hmem
  have hget : kernel.code[idx]? = some ins := List.mem_zipIdx_iff_getElem?.mp hx
  dsimp only at hy
  split at hy
  · rename_i i hop
    cases hy
    exact ⟨ins, i, hget, hop, rfl⟩
  · cases hy

/-- The counted events of a thread since its entry do not decrease. -/
theorem counted_mono {j k : Nat} (hjk : j ≤ k) : counted X g j0 j ≤ counted X g j0 k :=
  ((List.take_sublist_take_left hjk).drop j0).countP_le

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The event at an accessing position** of a state of the invariant (`access_at`, with the
concrete state and the firing fact taken from the execution). -/
theorem acc_event {t n : Nat} (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hR : RefAt P L g (.tile t n) s) (hn : n ∈ accPos) : AccEv P L g t n s.site e := by
  obtain ⟨site, w, p, x⟩ := s
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  exact access_at hpre hR.facts hR.site hat hc hf hn

/-- **A matrix event at a state of the invariant**: the state is at a matrix position `n` of a
tile `t`, with fewer than 182 matrix events of the tile before it, at the site the value layer
names for that number; the ordinal of the event is `182 * t + matOf n`. -/
theorem matrix_pos {op : MatrixOp} {own recv : List (Option Byte)}
    (he : X.get (g, k) = some e) (hq : e.kind = .matrix op own recv)
    (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) :
    ∃ t n m, n < 268 ∧ t < tilesOf P g ∧ tid g < 128 ∧ RefAt P L g (.tile t n) s ∧
      msOf (skOf n) = some m ∧ matOf n < 182 ∧ Values.Gen.ordSites[matOf n]? = some m ∧
      WarpMatrix.ordinal X g k = 182 * t + matOf n := by
  have hP := matrix_site_ind (sounds hpre) hX he hσ hq
    (P := fun site => site ≠ .bar 5 ∧
      ∀ n, (skOf n).At site → (msOf (skOf n)).isSome = true)
    (fun j row => ⟨nofun, fun n h => by rw [skOf_of_at h rfl]; rfl⟩)
    (fun j => ⟨nofun, fun n h => by rw [skOf_of_at h rfl]; rfl⟩)
    (fun j => ⟨nofun, fun n h => by rw [skOf_of_at h rfl]; rfl⟩)
    (fun j => ⟨nofun, fun n h => by rw [skOf_of_at h rfl]; rfl⟩)
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hP.1
  have hsome := hP.2 n hR.site
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hsome
  have htab := mat_table n hn hsome
  exact ⟨t, n, m, hn, ht, hc, hR, hm, htab.1, by rw [htab.2, hm], mats_tile hled⟩

/-! ### `ComputeRef.site`, `loadRow`, `storeRow`, `scalarLoad` -/

/-- **`ComputeRef.site`**: before its `N`-th matrix event the machine of a lane is at the
matrix site of ordinal `N % 182`. -/
theorem site_compute {N : Nat} (hN : X.MatrixK (g, k) N) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) : (Values.ordSite (N % 182)).At s.site := by
  obtain ⟨⟨e, he, hm⟩, hcnt⟩ := hN
  obtain ⟨op, own, recv, hq⟩ := isMatrix_kind hm
  obtain ⟨t, n, m, hn, ht, hc, hR, hms, hlt, hord, hmat⟩ := matrix_pos hpre hX he hq hσ hI
  have hN' : N = 182 * t + matOf n := hcnt.symm.trans hmat
  have hmod : N % 182 = matOf n := by omega
  have ho : Values.ordSite (N % 182) = m := by
    rw [hmod, Values.ordSite, List.getD_eq_getElem?_getD, hord]
    rfl
  rw [ho]
  exact msOf_at hms hR.site

/-- **`ComputeRef.loadRow`**: at the first event of the `j`-th `ldmatrix` the lane reads the 16
bytes of its row, at the offset `Values.loadOff` of its block's window, for the tile
`ordinal / 182`. -/
theorem loadRow_compute (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) {j : Fin 44} (hs : s.site = .matrixLoad j) :
    ∃ a bs, e = ⟨s.site.pc, .rd a bs⟩ ∧ a.size = 16 ∧
      a.loc = ⟨.shared, g / L.block,
        P.sharedBase + Values.loadOff j (WarpMatrix.ordinal X g k / 182) (g % L.block)⟩ := by
  obtain ⟨t, n, hn, ht, hc, hR, hled, hq⟩ := read_site hI (.inl ⟨j, hs⟩)
  obtain ⟨hb, -⟩ := read_tile hn hq hled
  have hat : (skOf n).At s.site := hR.site
  have hsk : skOf n = .ld j := skOf_of_at hat (by rw [hs]; rfl)
  have hidx : skTab.idxOf (.ld j) = n := by
    rw [← hsk]
    exact pos_idx n hn
  have hacc : n ∈ accPos := acc_of_kind n hn (by rw [hsk]; exact ld_acc)
  obtain ⟨r, c, sz, ha, hpc, hev⟩ := acc_event hpre hX he hσ hR hacc
  have hlen : j.val < Values.Gen.loadForms.length := j.isLt
  obtain ⟨⟨c0, s0, ws⟩, hlf⟩ : ∃ q, Values.Gen.loadForms[j.val]? = some q :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have htab := ld_table j
  rw [hidx, hlf] at htab
  obtain ⟨hsz, hval⟩ := posForm_val (P := P) (t := t) hc ha htab
  rcases hev with ⟨bs, -, hkd⟩ | ⟨j', row, hsite, -⟩
  · obtain ⟨pc, kd⟩ := e
    simp only at hpc hkd
    subst hpc hkd
    have hadr : regVal P g t r + c = P.sharedBase +
        Values.loadOff j (WarpMatrix.ordinal X g k / 182) (g % L.block) := by
      rw [hval, hb, block_mod hpre]
      simp only [Form.val, Values.loadOff, hlf]
      omega
    exact ⟨_, bs, rfl, hsz, by rw [hadr]⟩
  · rw [hs] at hsite
    cases hsite

/-- **`ComputeRef.storeRow`**: at the second event of the `j`-th `stmatrix` the lane writes the
16 bytes it received (the bytes `row` carried by the site) to its row, at the offset
`Values.storeOff`. -/
theorem storeRow_compute (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) {j : Fin 18} {row : List (Option Byte)}
    (hs : s.site = .matrixStoreWr j row) :
    ∃ a, e = ⟨s.site.pc, .wr a row.reduceOption⟩ ∧ a.size = 16 ∧
      a.loc = ⟨.shared, g / L.block,
        P.sharedBase + Values.storeOff j (WarpMatrix.ordinal X g k / 182) (g % L.block)⟩ := by
  have hne : s.site ≠ .bar 5 := by
    rw [hs]
    exact fun h => by cases h
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hne
  have hmat := mats_tile hled
  have hat : (skOf n).At s.site := hR.site
  have hsk : skOf n = .stWr j := skOf_of_at hat (by rw [hs]; rfl)
  have hidx : skTab.idxOf (.stWr j) = n := by
    rw [← hsk]
    exact pos_idx n hn
  have hacc : n ∈ accPos := acc_of_kind n hn (by rw [hsk]; exact stWr_acc)
  obtain ⟨r, c, sz, ha, hpc, hev⟩ := acc_event hpre hX he hσ hR hacc
  have hlen : j.val < Values.Gen.storeForms.length := j.isLt
  obtain ⟨⟨c0, s0, ws⟩, hlf⟩ : ∃ q, Values.Gen.storeForms[j.val]? = some q :=
    ⟨_, List.getElem?_eq_getElem hlen⟩
  have htab := st_table j
  rw [hidx, hlf] at htab
  obtain ⟨hsz, hval⟩ := posForm_val (P := P) (t := t) hc ha htab
  have hstage := st_stage j
  rw [hidx, hlf] at hstage
  rcases hev with ⟨bs, hnw, -⟩ | ⟨j', row', hsite, hkd⟩
  · rw [hsk] at hnw
    exact absurd rfl hnw
  · rw [hs] at hsite
    obtain ⟨-, rfl⟩ := Site.matrixStoreWr.inj hsite
    obtain ⟨pc, kd⟩ := e
    simp only at hpc hkd
    subst hpc hkd
    have hadr : regVal P g t r + c = P.sharedBase +
        Values.storeOff j (WarpMatrix.ordinal X g k / 182) (g % L.block) := by
      rw [hval, block_mod hpre]
      simp only [Form.val, Values.storeOff, hlf]
      rcases hstage with hlt | hz
      · have hb : WarpMatrix.ordinal X g k / 182 = t := by omega
        rw [hb]
        omega
      · have h0 : s0 = 0 := by simpa using hz
        subst h0
        omega
    exact ⟨_, rfl, hsz, by rw [hadr]⟩

/-- **`ComputeRef.scalarLoad`**: at the instruction of an entry `(pc, sz, c, ck, ws)` of the
value layer's `scalarForms` (the two gate logits, the sixteen decay factors) the lane reads
`sz` bytes of the input stage of its tile, at the listed offset. -/
theorem scalarLoad_compute (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) {pc sz c ck : Nat} {ws : List Nat}
    (hq : (pc, sz, c, ck, ws) ∈ Values.Gen.scalarForms) (hpc : s.site.pc = pc) :
    ∃ a bs, e = ⟨pc, .rd a bs⟩ ∧ a.size = sz ∧
      a.loc = ⟨.shared, g / L.block, P.sharedBase +
        (c + 18048 * (WarpMatrix.ordinal X g k / 182 % 3) + ck * Values.gateOff P L g +
          Values.bitsOff ws (g % L.block))⟩ := by
  obtain ⟨t, n, hn, ht, hc, hR, hled, hkind⟩ := read_site hI (.inr (.inr ⟨_, hq, hpc⟩))
  obtain ⟨hb, -⟩ := read_tile hn hkind hled
  have hat : (skOf n).At s.site := hR.site
  obtain ⟨hload, htab⟩ : kindOf (skOf n) = .load ∧
      posForm n = some (⟨c, 18048, 0, ck, ws⟩, sz) :=
    sc_table _ hq n hn ((pc_of_at hat).symm.trans hpc)
  have hacc : n ∈ accPos := acc_of_kind n hn (by rw [hload]; exact load_acc)
  obtain ⟨r, c', sz', ha, hpc', hev⟩ := acc_event hpre hX he hσ hR hacc
  obtain ⟨hsz, hval⟩ := posForm_val (P := P) (t := t) hc ha htab
  rcases hev with ⟨bs, -, hkd⟩ | ⟨j', row, hsite, -⟩
  · obtain ⟨pc0, kd⟩ := e
    simp only at hpc' hkd
    subst hkd
    have hpc0 : pc0 = pc := hpc'.trans hpc
    subst hpc0
    have hadr : regVal P g t r + c' = P.sharedBase +
        (c + 18048 * (WarpMatrix.ordinal X g k / 182 % 3) + ck * Values.gateOff P L g +
          Values.bitsOff ws (g % L.block)) := by
      rw [hval, hb, block_mod hpre, gate_eq hpre]
      simp only [Form.val]
      omega
    exact ⟨_, bs, rfl, hsz, by rw [hadr]⟩
  · have hk := kind_of_at hat
    rw [hsite, hload] at hk
    cases hk

/-! ### `Values.FirstLoad`, `Values.LoopExit` -/

/-- **`Values.FirstLoad`**: when the event `k` of a lane exists and the state after it is at
the second event of the first `ldmatrix`, the state before it is at the first event:
positions 2 and 3 of a tile are consecutive. (The event must exist: past the end of the trace
the states at `k` and `k + 1` are the same pending state.) -/
theorem firstLoad_compute (hg : g < L.threads) {s0 d : D} {row : List (Option Byte)}
    (h0 : At (code L) X g j0 s0) (hin : In P L X g j0 s0) (he : X.get (g, k) = some e)
    (hσ : At (code L) X g (k + 1) d) (hI : Inv P L X g j0 (k + 1) d)
    (hs : d.site = .matrixLoadMx 0 row) :
    ∃ d0, At (code L) X g k d0 ∧ d0.site = .matrixLoad 0 := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hne : d.site ≠ .bar 5 := by
    rw [hs]
    exact fun h => by cases h
  have hj0 : j0 ≤ k + 1 := hI.choose_spec.2.2.1
  obtain ⟨t, n, hn, ht, hc, hR, hled, hcnt⟩ := tile_of hI hne
  have hat : (skOf n).At d.site := hR.site
  have hsk : skOf n = .ldMx 0 := skOf_of_at hat (by rw [hs]; rfl)
  have hn3 : n = 3 := by
    rw [← pos_idx n hn, hsk]
    exact first_load.1
  subst hn3
  have hjk : j0 ≤ k := by
    rcases Nat.eq_or_lt_of_le hj0 with h | h
    · rw [h, counted_self] at hcnt
      omega
    · omega
  obtain ⟨d0, hd0⟩ := followed_of_le hσ (Nat.le_succ k)
  refine ⟨d0, hd0, ?_⟩
  have hsucc := counted_succ (j0 := j0) hjk he
  rcases inv_at hpre hX hg h0 hin hjk hk.le hd0 with hI0 | ⟨j, s1, h1, h2, h3, h4⟩
  · obtain ⟨pos, hR0, -, -, hcnt0⟩ := hI0
    have hfk := site_fires (sounds hpre) hX he hd0
    cases pos with
    | entry =>
      have : counted X g j0 k = 0 := hcnt0
      split at hsucc <;> omega
    | tile t' n' =>
      have hn' : n' < 268 := hR0.facts.pos
      have hat0 : (skOf n').At d0.site := hR0.site
      have hc0 : counted X g j0 k = 1 + 268 * t' + n' := hcnt0
      by_cases hcounts : e.counts = true
      · simp only [hcounts, ↓reduceIte] at hsucc
        obtain rfl : n' = 2 := by omega
        rw [first_load.2] at hat0
        exact hat0
      · simp only [hcounts, Bool.false_eq_true, ↓reduceIte] at hsucc
        obtain rfl : n' = 3 := by omega
        exfalso
        apply hcounts
        refine counts_of_fired hfk ?_
        rw [kind_of_at hat0, show skOf 3 = .ldMx 0 from hsk]
        exact fun h => by cases h
  · have h5 : counted X g j0 j = 1 + 268 * tilesOf P g := h4.2.2.2
    have h6 := counted_mono (X := X) (g := g) (j0 := j0) (show j ≤ k + 1 by omega)
    omega

/-- **`Values.LoopExit`**: a compute lane at `bar_7` after the phase's entry has made 182
matrix events per tile, when no state between the phase's exit and it is at a matrix site (the
Epilogue's share: after `bar_7` the thread is at the sites of the epilogue). The exit state
itself is `loopExit_out`. -/
theorem loopExit_compute (hg : g < L.threads) {s0 : D} (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hjk : j0 ≤ k) (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k s) (h7 : s.site = .bar 7)
    (hepi : ∀ j s1, j0 ≤ j → j ≤ k → At (code L) X g j s1 → Out P L X g j0 j s1 →
      ∀ i d, j ≤ i → i < k → At (code L) X g i d → d.site.kind ∉ matrixKinds) :
    WarpMatrix.ordinal X g k = 182 * Values.tileCount P L g := by
  obtain ⟨j, s1, h1, h2, h3, h4⟩ := out_of_bar7 hpre hX hg h0 hin hjk hk hσ h7
  have ht := count_transport_of_state (sounds hpre) hX firedOnly_isMatrix h2 hσ
    (Nat.le_succ k) fun i d hji hik hd => .inl (hepi j s1 h1 h2 h3 h4 i d hji hik hd)
  rw [← loopExit_out hpre h4]
  exact ht

/-! ### Memory: `memSpaces`, `sharedFrame` -/

/-- **What an operation of the phase touches**: the footprint of an accessing position `n` of
a tile `t` of the sequence: `sz` bytes at `regVal P g t r + c` in the window of the thread's
own block, `(r, c, sz)` the position's entry of `addrTab`. -/
def Touch (P : Params) (L : Launch) (g : Nat) (a : Acc) : Prop :=
  ∃ t n r c sz, t < tilesOf P g ∧ tid g < 128 ∧ n ∈ accPos ∧ addrTab[n]? = some (r, c, sz) ∧
    a = { loc := ⟨.shared, g / L.block, regVal P g t r + c⟩, size := sz }

omit hX in
/-- **A touched footprint is in the data part of the window of the thread's own block**: shared
memory, the block of the thread, the first 95104 bytes. -/
theorem touch_frame {a : Acc} (h : Touch P L g a) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 95104 := by
  obtain ⟨t, n, r, c, sz, ht, hc, hn, ha, rfl⟩ := h
  have hfr := addr_frame hpre hc (t := t) hn ha
  exact ⟨rfl, rfl, hfr.1, hfr.2⟩

/-- **What an event of the phase accesses or issues an access of**: the event of an accessing
position, with its footprint. The phase issues no asynchronous operation. -/
theorem touch_compute {a : Acc} (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) (ha : AccessOf e a ∨ AsyncOf e a) : Touch P L g a := by
  have hκ := access_kind ha (site_fires (sounds hpre) hX he hσ)
  have hne : s.site ≠ .bar 5 := by
    intro h5
    rw [h5] at hκ
    revert hκ
    decide
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hne
  have hat : (skOf n).At s.site := hR.site
  rw [kind_of_at hat] at hκ
  have hacc := acc_of_kind n hn hκ
  obtain ⟨r, c, sz, hadr, -, hev⟩ := acc_event hpre hX he hσ hR hacc
  obtain ⟨pc, kd⟩ := e
  rcases hev with ⟨bs, -, hkd⟩ | ⟨j, row, -, hkd⟩
  · simp only at hkd
    subst hkd
    rcases ha with ha | ha
    · exact ⟨t, n, r, c, sz, ht, hc, hacc, hadr, ha⟩
    · exact ha.elim
  · simp only at hkd
    subst hkd
    rcases ha with ha | ha
    · exact ⟨t, n, r, c, sz, ht, hc, hacc, hadr, ha⟩
    · exact ha.elim

/-- **What a memory operation issued in the phase touches** (`Execution.MemTouches`: thread
accesses, `nc` reads and the stages of asynchronous operations, pending or performed). -/
theorem memTouches_compute {r : AsyncCopy.Ref} {a : Acc} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) :
    Touch P L g a := by
  rcases ht with ⟨w, hi⟩ | ⟨i, bs, hri, pc, hnc⟩
  · obtain ⟨e, he, ha⟩ := Frame.intent_issuer hi
    rw [hr] at he
    exact touch_compute hpre hX he hσ hI ha
  · subst hri
    have hi : i = (g, k) := hr
    subst hi
    exact touch_compute hpre hX hnc hσ hI (.inl rfl)

/-- **`DirectFacts.memSpaces` for the Compute phase**: every operation is on shared memory
(none on global memory: the fields `globalReadFrame`, `writeFrame` and `globalWriteOnce` are
vacuous for the phase). -/
theorem memSpaces_compute {r : AsyncCopy.Ref} {a : Acc} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) :
    a.loc.space = .shared :=
  (touch_frame hpre (memTouches_compute hpre hX hr ht hσ hI)).1

/-- **`DirectFacts.sharedFrame` for the Compute phase**: every access is in the first 98304
bytes (in fact the first 95104: the state copy, the input stages and the output stages) of the
window of the issuing thread's own block. -/
theorem sharedFrame_compute {r : AsyncCopy.Ref} {a : Acc} (hr : r.issuer = (g, k))
    (ht : X.MemTouches r a) (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) :
    a.loc.cta = g / L.block ∧ P.sharedBase ≤ a.loc.addr ∧
      a.loc.addr + a.size ≤ P.sharedBase + 98304 := by
  obtain ⟨-, h1, h2, h3⟩ := touch_frame hpre (memTouches_compute hpre hX hr ht hσ hI)
  exact ⟨h1, h2, by omega⟩

/-- **No tensor copy is issued at a state of the invariant**: the fields `loadFill`,
`loadBounds` and `storeBounds` of `DirectFacts` are vacuous for the phase. -/
theorem no_tensor_compute (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) :
    (∀ al sp, e.kind ≠ .tensorIssue al sp) ∧ ∀ al sp, e.kind ≠ .tensorStore al sp := by
  have hfk := site_fires (sounds hpre) hX he hσ
  have hne : s.site.kind ≠ .tensorCopy := by
    obtain ⟨pos, hR, -⟩ := hI
    cases pos with
    | entry =>
      have h5 : s.site = .bar 5 := hR.site
      rw [h5]
      exact fun h => by cases h
    | tile t n =>
      have hat : (skOf n).At s.site := hR.site
      rw [kind_of_at hat]
      cases skOf n <;> exact fun h => by cases h
  constructor
  · intro al sp hk
    rw [hk] at hfk
    cases hκ : s.site.kind <;> rw [hκ] at hfk <;> first
      | exact hne hκ
      | cases hfk
  · intro al sp hk
    rw [hk] at hfk
    cases hκ : s.site.kind <;> rw [hκ] at hfk <;> first
      | exact hne hκ
      | cases hfk

/-! ### The matrix schedule: `matrixShape`, `matrixCount` -/

/-- **`DirectFacts.matrixShape` for the Compute phase**: a matrix event at a state of the
invariant is at the matrix instruction of the code whose number is the event's ordinal modulo
182, and has that instruction's operation. -/
theorem matrixShape_compute {pc : Nat} {op : MatrixOp} {own recv : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .matrix op own recv⟩) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) :
    Top.matrixSites[((X.tr g).take k).countP isMatrix % 182]? = some (pc, op) := by
  obtain ⟨t, n, m, hn, ht, hc, hR, hms, hlt, hord, hmat⟩ := matrix_pos hpre hX he rfl hσ hI
  have hmat' : ((X.tr g).take k).countP isMatrix = 182 * t + matOf n := hmat
  have hmod : ((X.tr g).take k).countP isMatrix % 182 = matOf n := by omega
  rw [hmod]
  have hat : (skOf n).At s.site := hR.site
  have hsome : (msOf (skOf n)).isSome = true := by rw [hms]; rfl
  have hpcs := matPc_table n hn hsome
  rw [← matPcs_eq, List.getElem?_map, ← pc_of_at hat] at hpcs
  obtain ⟨⟨pc', op'⟩, hget, hpc'⟩ := Option.map_eq_some_iff.mp hpcs
  dsimp only at hpc'
  subst hpc'
  obtain ⟨ins', i, hcode, hop, hiop⟩ := matrixSites_get hget
  obtain ⟨tt, ins, o, hatD, -, hcd, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  obtain rfl : ins' = ins := Option.some.inj (hcode.symm.trans hcd)
  rw [hop] at hf
  have hf' : Fires s.site.pc (matrixTmpl L g tt i) ⟨pc, .matrix op own recv⟩ o := hf
  have hopq := matrix_op hf' rfl
  have hpc : pc = s.site.pc := Frame.event_pc (sounds hpre) hX he hσ
  rw [hget, hpc, hopq, hiop]

omit hX in
/-- **`DirectFacts.matrixCount` for the Compute phase, the bound**: a compute thread whose
pending state satisfies the invariant has made at most `Top.matrixTotal` matrix events. -/
theorem matrixCount_compute (hI : Inv P L X g j0 (X.tr g).length s) :
    (X.tr g).countP isMatrix ≤ Top.matrixTotal P L g := by
  have hc : tid g < 128 := by
    obtain ⟨pos, hR, -⟩ := hI
    cases pos with
    | entry => exact hR.facts.compute
    | tile t n => exact hR.facts.compute
  have h := count_compute hpre hI
  rw [tileCount_eq hpre] at h
  rw [matrixTotal_eq hpre hc]
  exact h

omit hX in
/-- **`DirectFacts.matrixCount` for the Compute phase, at the exit**: a compute thread at the
exit of the phase has made exactly `Top.matrixTotal` matrix events. The Epilogue carries the
equality to the thread's `exit` event (it makes no matrix event). -/
theorem matrixCount_out {j : Nat} {s1 : D} (hO : Out P L X g j0 j s1) :
    ((X.tr g).take j).countP isMatrix = Top.matrixTotal P L g := by
  rw [matrixTotal_eq hpre hO.1.compute]
  exact count_out hO

/-- **No `exit` event at a state of the invariant**: the thread exits in the Epilogue (the
clause "if the thread exits" of `matrixCount` and of `ComputeRef.count` is the Epilogue's). -/
theorem not_exit_compute {pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) : False := by
  obtain ⟨j, hs⟩ := exit_site (sounds hpre) hX he hσ rfl
  have hne : s.site ≠ .bar 5 := by
    rw [hs]
    exact fun h => by cases h
  obtain ⟨t, n, hn, ht, hc, hR, hled, -⟩ := tile_of hI hne
  have hat : (skOf n).At s.site := hR.site
  have h := SK.at_iff.mp hat
  rw [hs] at h
  cases h

/-! ### Undefined behaviour and dead states: the control half of `computeNoUb` -/

/-- **An undefined-behaviour event at a state of the invariant** is at an `mma.sync`, at a
`movmatrix` or at the first event of an `stmatrix`: the instructions that read data registers
to build their matrix event (the value layer shows that those registers hold 32-bit values).
At the entry, the polls, the row reads, the second events of the `ldmatrix`, the row writes,
the scalar loads, the named barrier, the fence and the arrivals the event is never undefined
behaviour. -/
theorem ub_compute (hg : g < L.threads) {pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hσ : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) :
    (∃ j, s.site = .warpMma j) ∨ (∃ j, s.site = .matrixMove j) ∨
      ∃ j, s.site = .matrixStore j := by
  obtain ⟨pos, hR, -, -, -⟩ := hI
  obtain ⟨site, w, p, x⟩ := s
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  cases pos with
  | entry =>
    obtain rfl : site = .bar 5 := hR.site
    cases ev_entry hc hf
  | tile t n =>
    have hn : n < 268 := hR.facts.pos
    have hs : (skOf n).At site := hR.site
    have hT : Tile P L g t n w p x := hR.facts
    rcases kind_table n hn with hacc | hctl | hmat
    · obtain ⟨r, c, sz, -, -, hev⟩ := access_at hpre hT hs hat hc hf hacc
      rcases hev with ⟨bs, -, hk⟩ | ⟨j, row, -, hk⟩ <;> cases hk
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hctl
      rcases hctl with rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl : site = .mbarWait 7 := hs
        obtain ⟨ok, h⟩ := ev_pollE hpre hT hat hc hf
        cases h
      · obtain rfl : site = .mbarWait 8 := hs
        obtain ⟨ok, h⟩ := ev_pollF hpre hT hat hc hf
        cases h
      · obtain rfl : site = .bar 6 := hs
        cases ev_bar8 hpre hT hat hc hf
      · obtain rfl : site = .fenceProxy 2 := hs
        cases ev_fence hc hf
      · obtain rfl : site = .mbarArrive 4 := hs
        cases ev_arriveF hpre hT hat hc hf
      · obtain rfl : site = .mbarArrive 5 := hs
        cases ev_arriveE hpre hg hT hat hc hf
    · cases hsk : skOf n with
      | ldMx j =>
        exfalso
        have hkind : kindOf (skOf n) = .matrixLoadMx := by rw [hsk]; rfl
        have hld := ldMx_table n hn hkind
        rw [← pc_of_at hs, hc] at hld
        obtain ⟨i, m, hop, hmv, hst, hrule⟩ := isLd_spec hld
        rw [hsk] at hs
        obtain ⟨row, rfl⟩ := hs
        have hsub : tt.sub = 1 := hat.2.1
        rw [hop] at hf
        obtain ⟨own, recv, h⟩ := ev_ldMx (by rw [hpre.block]) hrule hmv hst
          (by rw [hsub]; exact Nat.one_ne_zero) hf
        cases h
      | mma j =>
        rw [hsk] at hs
        exact .inl ⟨j, hs⟩
      | mv j =>
        rw [hsk] at hs
        exact .inr (.inl ⟨j, hs⟩)
      | st j =>
        rw [hsk] at hs
        exact .inr (.inr ⟨j, hs⟩)
      | wait j => rw [hsk] at hmat; cases hmat
      | ld j => rw [hsk] at hmat; cases hmat
      | stWr j => rw [hsk] at hmat; cases hmat
      | load j => rw [hsk] at hmat; cases hmat
      | bar j => rw [hsk] at hmat; cases hmat
      | fence j => rw [hsk] at hmat; cases hmat
      | arrive j => rw [hsk] at hmat; cases hmat

/-- **No dead state on the control side**: after the event of a state of the invariant at a
barrier, a poll, the proxy fence or an arrival (the entry and the six control positions of a
tile) the machine follows the thread at a state again. -/
theorem next_control (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) (hI : Inv P L X g j0 k s) (hs : s.site.kind ∈ ctlKinds) :
    ∃ s', At (code L) X g (k + 1) s' := by
  obtain ⟨pos, hR, -, -, -⟩ := hI
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  have hctl : pos.control := by
    cases pos with
    | entry => trivial
    | tile t n =>
      have hat' : (skOf n).At s.site := hR.site
      rw [kind_of_at hat'] at hs
      exact ctl_table n hR.facts.pos hs
  obtain ⟨s', hs'⟩ := ok_control hpre hg hR hctl hat hc hf
  refine ⟨s', ?_⟩
  show Frame.stateAt (code L) X g (k + 1) = some (some s')
  rw [Frame.stateAt_succ he, hσ]
  exact hs'

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Vals
