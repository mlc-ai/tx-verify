-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution

@[expose] public section

/-! # Warp-level matrix instructions: what a lane receives from an instance

A proof tool, generic over the kernel: the value ("source") lemmas of `ldmatrix`, `stmatrix`,
`movmatrix` and `mma.sync`. A thread's own rule leaves the bytes a matrix event receives free;
Core fixes them with the execution rule `Consistent.matrix : MatrixOk L A X` (DEP-WARP-MATRIX,
DEP-WARP-MMA). The three files of `Lemmas/Matrix/` turn that rule into closed forms:

* `Lemmas/Matrix/Instance.lean` (this file): from a consistent execution and the events of the
  32 lanes of a warp at one ordinal, each lane received `matrixRecv` of the instance
  (`recv_of_matrixInstance`, `recv_of_instance`, `recv_of_instance_at`, and one corollary per
  operation: `recv_move`, `recv_transpose`, `recv_mma`). It also relates the ordinal of a matrix
  event (`Execution.MatrixK`) to positions of the thread's trace (`matrixK_iff`,
  `matrixK_of_append`, `matrixK_index_unique`, `exists_matrixK_of_lt_countP`).
* `Lemmas/Matrix/Move.lean`: the bytes and the 16-bit elements that the `.x4.m8n8.b16` loads and
  stores and `movmatrix` move.
* `Lemmas/Matrix/Mma.lean`: the real numbers that
  `mma.sync.aligned.m16n8k16.row.col.f32.bf16.bf16.f32` computes under the ideal-real assumption.

## The instance

A warp is 32 consecutive threads of a CTA whose size is a multiple of 32. Its first thread `w`
has lane 0 (`laneOf L w = 0`, that is `w % L.block % 32 = 0`: the index of `w` within its CTA
is a multiple of 32), and thread `w + l` is lane `l` (`laneOf_add`). Each thread numbers its own
matrix events 0, 1, 2, … in trace order (`Execution.MatrixK`, the ordinal). The `n`-th instance
of the warp consists of the `n`-th matrix event of every lane; it exists when all 32 lanes
perform that event at one source position `pc` with one operation `op` (`WarpInstance`, Core's
`MatrixInstance` restated from the warp's first thread). Lane `l` contributes the bytes `parts l`
and receives `matrixRecv A op parts l`. Only the contributions of the 32 lanes matter, and the
execution determines them (`WarpInstance.unique`).

## The layouts, in words

Write lane `l = 4 g + t` with group `g = l / 4` (0 to 7) and thread in group `t = l % 4`.
An 8×8 matrix of 16-bit elements is held by a warp one 32-bit register per lane: lane `4 g + t`
holds row `g`, columns `2 t` (low half of the register) and `2 t + 1` (high half).

* `ldmatrix.x4.m8n8.b16`: lane `8 r + i` supplies the address of the 16-byte memory row `i` of
  matrix `r` (`r` = 0 to 3) and reads those 16 bytes itself. Destination register `r` of lane
  `4 g + t` receives elements `2 t` and `2 t + 1` of memory row `g` of matrix `r`. With `.trans`
  it receives element `g` of memory rows `2 t` and `2 t + 1`: the registers hold the transposed
  matrix.
* `stmatrix.x4.m8n8.b16` is the inverse: lane `8 r + i` writes memory row `i` of matrix `r`, whose
  element `j` comes from source register `r` of lane `4 i + j / 2`, half `j % 2`; with `.trans`
  from lane `4 j + i / 2`, half `i % 2`.
* `movmatrix.m8n8.trans.b16`: the destination register holds the transpose of the 8×8 matrix
  that the 32 source registers hold: half `h` of lane `4 g + t` is half `g % 2` of the source
  register of lane `4 (2 t + h) + g / 2`.
* `mma.m16n8k16` with bf16 A and B and f32 C and D computes `D = A · B + C` for a 16×16 `A`, a
  16×8 `B` and 16×8 `C`, `D`. Lane `4 g + t` holds: in A register `r` (0 to 3) the elements of
  row `g + 8 (r % 2)`, columns `2 t + 8 (r / 2)` and `2 t + 1 + 8 (r / 2)`; in B register `r`
  (0 or 1) rows `8 r + 2 t` and `8 r + 2 t + 1` of column `g`; in C and D register `r` (0 to 3)
  the element of row `g + 8 (r / 2)` and column `2 t + r % 2`.
-/

namespace PTX.WarpMatrix

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## Ordinals of matrix events and positions of the trace -/

/-- The number of matrix events of thread `g` before position `i` of its trace: the ordinal of
a matrix event at position `i`. -/
def ordinal (X : Execution) (g i : Nat) : Nat := ((X.tr g).take i).countP isMatrix

/-- `Execution.MatrixK` in terms of the trace: position `i` of thread `g` holds a matrix event
and `n` matrix events come before it. -/
theorem matrixK_iff {g i n : Nat} :
    X.MatrixK (g, i) n ↔
      (∃ ev, (X.tr g)[i]? = some ev ∧ isMatrix ev = true) ∧
        ((X.tr g).take i).countP isMatrix = n :=
  Iff.rfl

/-- A matrix event has the ordinal `ordinal X g i`. -/
theorem matrixK_of_get {g i pc : Nat} {op : MatrixOp} {own recv : List (Option Byte)}
    (h : X.get (g, i) = some ⟨pc, .matrix op own recv⟩) : X.MatrixK (g, i) (ordinal X g i) :=
  ⟨⟨_, h, rfl⟩, rfl⟩

/-- The ordinal of a matrix event is the count of the matrix events before it. -/
theorem matrixK_ordinal {g i n : Nat} (h : X.MatrixK (g, i) n) : ordinal X g i = n := h.2

/-- An event has one ordinal. -/
theorem matrixK_ordinal_unique {e : EvId} {n n' : Nat} (h : X.MatrixK e n) (h' : X.MatrixK e n') :
    n = n' := h.2.symm.trans h'.2

/-- A trace that splits as `pre ++ ev :: post` at a matrix event `ev` has that event at position
`pre.length` with ordinal `pre.countP isMatrix`. -/
theorem matrixK_of_append {g : Nat} {pre post : List Event} {ev : Event}
    (htr : X.tr g = pre ++ ev :: post) (hm : isMatrix ev = true) :
    X.MatrixK (g, pre.length) (pre.countP isMatrix) := by
  refine ⟨⟨ev, ?_, hm⟩, ?_⟩
  · simp [Execution.get, htr]
  · simp [htr]

/-- The count of matrix events grows along the trace. -/
theorem ordinal_mono {g i j : Nat} (h : i ≤ j) : ordinal X g i ≤ ordinal X g j :=
  (List.take_sublist_take_left h).countP_le

/-- One step past a matrix event the count is one more. -/
theorem ordinal_succ_of_matrixK {g i n : Nat} (h : X.MatrixK (g, i) n) :
    ordinal X g (i + 1) = n + 1 := by
  obtain ⟨⟨ev, hg, hm⟩, hn⟩ := h
  have hg' : (X.tr g)[i]? = some ev := hg
  simp only [ordinal, List.take_add_one, hg', List.countP_append] at hn ⊢
  simp [hn, hm]

/-- One step past an event that is not a matrix event the count is unchanged. -/
theorem ordinal_succ_of_not_matrix {g i : Nat} {ev : Event} (hg : X.get (g, i) = some ev)
    (hm : isMatrix ev = false) : ordinal X g (i + 1) = ordinal X g i := by
  have hg' : (X.tr g)[i]? = some ev := hg
  simp [ordinal, List.take_add_one, hg', List.countP_append, hm]

/-- A later matrix event of a thread has a larger ordinal. -/
theorem matrixK_lt_of_lt {g i j n n' : Nat} (h : X.MatrixK (g, i) n) (h' : X.MatrixK (g, j) n')
    (hij : i < j) : n < n' := by
  have h1 := ordinal_succ_of_matrixK h
  have h2 : ordinal X g (i + 1) ≤ ordinal X g j := ordinal_mono hij
  have h3 := matrixK_ordinal h'
  omega

/-- The matrix events of a thread are ordered by their ordinals. -/
theorem matrixK_lt_iff {g i j n n' : Nat} (h : X.MatrixK (g, i) n) (h' : X.MatrixK (g, j) n') :
    i < j ↔ n < n' := by
  refine ⟨matrixK_lt_of_lt h h', fun hn => ?_⟩
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact hij
  · subst hij
    have := matrixK_ordinal_unique h h'
    omega
  · have := matrixK_lt_of_lt h' h hij
    omega

/-- A thread has one matrix event of each ordinal. -/
theorem matrixK_index_unique {g i j n : Nat} (h : X.MatrixK (g, i) n) (h' : X.MatrixK (g, j) n) :
    i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := matrixK_lt_of_lt h h' hij
    omega
  · exact hij
  · have := matrixK_lt_of_lt h' h hij
    omega

/-- The ordinal of a matrix event is less than the thread's number of matrix events. -/
theorem matrixK_lt_countP {g i n : Nat} (h : X.MatrixK (g, i) n) :
    n < (X.tr g).countP isMatrix := by
  have h1 := ordinal_succ_of_matrixK h
  have h2 : ordinal X g (i + 1) ≤ (X.tr g).countP isMatrix :=
    (List.take_sublist _ _).countP_le
  omega

private theorem exists_of_lt_countP (p : Event → Bool) :
    ∀ (es : List Event) (n : Nat), n < es.countP p →
      ∃ i ev, es[i]? = some ev ∧ p ev = true ∧ (es.take i).countP p = n
  | [], n, h => by simp at h
  | e :: es, n, h => by
    by_cases he : p e = true
    · cases n with
      | zero => exact ⟨0, e, rfl, he, rfl⟩
      | succ n =>
        have hn : n < es.countP p := by
          simp only [List.countP_cons, he, ite_true] at h
          omega
        obtain ⟨i, ev, hi, hp, hc⟩ := exists_of_lt_countP p es n hn
        exact ⟨i + 1, ev, by simpa using hi, hp, by simp [he, hc]⟩
    · have hn : n < es.countP p := by simpa [List.countP_cons, he] using h
      obtain ⟨i, ev, hi, hp, hc⟩ := exists_of_lt_countP p es n hn
      exact ⟨i + 1, ev, by simpa using hi, hp, by simp [he, hc]⟩

/-- A thread with more than `n` matrix events has a matrix event of ordinal `n`. -/
theorem exists_matrixK_of_lt_countP {g n : Nat} (h : n < (X.tr g).countP isMatrix) :
    ∃ i, X.MatrixK (g, i) n := by
  obtain ⟨i, ev, hi, hp, hc⟩ := exists_of_lt_countP isMatrix (X.tr g) n h
  exact ⟨i, ⟨ev, hi, hp⟩, hc⟩

/-! ## The lanes of a warp -/

/-- Thread `w + l` is lane `l` of the warp whose first thread is `w`, in a CTA whose size is a
multiple of 32 (the size every matrix instruction requires, THREAD-MATRIX). -/
theorem laneOf_add {w l : Nat} (hb : L.block % 32 = 0) (hw : laneOf L w = 0) (hl : l < 32) :
    laneOf L (w + l) = l := by
  unfold laneOf at hw ⊢
  rcases Nat.eq_zero_or_pos L.block with h0 | hpos
  · rw [h0, Nat.mod_zero] at hw ⊢
    omega
  · have hr : w % L.block < L.block := Nat.mod_lt _ hpos
    have hlt : w % L.block + l < L.block := by omega
    have hmod : (w + l) % L.block = w % L.block + l := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (a := l) (by omega), Nat.mod_eq_of_lt hlt]
    rw [hmod]
    omega

/-- The first thread of the warp of thread `g` has lane 0. -/
theorem laneOf_base (hb : L.block % 32 = 0) (g : Nat) : laneOf L (g - laneOf L g) = 0 := by
  unfold laneOf
  rcases Nat.eq_zero_or_pos L.block with h0 | hpos
  · simp only [h0, Nat.mod_zero]
    omega
  · have hr : g % L.block < L.block := Nat.mod_lt _ hpos
    have hg : g % L.block + L.block * (g / L.block) = g := Nat.mod_add_div g L.block
    generalize g % L.block = r at hr hg ⊢
    generalize g / L.block = q at hg
    subst hg
    have hle : r % 32 ≤ r := Nat.mod_le _ _
    have hsub : r + L.block * q - r % 32 = (r - r % 32) + L.block * q := by omega
    rw [hsub, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (a := r - r % 32) (b := L.block) (by omega)]
    omega

/-- **The instance of a warp, from its first thread.** The 32 lanes of the warp whose first
thread is `w` perform their `n`-th matrix events at source position `pc` with operation `op`;
lane `l` contributes the bytes `parts l`. Core's `MatrixInstance L X g n pc op parts` is this
statement for `w = g - laneOf L g` (`matrixInstance_iff`). -/
def WarpInstance (X : Execution) (w n pc : Nat) (op : MatrixOp)
    (parts : Nat → List (Option Byte)) : Prop :=
  ∀ lane < 32, ∃ j recv,
    X.get (w + lane, j) = some ⟨pc, .matrix op (parts lane) recv⟩ ∧ X.MatrixK (w + lane, j) n

/-- Core's instance of thread `g` is the instance of the warp's first thread. -/
theorem matrixInstance_iff {g n pc : Nat} {op : MatrixOp} {parts : Nat → List (Option Byte)} :
    MatrixInstance L X g n pc op parts ↔ WarpInstance X (g - laneOf L g) n pc op parts :=
  Iff.rfl

/-- Core's instance of lane `l` of the warp whose first thread is `w`. -/
theorem WarpInstance.matrixInstance {w n pc l : Nat} {op : MatrixOp}
    {parts : Nat → List (Option Byte)} (hI : WarpInstance X w n pc op parts)
    (hb : L.block % 32 = 0) (hw : laneOf L w = 0) (hl : l < 32) :
    MatrixInstance L X (w + l) n pc op parts := by
  rw [matrixInstance_iff, laneOf_add hb hw hl, Nat.add_sub_cancel]
  exact hI

/-- An instance depends only on what the 32 lanes contribute. -/
theorem WarpInstance.congr {w n pc : Nat} {op : MatrixOp} {parts parts' : Nat → List (Option Byte)}
    (hI : WarpInstance X w n pc op parts) (h : ∀ l < 32, parts l = parts' l) :
    WarpInstance X w n pc op parts' := fun lane hl => by
  rw [← h lane hl]
  exact hI lane hl

/-- The instance from the events of the lanes, each with its own contributed bytes. -/
theorem WarpInstance.of_events {w n pc : Nat} {op : MatrixOp} {parts : Nat → List (Option Byte)}
    (h : ∀ l < 32, ∃ j own recv, X.get (w + l, j) = some ⟨pc, .matrix op own recv⟩ ∧
      X.MatrixK (w + l, j) n ∧ own = parts l) : WarpInstance X w n pc op parts := fun l hl => by
  obtain ⟨j, own, recv, hg, hk, rfl⟩ := h l hl
  exact ⟨j, recv, hg, hk⟩

/-- The event of lane `l` in an instance is the lane's only matrix event of that ordinal. -/
theorem WarpInstance.event_eq {w n pc l i pc' : Nat} {op op' : MatrixOp}
    {parts : Nat → List (Option Byte)} {own recv : List (Option Byte)}
    (hI : WarpInstance X w n pc op parts) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    pc' = pc ∧ op' = op ∧ own = parts l := by
  obtain ⟨j, recv', hg, hk'⟩ := hI l hl
  have hij := matrixK_index_unique hk hk'
  subst hij
  rw [he] at hg
  cases hg
  exact ⟨rfl, rfl, rfl⟩

/-- **An instance is determined by the execution.** Two descriptions of the `n`-th instance of
one warp have the same source position and operation, and the same contributed bytes in each of
the 32 lanes. (Core's `MatrixUnsafe` quantifies over the contributions `parts`; this pins them
to the ones at hand.) -/
theorem WarpInstance.unique {w n pc pc' : Nat} {op op' : MatrixOp}
    {parts parts' : Nat → List (Option Byte)} (hI : WarpInstance X w n pc op parts)
    (hI' : WarpInstance X w n pc' op' parts') :
    pc' = pc ∧ op' = op ∧ ∀ l < 32, parts' l = parts l := by
  obtain ⟨j, recv, hg, hk⟩ := hI' 0 (by decide)
  obtain ⟨rfl, rfl, -⟩ := hI.event_eq (by decide) hg hk
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  obtain ⟨j, recv, hg, hk⟩ := hI' l hl
  exact (hI.event_eq hl hg hk).2.2

/-! ## What a lane receives -/

/-- The result of a matrix load or store is `matrixMoveRecv`; it is never an error. -/
theorem matrixRecv_move (A : List Assumption) (m : MatrixMove)
    (parts : Nat → List (Option Byte)) (l : Nat) :
    matrixRecv A (.move m) parts l = .ok (matrixMoveRecv m parts l) :=
  rfl

/-- The result of `movmatrix` is the bytes of `transposeRecv`; it is never an error. -/
theorem matrixRecv_transpose (A : List Assumption) (parts : Nat → List (Option Byte)) (l : Nat) :
    matrixRecv A .transpose parts l = .ok (.bytes (transposeRecv parts l)) :=
  rfl

/-- The result of an MMA whose D registers `mmaRecv` computes. -/
theorem matrixRecv_mma_ok {A : List Assumption} {s : MmaSpec} {parts : Nat → List (Option Byte)}
    {l : Nat} {bs : List (Option Byte)} (h : mmaRecv A s parts l = .ok bs) :
    matrixRecv A (.mma s) parts l = .ok (.bytes bs) := by
  simp [matrixRecv, h]

/-- **Core's rule, for one event.** A matrix event of thread `g` whose warp has an instance at
its ordinal received the bytes `matrixRecv` computes for its lane. -/
theorem recv_of_matrixInstance (hX : Consistent L K A mem0 X) {g i pc n : Nat} {op : MatrixOp}
    {own recv bs : List (Option Byte)} {parts : Nat → List (Option Byte)}
    (he : X.get (g, i) = some ⟨pc, .matrix op own recv⟩) (hk : X.MatrixK (g, i) n)
    (hI : MatrixInstance L X g n pc op parts)
    (hr : matrixRecv A op parts (laneOf L g) = .ok (.bytes bs)) : recv = bs := by
  have h := hX.matrix g i pc op own recv n he hk parts hI
  rw [hr] at h
  exact h

/-- **What lane `l` received from an instance.** In a consistent execution, if the 32 lanes of
the warp whose first thread is `w` perform their `n`-th matrix events at `pc` with operation `op`
and contributions `parts`, then the `n`-th matrix event of lane `l` is at `pc`, has operation
`op`, contributed `parts l` and received the bytes of `matrixRecv A op parts l`. -/
theorem recv_of_instance (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {w n pc l : Nat}
    {op : MatrixOp} {parts : Nat → List (Option Byte)} {bs : List (Option Byte)}
    (hw : laneOf L w = 0) (hI : WarpInstance X w n pc op parts) (hl : l < 32)
    (hr : matrixRecv A op parts l = .ok (.bytes bs)) :
    ∃ j, X.get (w + l, j) = some ⟨pc, .matrix op (parts l) bs⟩ ∧ X.MatrixK (w + l, j) n := by
  obtain ⟨j, recv, hg, hk⟩ := hI l hl
  have h := recv_of_matrixInstance hX hg hk (hI.matrixInstance hb hw hl)
    (by rw [laneOf_add hb hw hl]; exact hr)
  subst h
  exact ⟨j, hg, hk⟩

/-- **What a given event of lane `l` received.** The form of `recv_of_instance` for an event
already at hand: it is the lane's event of the instance, so its position, operation and
contributed bytes are the instance's and its received bytes are `matrixRecv`'s. -/
theorem recv_of_instance_at (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {w n pc l i pc' : Nat} {op op' : MatrixOp} {parts : Nat → List (Option Byte)}
    {own recv bs : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc op parts) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n)
    (hr : matrixRecv A op parts l = .ok (.bytes bs)) :
    pc' = pc ∧ op' = op ∧ own = parts l ∧ recv = bs := by
  obtain ⟨rfl, rfl, rfl⟩ := hI.event_eq hl he hk
  exact ⟨rfl, rfl, rfl, recv_of_matrixInstance hX he hk (hI.matrixInstance hb hw hl)
    (by rw [laneOf_add hb hw hl]; exact hr)⟩

/-- A matrix load or store: the lane received the bytes of `matrixMoveRecv` (closed forms in
`Lemmas/Matrix/Move.lean`). -/
theorem recv_move (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {w n pc l i pc' : Nat}
    {m : MatrixMove} {op' : MatrixOp} {parts : Nat → List (Option Byte)}
    {own recv bs : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc (.move m) parts) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n)
    (hr : matrixMoveRecv m parts l = .bytes bs) : recv = bs :=
  (recv_of_instance_at hX hb hw hI hl he hk (by rw [matrixRecv_move, hr])).2.2.2

/-- `movmatrix`: the lane received the bytes of `transposeRecv`. -/
theorem recv_transpose (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    {w n pc l i pc' : Nat} {op' : MatrixOp} {parts : Nat → List (Option Byte)}
    {own recv : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc .transpose parts) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n) :
    recv = transposeRecv parts l :=
  (recv_of_instance_at hX hb hw hI hl he hk (matrixRecv_transpose A parts l)).2.2.2

/-- An MMA: the lane received the bytes of its D registers, when `mmaRecv` computes them. -/
theorem recv_mma (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0) {w n pc l i pc' : Nat}
    {s : MmaSpec} {op' : MatrixOp} {parts : Nat → List (Option Byte)}
    {own recv bs : List (Option Byte)} (hw : laneOf L w = 0)
    (hI : WarpInstance X w n pc (.mma s) parts) (hl : l < 32)
    (he : X.get (w + l, i) = some ⟨pc', .matrix op' own recv⟩) (hk : X.MatrixK (w + l, i) n)
    (hr : mmaRecv A s parts l = .ok bs) : recv = bs :=
  (recv_of_instance_at hX hb hw hI hl he hk (matrixRecv_mma_ok hr)).2.2.2

end PTX.WarpMatrix
