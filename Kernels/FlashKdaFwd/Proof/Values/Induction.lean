-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Hyps
public import Kernels.FlashKdaFwd.Proof.Values.Tables

@[expose] public section

/-!
# The invariant of the value induction and its steps

**The invariant.** For a compute warp with first thread `w0` and warp number `w`, and a family
`xs` of the real arrays of each tile (`xs b : Math.Fragments.Inputs`):

* A *program point* (`Pt`, `Sites.lean`) is a site of the thread machine at which a lane waits
  for an event of the tile's data path. `Pt.At x w l d pt` says the state `d` of lane `l` is at
  that point, and, at the second event of a load or a store, that the row it holds is the row
  of the arrays `x` (`LoadSrc.RowOk`, `StoreSrc.row`). `PtOk` adds the register table of the
  point: the data slots `d.x` satisfy it on `x`.
* `SiteOk x w l n d`: a lane that has made `n` matrix events of its tile is at one of the
  points of that count (`pointsAt n`) and satisfies it.
* Between the last store of a tile and the first load of the next, a lane is at the row write
  of that store or at a control site of the loop's tail (`TailSite`: the `bar.sync`, the fence,
  the two mbarrier arrivals and the two polls, and the `bar.sync` after the exit branch), and
  its carries already satisfy the table of ordinal 0 on the arrays of the next tile (`TailOk`).
* `Inv`: the invariant of one state, with the number `N` of matrix events the lane has made:
  `SiteOk` for tile `N / 182` and count `N % 182`; or, when `N % 182 = 0`, `TailOk`, or the lane
  has left the loop (`Left`: it was at the site after the exit branch at an earlier position
  with the same count), or, when `N = 0`, it has not entered the loop yet (`¬ Entered`).
* `ValAt` is `Inv` at a position of a lane's trace; `Val` is `ValAt` at every position of every
  lane of the warp with a given number of matrix events.

**The steps.** `val_zero` and `val_succ` reduce `Val` to the *matrix step* (the state of a lane
after its matrix event of ordinal `N`, which uses `Val` at `N` for all 32 lanes:
`ptOk_at_event`) and the *local step* (across an event that is no matrix event). The matrix
steps are `mma_step`, `load_step`, `move_step`, `store_step` (and `store_last` for the last
store of a tile); they also give that the lane is alive after the event. The local steps are
stated per point (`PtStep`: a lane at the point, with an event that is no matrix event, moves to
a point of the same count): `rd_local`, `ld_local`, `wr_local` are real steps, `mx_local`,
`mma_local`, `mov_local`, `st_local` say that only a matrix event occurs there; `local_step`
assembles them for a count. After an `mma.sync`, a scalar load or the row write of a store the
machine may evaluate a run of scalar instructions; these steps take the run's condition `Cd`
and a proof `hpost` that it holds on registers that satisfy the table before the run (from
`Gen/Runs.lean`), so "the lane is alive after the run" is proved, not assumed. The generated
file `Gen/Steps.lean` applies the steps to each ordinal.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## Program points -/

/-- The machine's site is the site of the point (the row it holds is left open). -/
def Pt.Shape : Pt → Site → Prop
  | .rd j, s => s = .matrixLoad j
  | .mx j, s => ∃ row, s = .matrixLoadMx j row
  | .mma j, s => s = .warpMma j
  | .mov j, s => s = .matrixMove j
  | .st j, s => s = .matrixStore j
  | .wr j, s => ∃ row, s = .matrixStoreWr j row
  | .ld i, s => s = .load i

/-- **The state is at the point**, with the row of the arrays `x` at a second event. -/
def Pt.At (x : Inputs) (w l : ℕ) (d : D) : Pt → Prop
  | .rd j => d.site = .matrixLoad j
  | .mx j => ∃ row, d.site = .matrixLoadMx j row ∧ (loadSrc j).RowOk x w l row
  | .mma j => d.site = .warpMma j
  | .mov j => d.site = .matrixMove j
  | .st j => d.site = .matrixStore j
  | .wr j => ∃ row, d.site = .matrixStoreWr j row ∧ row = (storeSrc j).row x w l
  | .ld i => d.site = .load i

theorem Pt.At.shape {x : Inputs} {w l : ℕ} {d : D} {pt : Pt} (h : pt.At x w l d) :
    pt.Shape d.site := by
  cases pt with
  | mx j => obtain ⟨row, hs, -⟩ := h; exact ⟨row, hs⟩
  | wr j => obtain ⟨row, hs, -⟩ := h; exact ⟨row, hs⟩
  | _ => exact h

/-- A site is the site of one point only. -/
theorem Pt.shape_inj {p q : Pt} {s : Site} (hp : p.Shape s) (hq : q.Shape s) : p = q := by
  cases p <;> cases q <;>
    (first | (obtain rfl := hp) | (obtain ⟨_, rfl⟩ := hp)) <;>
    (first
      | (obtain ⟨_, hq'⟩ := hq; cases hq'; try rfl)
      | (cases hq; try rfl))

theorem Pt.ofMSite_shape {m : MSite} {s : Site} (h : m.At s) : (Pt.ofMSite m).Shape s := by
  cases m <;> exact h

/-- **The invariant at one point**: the state is at the point and its data slots satisfy the
point's table. -/
def PtOk (x : Inputs) (w l : ℕ) (q : Pt × Table) (d : D) : Prop :=
  q.1.At x w l d ∧ q.2.Holds x w l d.x

/-- **The invariant of a state inside a tile**: lane `l` of warp `w` has made `n` matrix events
of its tile, whose arrays are `x`; it is at one of the points of that count. -/
def SiteOk (x : Inputs) (w l n : ℕ) (d : D) : Prop := ∃ q ∈ pointsAt n, PtOk x w l q d

theorem pts_mem {n ip : ℕ} {q : Pt × Table} (h : (pointsAt n)[ip]? = some q) : q ∈ pointsAt n :=
  List.mem_of_getElem? h

/-- From `SiteOk` and the site of the state: the invariant at the point of that site (the
points of a count are distinct, `hnd`, and `(pt, T)` is one of them, `hT`). -/
theorem SiteOk.pick {x : Inputs} {w l n : ℕ} {d : D} (h : SiteOk x w l n d) {pt : Pt} {T : Table}
    {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup) (hT : (pointsAt n)[ip]? = some (pt, T))
    (hs : pt.Shape d.site) : PtOk x w l (pt, T) d := by
  obtain ⟨q, hq, hok⟩ := h
  have h1 : q.1 = pt := Pt.shape_inj hok.1.shape hs
  have hq' : q = (pt, T) := List.inj_on_of_nodup_map hnd hq (pts_mem hT) h1
  rw [← hq']
  exact hok

/-! ## The tail of a tile, the entry and the exit of the loop -/

/-- The control sites between the last store of a tile and the first load of the next, the
site after the exit branch of the loop, and the five traps that the checks of the tail branch
to (a thread at a trap has no further state; the reference layer shows they are not reached). -/
def TailSite (s : Site) : Prop :=
  s = .bar 6 ∨ s = .fenceProxy 2 ∨ s = .mbarArrive 4 ∨ s = .mbarArrive 5 ∨ s = .mbarWait 7 ∨
    s = .mbarWait 8 ∨ s = .bar 7 ∨ s = .trap 7 ∨ s = .trap 8 ∨ s = .trap 9 ∨ s = .trap 10 ∨
    s = .trap 11

/-- **The invariant between two tiles.** `xp` are the arrays of the tile that ended and `x`
those of the next: the lane is at the row write of the last store, holding the row of `xp`, or
at a control site of the tail, and its data slots satisfy the table of ordinal 0 on `x`. -/
def TailOk (xp x : Inputs) (w l : ℕ) (d : D) : Prop :=
  ((∃ row, d.site = .matrixStoreWr 17 row ∧ row = (storeSrc 17).row xp w l) ∨ TailSite d.site) ∧
    (tableAt 0).Holds x w l d.x

/-- The lane has been at the first `ldmatrix` of the tile loop at or before position `k`. -/
def Entered (X : Execution) (g k : ℕ) : Prop :=
  ∃ k' ≤ k, ∃ d, stateAt (code L) X g k' = some (some d) ∧
    (d.site = .matrixLoad 0 ∨ ∃ row, d.site = .matrixLoadMx 0 row)

/-- The lane was at the site after the exit branch of the tile loop at an earlier position,
with the number of matrix events it has now. -/
def Left (X : Execution) (g k : ℕ) : Prop :=
  ∃ k' < k, ordinal X g k' = ordinal X g k ∧
    ∃ d, stateAt (code L) X g k' = some (some d) ∧ d.site = .bar 7

/-- **The invariant of one state**: `d` is the state of lane `l` (thread `g`) before position
`k` of its trace, where it has made `N` matrix events. -/
def Inv (xs : ℕ → Inputs) (w l : ℕ) (X : Execution) (g k N : ℕ) (d : D) : Prop :=
  SiteOk (xs (N / 182)) w l (N % 182) d ∨
    (N % 182 = 0 ∧ 1 ≤ N / 182 ∧ TailOk (xs (N / 182 - 1)) (xs (N / 182)) w l d) ∨
    (N % 182 = 0 ∧ 1 ≤ N / 182 ∧ Left (L := L) X g k) ∨
    (N = 0 ∧ ¬ Entered (L := L) X g k)

/-- **The invariant at a position of a lane's trace.** -/
def ValAt (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 l k : ℕ) : Prop :=
  ∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
    Inv (L := L) xs w l X (w0 + l) k (ordinal X (w0 + l) k) d

/-- **The invariant of the warp after `N` matrix events.** -/
def Val (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 N : ℕ) : Prop :=
  ∀ l < 32, ∀ k, ordinal X (w0 + l) k = N → ValAt (L := L) xs w X w0 l k

/-! ## The induction on the number of matrix events -/

/-- A position past the end of a lane's trace: the state and the count do not change. -/
theorem valAt_of_none {xs : ℕ → Inputs} {w w0 l k : ℕ} (he : X.get (w0 + l, k) = none)
    (ih : ValAt (L := L) xs w X w0 l k) :
    ordinal X (w0 + l) (k + 1) = ordinal X (w0 + l) k ∧ ValAt (L := L) xs w X w0 l (k + 1) := by
  have hlen : (X.tr (w0 + l)).length ≤ k := by
    by_contra hlt
    have : (X.tr (w0 + l))[k]? = none := he
    rw [List.getElem?_eq_none_iff] at this
    omega
  have htake : (X.tr (w0 + l)).take (k + 1) = (X.tr (w0 + l)).take k := by
    rw [List.take_of_length_le (by omega), List.take_of_length_le hlen]
  have hord : ordinal X (w0 + l) (k + 1) = ordinal X (w0 + l) k := by
    simp only [ordinal, htake]
  have hst : stateAt (code L) X (w0 + l) (k + 1) = stateAt (code L) X (w0 + l) k := by
    unfold stateAt
    rw [htake]
  refine ⟨hord, fun d hd => ?_⟩
  rw [hord]
  have := ih d (hst ▸ hd)
  rcases this with h | h | ⟨h0, h1, k', hk', ho, hd'⟩ | ⟨h0, hne⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ⟨h0, h1, k', by omega, by rw [hord]; exact ho, hd'⟩))
  · refine .inr (.inr (.inr ⟨h0, fun ⟨k', hk', d', hd', hs'⟩ => ?_⟩))
    rcases Nat.lt_or_ge k' (k + 1) with hlt | hge
    · exact hne ⟨k', by omega, d', hd', hs'⟩
    · have hk1 : k' = k + 1 := by omega
      subst hk1
      exact hne ⟨k, le_rfl, d', hst ▸ hd', hs'⟩

/-- **`Val` at 0** from the first state of each lane and the local step. -/
theorem val_zero {xs : ℕ → Inputs} {w w0 : ℕ} (h0 : ∀ l < 32, ValAt (L := L) xs w X w0 l 0)
    (hloc : ∀ l < 32, ∀ k e, X.get (w0 + l, k) = some e → isMatrix e = false →
      ordinal X (w0 + l) k = 0 → ValAt (L := L) xs w X w0 l k →
      ValAt (L := L) xs w X w0 l (k + 1)) :
    Val (L := L) xs w X w0 0 := by
  intro l hl k
  induction k with
  | zero => exact fun _ => h0 l hl
  | succ k ih =>
    intro hk
    cases he : X.get (w0 + l, k) with
    | none =>
      have hord : ordinal X (w0 + l) (k + 1) = ordinal X (w0 + l) k := by
        have hlen : (X.tr (w0 + l)).length ≤ k := by
          by_contra hlt
          have : (X.tr (w0 + l))[k]? = none := he
          rw [List.getElem?_eq_none_iff] at this
          omega
        simp only [ordinal, List.take_of_length_le (show (X.tr (w0 + l)).length ≤ k + 1 by omega),
          List.take_of_length_le hlen]
      exact (valAt_of_none he (ih (hord ▸ hk))).2
    | some e =>
      cases hmx : isMatrix e
      · have hord := ordinal_succ_of_not_matrix he hmx
        exact hloc l hl k e he hmx (hord ▸ hk) (ih (hord ▸ hk))
      · have hK : X.MatrixK (w0 + l, k) (ordinal X (w0 + l) k) := ⟨⟨e, he, hmx⟩, rfl⟩
        have hord := ordinal_succ_of_matrixK hK
        omega

/-- **`Val` at `N + 1`** from the matrix step at `N` and the local step at `N + 1`. -/
theorem val_succ {xs : ℕ → Inputs} {w w0 N : ℕ}
    (hm : ∀ l < 32, ∀ k, X.MatrixK (w0 + l, k) N → ValAt (L := L) xs w X w0 l (k + 1))
    (hloc : ∀ l < 32, ∀ k e, X.get (w0 + l, k) = some e → isMatrix e = false →
      ordinal X (w0 + l) k = N + 1 → ValAt (L := L) xs w X w0 l k →
      ValAt (L := L) xs w X w0 l (k + 1)) :
    Val (L := L) xs w X w0 (N + 1) := by
  intro l hl k
  induction k with
  | zero =>
    intro h
    simp [ordinal] at h
  | succ k ih =>
    intro hk
    cases he : X.get (w0 + l, k) with
    | none =>
      have hord : ordinal X (w0 + l) (k + 1) = ordinal X (w0 + l) k := by
        have hlen : (X.tr (w0 + l)).length ≤ k := by
          by_contra hlt
          have : (X.tr (w0 + l))[k]? = none := he
          rw [List.getElem?_eq_none_iff] at this
          omega
        simp only [ordinal, List.take_of_length_le (show (X.tr (w0 + l)).length ≤ k + 1 by omega),
          List.take_of_length_le hlen]
      exact (valAt_of_none he (ih (hord ▸ hk))).2
    | some e =>
      cases hmx : isMatrix e
      · have hord := ordinal_succ_of_not_matrix he hmx
        exact hloc l hl k e he hmx (hord ▸ hk) (ih (hord ▸ hk))
      · have hK : X.MatrixK (w0 + l, k) (ordinal X (w0 + l) k) := ⟨⟨e, he, hmx⟩, rfl⟩
        have hord := ordinal_succ_of_matrixK hK
        have hN : ordinal X (w0 + l) k = N := by omega
        exact hm l hl k (hN ▸ hK)

/-! ## The state of a lane at its matrix event, from the invariant -/

/-- **A lane at its matrix event of ordinal `N` is at the point of that event**, by `Val` at
`N`: the reference layer gives the site (`ComputeRef.site`); a lane in the tail or before the
loop is at another site, and a lane that left the loop makes no matrix event (`LoopExit` and
the count of matrix events, `ComputeRef.count`). -/
theorem ptOk_at_event (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) {xs : ℕ → Inputs}
    (IH : Val (L := L) xs w X w0 N) {pt : Pt} {T : Table} {ip : ℕ}
    (hpt : Pt.ofMSite (ordSite n) = pt) (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (pt, T)) {l k : ℕ} {d : D} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) (hσ : stateAt (code L) X (w0 + l) k = some (some d)) :
    PtOk (xs (N / 182)) w l (pt, T) d := by
  have ho := matrixK_ordinal hk
  have hinv := IH l hl k ho d hσ
  rw [ho] at hinv
  have hsite := R.site (w0 + l) k N d (W.compute l hl) hk hσ
  rw [hN] at hsite
  have hshape : pt.Shape d.site := hpt ▸ Pt.ofMSite_shape hsite
  have hmx : N % 182 = 0 → ∃ row, d.site = .matrixLoadMx 0 row := by
    intro h0
    have hn0 : n = 0 := by omega
    subst hn0
    exact hsite
  rcases hinv with h | ⟨h0, -, ht, -⟩ | ⟨h0, -, k', hk', ho', d0, hσ0, hs0⟩ | ⟨h0, hne⟩
  · rw [hN] at h
    exact h.pick hnd hT hshape
  · exfalso
    obtain ⟨row, hs⟩ := hmx h0
    rcases ht with ⟨row', hs', -⟩ | hs'
    · rw [hs] at hs'
      cases hs'
    · rw [hs] at hs'
      rcases hs' with h | h | h | h | h | h | h | h | h | h | h | h <;> cases h
  · exfalso
    have h1 := E (w0 + l) k' d0 (W.compute l hl) hσ0 hs0
    have h2 := matrixK_lt_countP hk
    have h3 := (R.count (w0 + l) (W.compute l hl)).1
    omega
  · exfalso
    obtain ⟨row, hs⟩ := hmx (by omega)
    exact hne ⟨k, le_rfl, d, hσ, .inr ⟨row, hs⟩⟩

/-- The invariant after a matrix event of ordinal `N` (not the last of the tile) at a point of
the next count. -/
theorem valAt_after {xs : ℕ → Inputs} {w w0 N n l k : ℕ} (hN : N % 182 = n) (hn : n + 1 < 182)
    (hk : X.MatrixK (w0 + l, k) N) {d' : D}
    (hσ' : stateAt (code L) X (w0 + l) (k + 1) = some (some d')) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt (n + 1)) (hok : PtOk (xs (N / 182)) w l q' d') :
    ValAt (L := L) xs w X w0 l (k + 1) := by
  intro d hd
  have ho := ordinal_succ_of_matrixK hk
  rw [ho]
  have h1 : (N + 1) / 182 = N / 182 := by omega
  have h2 : (N + 1) % 182 = n + 1 := by omega
  have hdd : d = d' := Option.some.inj (Option.some.inj (hd.symm.trans hσ'))
  refine .inl ?_
  rw [h1, h2, hdd]
  exact ⟨q', hq', hok⟩

/-- The end of a matrix step: the machine's transition gives the state after the event, which
is at a point of the next count. -/
theorem step_done {xs : ℕ → Inputs} {w w0 N n l k : ℕ} (hN : N % 182 = n) (hn : n + 1 < 182)
    (hk : X.MatrixK (w0 + l, k) N) {d d' : D} {e : Event} (he : X.get (w0 + l, k) = some e)
    (hσ : stateAt (code L) X (w0 + l) k = some (some d))
    (hnx : Thread.next L (w0 + l) d e = some (some d')) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt (n + 1)) (hok : PtOk (xs (N / 182)) w l q' d') :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  have hσ' : stateAt (code L) X (w0 + l) (k + 1) = some (some d') := by
    rw [stateAt_next he hσ]
    exact hnx
  exact ⟨⟨_, hσ'⟩, valAt_after hN hn hk hσ' hq' hok⟩

/-! ## The matrix step of a multiply-accumulate -/

/-- **The step across a multiply-accumulate.** `n` is an ordinal whose site is the `mma.sync`
at `pc` with the source registers `a0 … c3` (forms `regA A`, `regB B` and `regC C` or the zero
register in the table `T` of its point: `hchk`) and the destination registers `ds`, whose
result is the matrix `Z` (`hD`, an equation of `Math/Fragments.lean`). `hnext` is the machine's
transition at the site: a successor `after` under the condition `Cd` of the run of scalar
instructions that follows (`True` when there is none). `M` is the table after the event
(`hsub`), and `hpost` says that on slots that satisfy `M` the condition holds and the successor
is at the point `q'` of the next count. Then, from `Val` at `N` (all 32 lanes), a lane that
makes the event is alive after it and satisfies the invariant. -/
theorem mma_step (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) (hn : n + 1 < 182) {jj : Fin 104}
    (hord : ordSite n = .mma jj) {pc : ℕ} (hpc : (Site.warpMma jj).pc = pc) {ins : Instr}
    {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .mma mma16) (hrule : i.rule = some .threadMma)
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ}
    (hsrcs : i.srcs = [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map .reg)
    (hlive : ([a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].all fun r =>
      (Flow.live pc).contains r) = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.mma jj, T)) {A B Z : Mat} {C : Option Mat}
    (hchk : mmaCheck T [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3] A B C = true)
    (hD : ∀ x w, Z.eval x w = mmaReal (A.eval x w) (B.eval x w) (accEval x w C))
    {ds : List ℕ} (hdn : ds.Nodup) (hdl : ds.length = 4) {Cd : D → List Value → Prop}
    {after : Launch → ℕ → D → List Value → D}
    (hnext : ∀ (g : ℕ) (d : D) (own recv : List (Option Byte)) (vs : List Value),
      d.site = .warpMma jj → matrixVals 32 4 recv = .ok vs →
      Thread.next L g d ⟨pc, .matrix (.mma mma16) own recv⟩ =
        across (Cd d vs) (after L g d vs))
    {M : Table} (hsub : Table.sub M T (ds.zip (accForms Z)) = true) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt (n + 1))
    (hpost : ∀ x l g d vs, l < 32 → M.Holds x w l (valueEx d.x (ds.zip vs)) →
      Cd d vs ∧ PtOk x w l q' (after L g d vs))
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  have hordN : ordSite (N % 182) = .mma jj := by rw [hN]; exact hord
  have hgood : ∀ l' < 32, ∀ k' d', X.MatrixK (w0 + l', k') N →
      stateAt (code L) X (w0 + l') k' = some (some d') →
      d'.site = .warpMma jj ∧ T.Holds (xs (N / 182)) w l' d'.x := fun l' hl' k' d' hk' hσ' =>
    ptOk_at_event R E W hN IH (by rw [hord]; rfl) hnd hT hl' hk' hσ'
  obtain ⟨own, he⟩ := mma_event F R W hordN hpc hcode hins hop hrule hsrcs hlive
    (accOperands (xs (N / 182)) w A B C)
    (fun l' hl' k' d' hk' hσ' hs' => mma_values hchk (hgood l' hl' k' d' hk' hσ').2
      (R.zero _ _ _ _ (W.compute l' hl') hσ' hs'))
    hl hk
  obtain ⟨e, d, he', -, hσ⟩ := state_of_matrixK F hk
  obtain ⟨hs, hTd⟩ := hgood l hl k d hk hσ
  have hvs : matrixVals 32 4 _ = .ok ((List.range 4).map fun r => Value.float .f32
      (mmaReal (A.eval (xs (N / 182)) w) (B.eval (xs (N / 182)) w)
        (accEval (xs (N / 182)) w C) (cRow l r) (cCol l r))) := matrixVals_mma _ l
  have hM : M.Holds (xs (N / 182)) w l (valueEx d.x (ds.zip _)) :=
    Table.step hdn (by rw [hdl]; rfl) (by rw [hdl]; simp) hTd hsub fun r h =>
      accForms_hold (hD _ _) r (by rw [hdl] at h; exact h)
  obtain ⟨hc, hok⟩ := hpost _ l (w0 + l) d _ hl hM
  exact step_done hN hn hk he hσ ((hnext _ d _ _ _ hs hvs).trans (across_pos hc)) hq' hok

/-- **The event of a lane at a multiply-accumulate**: a lane at an `mma.sync` whose source
registers hold their forms makes the matrix event of the instruction, and contributes the
bytes of the registers of the real matrices `A`, `B` and `C`. -/
theorem mma_parts (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 w : ℕ} (W : Warp L w0)
    {jj : Fin 104} {pc : ℕ} (hpc : (Site.warpMma jj).pc = pc) {ins : Instr} {i : MatrixInstr}
    (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .mma mma16) (hrule : i.rule = some .threadMma)
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ}
    (hsrcs : i.srcs = [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map .reg)
    (hlive : ([a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].all fun r =>
      (Flow.live pc).contains r) = true)
    {T : Table} {A B : Mat} {C : Option Mat}
    (hchk : mmaCheck T [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3] A B C = true)
    {x : Inputs} {l k : ℕ} (hl : l < 32) {d : D} {e : Event}
    (hσ : stateAt (code L) X (w0 + l) k = some (some d)) (he : X.get (w0 + l, k) = some e)
    (hok : PtOk x w l (.mma jj, T) d) :
    ∃ recv, e = ⟨pc, .matrix (.mma mma16)
      (mmaParts (regA (A.eval x w)) (regB (B.eval x w)) (accRegs x w C) l) recv⟩ := by
  obtain ⟨hs, hT⟩ := hok
  have hs : d.site = .warpMma jj := hs
  have hz := R.zero _ _ _ _ (W.compute l hl) hσ hs
  have hv := mma_values (x := x) (w := w) (l := l) hchk hT hz
  have hpc' : d.site.pc = pc := by rw [hs]; exact hpc
  have hops := accOperands x w A B C
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
      · exact (hops.c l hl 0 (by omega)).bytes
      · exact (hops.c l hl 1 (by omega)).bytes
      · exact (hops.c l hl 2 (by omega)).bytes
      · exact (hops.c l hl 3 (by omega)).bytes
    exact fun r hr => hall _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hlive' : ∀ r ∈ [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3],
      r ∈ Flow.live d.site.pc := by
    intro r hr
    rw [hpc']
    simpa using List.all_eq_true.mp hlive r hr
  obtain ⟨recv, hrecv⟩ := mma_shape F he hσ (by rw [hpc']; exact hcode) hins hop hrule
    hsrcs rfl rfl hlive' hb4
  refine ⟨recv, ?_⟩
  rw [hrecv, hpc', hv, ownBytes_mma]

/-- **The local step at a multiply-accumulate**: a lane at an `mma.sync` whose source registers
hold their forms makes a matrix event next, so an event that is no matrix event does not occur
there. -/
theorem mma_local (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 w : ℕ} (W : Warp L w0)
    {jj : Fin 104} {pc : ℕ} (hpc : (Site.warpMma jj).pc = pc) {ins : Instr} {i : MatrixInstr}
    (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .mma mma16) (hrule : i.rule = some .threadMma)
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ}
    (hsrcs : i.srcs = [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map .reg)
    (hlive : ([a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].all fun r =>
      (Flow.live pc).contains r) = true)
    {T : Table} {A B : Mat} {C : Option Mat}
    (hchk : mmaCheck T [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3] A B C = true)
    {x : Inputs} {l k : ℕ} (hl : l < 32) {d : D} {e : Event}
    (hσ : stateAt (code L) X (w0 + l) k = some (some d)) (he : X.get (w0 + l, k) = some e)
    (hok : PtOk x w l (.mma jj, T) d) : isMatrix e = true := by
  obtain ⟨recv, rfl⟩ :=
    mma_parts F R W hpc hcode hins hop hrule hsrcs hlive hchk hl hσ he hok
  rfl

/-- **The operands of the multiply-accumulates** of the warp, at ordinal `N`: an instance of
an `mma` (all 32 lanes at their matrix event of ordinal `N`) is the bf16 `m16n8k16` form and
its lanes contribute the registers of real matrices (the statement of
`DirectFacts.mmaOperands`, for one warp and one ordinal). -/
def MmaClaim (X : Execution) (w0 N : ℕ) : Prop :=
  ∀ pc s parts, WarpInstance X w0 N pc (.mma s) parts →
    s = mma16 ∧ ∃ ra rb rc a b c, Operands ra rb rc a b c ∧
      ∀ l < 32, parts l = mmaParts ra rb rc l

/-- `MmaClaim` at an ordinal of an `mma.sync`, from `Val`. -/
theorem mma_claim (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) {jj : Fin 104}
    (hord : ordSite n = .mma jj) {pc : ℕ} (hpc : (Site.warpMma jj).pc = pc) {ins : Instr}
    {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .mma mma16) (hrule : i.rule = some .threadMma)
    {a0 a1 a2 a3 b0 b1 c0 c1 c2 c3 : ℕ}
    (hsrcs : i.srcs = [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].map .reg)
    (hlive : ([a0, a1, a2, a3, b0, b1, c0, c1, c2, c3].all fun r =>
      (Flow.live pc).contains r) = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.mma jj, T)) {A B : Mat} {C : Option Mat}
    (hchk : mmaCheck T [a0, a1, a2, a3, b0, b1, c0, c1, c2, c3] A B C = true)
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) : MmaClaim X w0 N := by
  intro pc' s parts hI
  have key : ∀ l < 32, s = mma16 ∧ parts l = mmaParts (regA (A.eval (xs (N / 182)) w))
      (regB (B.eval (xs (N / 182)) w)) (accRegs (xs (N / 182)) w C) l := by
    intro l hl
    obtain ⟨j, recv, he, hk⟩ := hI l hl
    obtain ⟨e, d, -, -, hσ⟩ := state_of_matrixK F hk
    have hok := ptOk_at_event R E W hN IH (by rw [hord]; rfl) hnd hT hl hk hσ
    obtain ⟨recv', he'⟩ :=
      mma_parts F R W hpc hcode hins hop hrule hsrcs hlive hchk hl hσ he hok
    injection he' with h1 h2
    injection h2 with h3 h4 h5
    injection h3 with h6
    exact ⟨h6, h4⟩
  exact ⟨(key 0 (by omega)).1, _, _, _, _, _, _, accOperands (xs (N / 182)) w A B C,
    fun l hl => (key l hl).2⟩

/-! ## The steps of a load -/

/-- `e` is a warp matrix event of an operation that is no multiply-accumulate. -/
def MoveEv (e : Event) : Prop :=
  ∃ pc op own recv, e = ⟨pc, .matrix op own recv⟩ ∧ ∀ s, op ≠ .mma s

theorem MoveEv.isMatrix {e : Event} (h : MoveEv e) : isMatrix e = true := by
  obtain ⟨pc, op, own, recv, rfl, -⟩ := h
  rfl

/-- Two matrix events of a thread with the same ordinal are the same event. -/
theorem matrixK_pos_unique {g i j n : ℕ} (h : X.MatrixK (g, i) n) (h' : X.MatrixK (g, j) n) :
    i = j := by
  rcases Nat.lt_trichotomy i j with h1 | h1 | h1
  · exact absurd (matrixK_lt_of_lt h h' h1) (lt_irrefl _)
  · exact h1
  · exact absurd (matrixK_lt_of_lt h' h h1) (lt_irrefl _)

/-- A list of 16 optional bytes, read back entry by entry. -/
theorem rowPart_getElem {row : List (Option Byte)} (h : row.length = 16) (s : ℕ) :
    rowPart (fun (_ : ℕ) k => row[k]?.join) s = row := by
  apply List.ext_getElem?
  intro k
  unfold rowPart
  by_cases hk : k < 16
  · have hk' : k < row.length := by omega
    simp [List.getElem?_eq_getElem hk', hk]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem VRow.length {x : Inputs} {w bi l : ℕ} {row : List (Option Byte)}
    (h : VRow x w bi l row) : row.length = 16 := by
  rcases h with ⟨n, -, rfl⟩ | ⟨-, rfl⟩ <;> simp

/-- **The rows of the 32 lanes at the matrix event of a load, and the values a lane
receives.** When every lane that is at the event holds a row of the source `s` (`hgood`), there
is one family `rows` of the 32 rows that the lanes hold; all its bytes are known; and the bytes
lane `l` receives rebuild into four values that satisfy the forms of the source. For a source
of payloads the rows are those of the arrays; for `v` they are the rows the lanes read (every
lane has made the event when one has), whatever bit patterns they hold. -/
theorem load_rows (F : Followed L mem0 X) (R : ComputeRef P L X) {w0 N : ℕ} (W : Warp L w0)
    {j : Fin 44} (hordN : ordSite (N % 182) = .load j) {x : Inputs} {w : ℕ} (s : LoadSrc)
    (hgood : ∀ l' < 32, ∀ k' d' row, X.MatrixK (w0 + l', k') N →
      stateAt (code L) X (w0 + l') k' = some (some d') → d'.site = .matrixLoadMx j row →
      s.RowOk x w l' row)
    {l k : ℕ} (hl : l < 32) (hk : X.MatrixK (w0 + l, k) N) :
    ∃ rows : ℕ → ℕ → Option Byte,
      (∀ l' < 32, ∀ k' d' row, X.MatrixK (w0 + l', k') N →
        stateAt (code L) X (w0 + l') k' = some (some d') → d'.site = .matrixLoadMx j row →
        row = rowPart rows l') ∧
      (∀ l' < 32, (rowPart rows l').all Option.isSome = true) ∧
      ∃ vs : List Value, matrixVals 32 4 (regPart (ldByte s.trans rows) l) = .ok vs ∧
        vs.length = 4 ∧
        ∀ r (h1 : r < s.forms.length) (h2 : r < vs.length), (s.forms[r]).Holds x w l vs[r] := by
  by_cases hpay : s.payload = true
  · refine ⟨matRows bf16Enc (s.tiles x w), ?_, fun l' _ => s.row_all x w l', s.vals x w l,
      s.vals_ok x w hl, s.vals_length x w l, ?_⟩
    · intro l' hl' k' d' row hk' hσ' hs'
      exact (LoadSrc.rowOk_payload hpay).mp (hgood l' hl' k' d' row hk' hσ' hs')
    · intro r h1 h2
      exact s.forms_hold x w l hpay r (by rw [LoadSrc.forms_length] at h1; exact h1)
  · cases s with
    | values bi =>
      have hex : ∀ l' : ℕ, ∃ row : List (Option Byte), l' < 32 →
          (VRow x w bi l' row ∧ ∀ k' d' row', X.MatrixK (w0 + l', k') N →
            stateAt (code L) X (w0 + l') k' = some (some d') →
            d'.site = .matrixLoadMx j row' → row' = row) := by
        intro l'
        by_cases hl' : l' < 32
        · obtain ⟨k', hk'⟩ := lanes_of_event F.consistent F.block W.lane0 hl hk
            (no_short_exit F R W hl hk) hl'
          obtain ⟨e', d', he', -, hσ'⟩ := state_of_matrixK F hk'
          have hs := R.site (w0 + l') k' N d' (W.compute l' hl') hk' hσ'
          rw [hordN] at hs
          obtain ⟨row, hs'⟩ : ∃ row, d'.site = .matrixLoadMx j row := hs
          refine ⟨row, fun _ => ⟨hgood l' hl' k' d' row hk' hσ' hs', ?_⟩⟩
          intro k'' d'' row' hk'' hσ'' hs''
          have hkk : k'' = k' := matrixK_pos_unique hk'' hk'
          subst hkk
          have hdd : d'' = d' := Option.some.inj (Option.some.inj (hσ''.symm.trans hσ'))
          subst hdd
          rw [hs'] at hs''
          cases hs''
          rfl
        · exact ⟨[], fun h => absurd h hl'⟩
      choose rowL hrowL using hex
      have hpart : ∀ l' < 32, rowPart (fun l'' k => (rowL l'')[k]?.join) l' = rowL l' :=
        fun l' hl' => rowPart_getElem (hrowL l' hl').1.length l'
      obtain ⟨v0, v1, v2, v3, hmv, f0, f1, f2, f3⟩ :=
        raw_vals (rows := fun l'' k => (rowL l'')[k]?.join) (x := x) (w := w) (bi := bi)
          (fun s' hs' => by rw [hpart s' hs']; exact (hrowL s' hs').1) hl
      refine ⟨fun l'' k => (rowL l'')[k]?.join, ?_, ?_, [v0, v1, v2, v3], hmv, rfl, ?_⟩
      · intro l' hl' k' d' row hk' hσ' hs'
        rw [hpart l' hl']
        exact (hrowL l' hl').2 k' d' row hk' hσ' hs'
      · intro l' hl'
        rw [hpart l' hl']
        exact (hrowL l' hl').1.all
      · intro r h1 h2
        have hr : r < 4 := h2
        interval_cases r
        · exact f0
        · exact f1
        · exact f2
        · exact f3
    | tilesA M => exact absurd rfl hpay
    | state bi m => exact absurd rfl hpay
    | restored m => exact absurd rfl hpay

/-- **The step across the matrix event of an `ldmatrix`.** `n` is an ordinal whose site is the
`j`-th `ldmatrix` with destination registers `ds`. From `Val` at `N` (every lane at the event
holds a row of the source), a lane that makes the event receives registers that satisfy the
forms of the source, is alive after it and satisfies the invariant at the point `q'` of the
next count. -/
theorem load_step (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) (hn : n + 1 < 182) {j : Fin 44}
    (hord : ordSite n = .load j) {ins : Instr} {i : MatrixInstr}
    (hcode : kernel.code[(Site.matrixLoad j).pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (ld4 (loadSrc j).trans)) (hrule : i.rule = some .threadMatrix)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.mx j, T)) {ds : List ℕ} (hdn : ds.Nodup)
    (hdl : ds.length = 4) {after : Launch → ℕ → D → List Value → D}
    (hnext : ∀ (g : ℕ) (d : D) (row own recv : List (Option Byte)) (vs : List Value),
      d.site = .matrixLoadMx j row → matrixVals 32 4 recv = .ok vs →
      Thread.next L g d ⟨(Site.matrixLoad j).pc, .matrix (.move (ld4 (loadSrc j).trans)) own recv⟩
        = some (some (after L g d vs)))
    (hx : ∀ g d vs, (after L g d vs).x = valueEx d.x (ds.zip vs)) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt (n + 1)) (hat : ∀ x l g d vs, q'.1.At x w l (after L g d vs))
    (hsub : Table.sub q'.2 T (ds.zip (loadSrc j).forms) = true)
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  have hordN : ordSite (N % 182) = .load j := by rw [hN]; exact hord
  have hgood : ∀ l' < 32, ∀ k' d' row, X.MatrixK (w0 + l', k') N →
      stateAt (code L) X (w0 + l') k' = some (some d') → d'.site = .matrixLoadMx j row →
      (loadSrc j).RowOk (xs (N / 182)) w l' row ∧ T.Holds (xs (N / 182)) w l' d'.x := by
    intro l' hl' k' d' row hk' hσ' hs'
    obtain ⟨⟨row', hs'', hr⟩, hTd⟩ :=
      ptOk_at_event R E W hN IH (by rw [hord]; rfl) hnd hT hl' hk' hσ'
    rw [hs'] at hs''
    cases hs''
    exact ⟨hr, hTd⟩
  obtain ⟨rows, hrows, hall, vs, hvs, hvl, hvf⟩ := load_rows F R W hordN (loadSrc j)
    (fun l' hl' k' d' row hk' hσ' hs' => (hgood l' hl' k' d' row hk' hσ' hs').1) hl hk
  obtain ⟨own, he⟩ := load_event F R W hordN hcode hins hop hrule hrows hall hl hk
  obtain ⟨e, d, he', -, hσ⟩ := state_of_matrixK F hk
  have hs := R.site (w0 + l) k N d (W.compute l hl) hk hσ
  rw [hordN] at hs
  obtain ⟨row, hs'⟩ : ∃ row, d.site = .matrixLoadMx j row := hs
  have hTd := (hgood l hl k d row hk hσ hs').2
  have hM : q'.2.Holds (xs (N / 182)) w l (valueEx d.x (ds.zip vs)) :=
    Table.step hdn (by rw [hdl, LoadSrc.forms_length]) (by rw [hdl, hvl]) hTd hsub
      fun r _ => hvf r _ _
  exact step_done hN hn hk he hσ (hnext _ d row _ _ _ hs' hvs) hq'
    ⟨hat _ _ _ _ _, by rw [hx]; exact hM⟩

/-! ## The statement of a local step, per point -/

/-- **The row a lane reads**, as a statement about one state `d` and its event `e`: if the state
is at the first event of an `ldmatrix`, the event is a read that returns a row of the load's
source for the arrays `x`. -/
def RowRead (x : Inputs) (w l : ℕ) (d : D) (e : Event) : Prop :=
  ∀ j : Fin 44, d.site = .matrixLoad j →
    ∃ pc a row, e = ⟨pc, .rd a row⟩ ∧ (loadSrc j).RowOk x w l row

/-- **The local step at a point.** A lane at the point `q` (of count `n`, in tile `N / 182`)
whose next event is no matrix event, and reads a row of its tile if it is a row read
(`RowRead`), is alive after it, at a point of the same count. -/
def PtStep (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 l k N n : ℕ) (q : Pt × Table) : Prop :=
  ∀ d e, stateAt (code L) X (w0 + l) k = some (some d) → X.get (w0 + l, k) = some e →
    isMatrix e = false → ordinal X (w0 + l) k = N → RowRead (xs (N / 182)) w l d e →
    PtOk (xs (N / 182)) w l q d →
    ∃ d', Thread.next L (w0 + l) d e = some (some d') ∧
      ∃ q' ∈ pointsAt n, PtOk (xs (N / 182)) w l q' d'

/-- The points at which a lane makes its matrix event. -/
def Pt.isMatrix : Pt → Bool
  | .mx _ | .mma _ | .mov _ | .st _ => true
  | _ => false

/-- **At a matrix point only a matrix event occurs**, and it is a multiply-accumulate only at
the point of an `mma.sync`. -/
def PtMatrix (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 l k N : ℕ) (q : Pt × Table) : Prop :=
  ∀ d e, stateAt (code L) X (w0 + l) k = some (some d) → X.get (w0 + l, k) = some e →
    PtOk (xs (N / 182)) w l q d →
    isMatrix e = true ∧
      ((∃ pc s own recv, e = ⟨pc, .matrix (.mma s) own recv⟩) → ∃ j, q.1 = .mma j)

/-- **What is proved at each point of a count**: the local step, and for a matrix point that
only its matrix event occurs there. -/
def PtLocal (xs : ℕ → Inputs) (w : ℕ) (X : Execution) (w0 l k N n : ℕ) (q : Pt × Table) : Prop :=
  PtStep (L := L) xs w X w0 l k N n q ∧
    (q.1.isMatrix = true → PtMatrix (L := L) xs w X w0 l k N q)

theorem PtLocal.of_step {xs : ℕ → Inputs} {w w0 l k N n : ℕ} {q : Pt × Table}
    (hq : q.1.isMatrix = false) (h : PtStep (L := L) xs w X w0 l k N n q) :
    PtLocal (L := L) xs w X w0 l k N n q :=
  ⟨h, fun hm => by rw [hq] at hm; cases hm⟩

theorem PtLocal.of_matrix {xs : ℕ → Inputs} {w w0 l k N n : ℕ} {q : Pt × Table}
    (h : PtMatrix (L := L) xs w X w0 l k N q) : PtLocal (L := L) xs w X w0 l k N n q :=
  ⟨fun d e hσ he hnm _ _ hok => absurd hnm (by rw [(h d e hσ he hok).1]; simp), fun _ => h⟩

/-- A point of an `mma.sync`, from "only a matrix event occurs there". -/
theorem PtLocal.of_mma {xs : ℕ → Inputs} {w w0 l k N n : ℕ} {j : Fin 104} {T : Table}
    (h : ∀ d e, stateAt (code L) X (w0 + l) k = some (some d) → X.get (w0 + l, k) = some e →
      PtOk (xs (N / 182)) w l (.mma j, T) d → isMatrix e = true) :
    PtLocal (L := L) xs w X w0 l k N n (.mma j, T) :=
  .of_matrix fun d e hσ he hok => ⟨h d e hσ he hok, fun _ => ⟨j, rfl⟩⟩

/-- A matrix point of a load, a `movmatrix` or a store, from the shape of its event. -/
theorem PtLocal.of_move {xs : ℕ → Inputs} {w w0 l k N n : ℕ} {q : Pt × Table}
    (h : ∀ d e, stateAt (code L) X (w0 + l) k = some (some d) → X.get (w0 + l, k) = some e →
      PtOk (xs (N / 182)) w l q d → MoveEv e) :
    PtLocal (L := L) xs w X w0 l k N n q :=
  .of_matrix fun d e hσ he hok => by
    obtain ⟨pc, op, own, recv, rfl, hop⟩ := h d e hσ he hok
    refine ⟨rfl, ?_⟩
    rintro ⟨pc', s, own', recv', h'⟩
    cases h'
    exact absurd rfl (hop s)

/-- **The local step of a count** (`n ≠ 0`), from what is proved at its points: across an
event that is no matrix event (a read of a row of the tile if it is a row read, `hrd`) the lane
is alive and the invariant is kept. -/
theorem local_step {xs : ℕ → Inputs} {w w0 N n l k : ℕ} (hN : N % 182 = n) (hn0 : n ≠ 0)
    {e : Event} (he : X.get (w0 + l, k) = some e) (hnm : isMatrix e = false)
    (hk : ordinal X (w0 + l) k = N)
    (hrd : ∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
      RowRead (xs (N / 182)) w l d e)
    (hpts : AllOf (PtLocal (L := L) xs w X w0 l k N n) (pointsAt n))
    (IH : ValAt (L := L) xs w X w0 l k) :
    (∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
        ∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  subst hN
  have hord' := ordinal_succ_of_not_matrix he hnm
  have key : ∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
      ∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d') ∧
        Inv (L := L) xs w l X (w0 + l) (k + 1) N d' := by
    intro d hσ
    have hinv := IH d hσ
    rw [hk] at hinv
    rcases hinv with ⟨q, hq, hok⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨d'', hnx, q', hq', hok'⟩ :=
        (hpts.mem q hq).1 d e hσ he hnm hk (hrd d hσ) hok
      exact ⟨d'', by rw [stateAt_next he hσ, hnx], .inl ⟨q', hq', hok'⟩⟩
    · exact absurd h0 hn0
    · exact absurd h0 hn0
    · exact absurd (by omega) hn0
  refine ⟨fun d hσ => (key d hσ).imp fun _ h => h.1, ?_⟩
  intro d' hd'
  cases hσ : stateAt (code L) X (w0 + l) k with
  | none => rw [stateAt_succ (C := code L) he, hσ] at hd'; cases hd'
  | some σ =>
    cases σ with
    | none => rw [stateAt_succ (C := code L) he, hσ] at hd'; cases hd'
    | some d =>
      obtain ⟨d'', hσ'', hinv⟩ := key d hσ
      have hdd : d' = d'' := Option.some.inj (Option.some.inj (hd'.symm.trans hσ''))
      rw [hord', hk, hdd]
      exact hinv

/-- **The row read of an `ldmatrix`**: the lane reads a row of the source (`RowRead`) and moves
to the second event with that row. `hnext` is the machine's transition. -/
theorem rd_local {w0 w n : ℕ} {j : Fin 44} {T : Table}
    (hnext : ∀ (g : ℕ) (d : D) (pc : ℕ) (a : Acc) (bs : List (Option Byte)),
      d.site = .matrixLoad j →
      Thread.next L g d ⟨pc, .rd a bs⟩ = ldRow d bs (.matrixLoadMx j))
    (hq' : (Pt.mx j, T) ∈ pointsAt n) {xs : ℕ → Inputs} {l k N : ℕ} :
    PtStep (L := L) xs w X w0 l k N n (.rd j, T) := by
  intro d e hσ he _ hk hrd ⟨hs, hT⟩
  have hs : d.site = .matrixLoad j := hs
  obtain ⟨pc, a, row, rfl, hr⟩ := hrd j hs
  refine ⟨⟨.matrixLoadMx j row, d.w, d.p, d.x⟩, ?_, _, hq', ⟨row, rfl, hr⟩, hT⟩
  rw [hnext _ d pc a row hs, ldRow, ite_eq_left hr.all]

/-- At the second event of an `ldmatrix` only its matrix event occurs. -/
theorem mx_event (F : Followed L mem0 X) {w0 w : ℕ} {j : Fin 44} {T : Table} {ins : Instr}
    {i : MatrixInstr} {m : MatrixMove}
    (hcode : kernel.code[(Site.matrixLoad j).pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move m) (hrule : i.rule = some .threadMatrix) (hst : m.store = false)
    (hmr : m.num * m.rows = 32) {x : Inputs} {l k : ℕ} {d : D} {e : Event}
    (hσ : stateAt (code L) X (w0 + l) k = some (some d)) (he : X.get (w0 + l, k) = some e)
    (hok : PtOk x w l (.mx j, T) d) : MoveEv e := by
  obtain ⟨⟨row, hs, hr⟩, -⟩ := hok
  obtain ⟨recv, hrecv⟩ := loadMx_shape (bs := row) F he hσ
    (by rw [hs]; exact hcode) hins hop hrule hst hmr (by rw [hs]; rfl) (by rw [hs]; rfl) hr.all
  exact ⟨_, _, _, _, hrecv, fun s h => by cases h⟩

/-- **A scalar load of the tile loop**: the lane reads the bytes of the load's source
(`ScalarsRead`; `s` is the source), which rebuild into a value `v` with the form `f` (`hval`);
the machine writes it to register `r` and evaluates the run that follows under the condition
`Cd`. `M` is the table after the load, `hpost` as in `mma_step`. -/
theorem ld_local {w0 w n : ℕ} {i : Fin 178} (hi : 159 ≤ i.val) (hi' : i.val < 177) {T : Table}
    {r : ℕ} {f : Form} {ldf : List (Option Byte) → Exec Value} {s : ScalarSrc}
    (hsrc : scalarSrc i = s)
    (hval : ∀ x l bs, s.Bytes x l bs → ∃ v, ldf bs = .ok v ∧ f.Holds x w l v)
    {Cd : D → Value → Prop} {after : Launch → ℕ → D → Value → D}
    (hnext : ∀ (g : ℕ) (d : D) (pc : ℕ) (a : Acc) (bs : List (Option Byte)) (v : Value),
      d.site = .load i → ldf bs = .ok v →
      Thread.next L g d ⟨pc, .rd a bs⟩ = across (Cd d v) (after L g d v))
    {M : Table} (hsub : Table.sub M T [(r, f)] = true) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt n)
    (hpost : ∀ x l g d v, l < 32 → M.Holds x w l (valueEx d.x [(r, v)]) →
      Cd d v ∧ PtOk x w l q' (after L g d v))
    {xs : ℕ → Inputs} (hsc : ScalarsRead (L := L) xs X w0) {l k N : ℕ} (hl : l < 32) :
    PtStep (L := L) xs w X w0 l k N n (.ld i, T) := by
  intro d e hσ he _ hk _ ⟨hs, hT⟩
  have hs : d.site = .load i := hs
  -- rewrite the source before naming the bytes: a hypothesis about `scalarSrc ↑i` with a
  -- variable `i` sends later weak-head normalisations into the table lookup
  have hread := hsc l hl k d e i hi hi' hσ hs he
  rw [hk, hsrc] at hread
  obtain ⟨pc, a, bs, rfl, hb⟩ := hread
  obtain ⟨v, hv, hf⟩ := hval (xs (N / 182)) l bs hb
  have hM : M.Holds (xs (N / 182)) w l (valueEx d.x [(r, v)]) :=
    Table.step (ds := [r]) (fs := [f]) (vs := [v]) (List.nodup_singleton r) rfl rfl hT hsub
      fun j hj => by
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        exact hf
  obtain ⟨hc, hok⟩ := hpost _ l (w0 + l) d v hl hM
  exact ⟨_, (hnext _ d pc a bs v hs hv).trans (across_pos hc), q', hq', hok⟩

/-- **The row write of an `stmatrix`**: the lane writes its row (`ComputeRef.storeRow`) and the
machine evaluates the run that follows under the condition `Cd`; `hpost` as in `mma_step`, on
the table of the point (the write changes no register). -/
theorem wr_local (R : ComputeRef P L X) {w0 w n : ℕ} (W : Warp L w0) {j : Fin 18} {T : Table}
    {Cd : D → Prop} {after : Launch → ℕ → D → D}
    (hnext : ∀ (g : ℕ) (d : D) (row : List (Option Byte)) (pc : ℕ) (a : Acc) (bs : List Byte),
      d.site = .matrixStoreWr j row →
      Thread.next L g d ⟨pc, .wr a bs⟩ = across (Cd d) (after L g d))
    {q' : Pt × Table} (hq' : q' ∈ pointsAt n)
    (hpost : ∀ x l g d, l < 32 → T.Holds x w l d.x → Cd d ∧ PtOk x w l q' (after L g d))
    {xs : ℕ → Inputs} {l k N : ℕ} (hl : l < 32) :
    PtStep (L := L) xs w X w0 l k N n (.wr j, T) := by
  intro d e hσ he _ _ _ ⟨⟨row, hs, _⟩, hT⟩
  obtain ⟨a, rfl, -, -⟩ := R.storeRow (w0 + l) k d e j row (W.compute l hl) hσ hs he
  obtain ⟨hc, hok⟩ := hpost _ l (w0 + l) d hl hT
  exact ⟨_, (hnext _ d row _ a _ hs).trans (across_pos hc), q', hq', hok⟩

/-! ## `movmatrix` -/

/-- The source register of a `movmatrix`, read off the table. -/
theorem mov_source {T : Table} {x : Inputs} {w l : ℕ} {d : D} {src : ℕ} {M : Mat} {p : ℕ}
    (hsrc : (T.has src (.rowPair M p) && isOpaque src) = true) (hT : T.Holds x w l d.x) :
    (Form.rowPair M p).Holds x w l (valueOf d src) := by
  simp only [Bool.and_eq_true] at hsrc
  rw [valueOf_opaque hsrc.2]
  exact hT.get hsrc.1

/-- **The step across a `movmatrix`**: the source register holds a packed pair of rows of the
matrix `M` (form `rowPair M p`), the destination receives B register `p` of `M`. -/
theorem move_step (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) (hn : n + 1 < 182) {j : Fin 16}
    (hord : ordSite n = .move j) {pc : ℕ} (hpc : (Site.matrixMove j).pc = pc) {ins : Instr}
    {i : MatrixInstr} {dst src : ℕ} (hcode : kernel.code[pc]? = some ins)
    (hins : ins.op = .matrix i) (hop : i.op = .transpose) (hd : i.dsts = [dst])
    (hs : i.srcs = [.reg src]) (hlive : (Flow.live pc).contains src = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.mov j, T)) {M : Mat} {p : ℕ}
    (hsrc : (T.has src (.rowPair M p) && isOpaque src) = true)
    {after : Launch → ℕ → D → List Value → D}
    (hnext : ∀ (g : ℕ) (d : D) (own recv : List (Option Byte)) (vs : List Value),
      d.site = .matrixMove j → matrixVals 32 1 recv = .ok vs →
      Thread.next L g d ⟨pc, .matrix .transpose own recv⟩ = some (some (after L g d vs)))
    (hx : ∀ g d vs, (after L g d vs).x = valueEx d.x ([dst].zip vs)) {q' : Pt × Table}
    (hq' : q' ∈ pointsAt (n + 1)) (hat : ∀ x l g d vs, q'.1.At x w l (after L g d vs))
    (hsub : Table.sub q'.2 T [(dst, .regB M p)] = true)
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  have hordN : ordSite (N % 182) = .move j := by rw [hN]; exact hord
  have hgood : ∀ l' < 32, ∀ k' d', X.MatrixK (w0 + l', k') N →
      stateAt (code L) X (w0 + l') k' = some (some d') →
      d'.site = .matrixMove j ∧ T.Holds (xs (N / 182)) w l' d'.x := fun l' hl' k' d' hk' hσ' =>
    ptOk_at_event R E W hN IH (by rw [hord]; rfl) hnd hT hl' hk' hσ'
  obtain ⟨own, he⟩ := move_event F R W hordN hpc hcode hins hop hd hs hlive
    (S := rowTile (M.eval (xs (N / 182)) w) p)
    (fun l' hl' k' d' hk' hσ' _ =>
      ⟨rowPair_own (mov_source hsrc (hgood l' hl' k' d' hk' hσ').2),
        Form.bytes (mov_source hsrc (hgood l' hl' k' d' hk' hσ').2) rfl⟩) hl hk
  obtain ⟨e, d, he', -, hσ⟩ := state_of_matrixK F hk
  obtain ⟨hsd, hTd⟩ := hgood l hl k d hk hσ
  have hmv := mov_vals (xs (N / 182)) w M p hl
  have hM : q'.2.Holds (xs (N / 182)) w l
      (valueEx d.x ([dst].zip [regB (M.eval (xs (N / 182)) w) l p])) :=
    Table.step (ds := [dst]) (fs := [.regB M p]) (List.nodup_singleton dst) rfl rfl hTd hsub
      fun r hr => by
        have hr0 : r = 0 := by simpa using hr
        subst hr0
        exact rfl
  exact step_done hN hn hk he hσ (hnext _ d _ _ _ hsd hmv) hq'
    ⟨hat _ _ _ _ _, by rw [hx]; exact hM⟩

/-- At a `movmatrix` only its matrix event occurs. -/
theorem mov_event (F : Followed L mem0 X) {w0 w : ℕ} {j : Fin 16} {pc : ℕ}
    (hpc : (Site.matrixMove j).pc = pc) {ins : Instr} {i : MatrixInstr} {dst src : ℕ}
    (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i) (hop : i.op = .transpose)
    (hd : i.dsts = [dst]) (hs : i.srcs = [.reg src])
    (hlive : (Flow.live pc).contains src = true) {T : Table} {M : Mat} {p : ℕ}
    (hsrc : (T.has src (.rowPair M p) && isOpaque src) = true) {x : Inputs} {l k : ℕ} {d : D}
    {e : Event} (hσ : stateAt (code L) X (w0 + l) k = some (some d))
    (he : X.get (w0 + l, k) = some e) (hok : PtOk x w l (.mov j, T) d) : MoveEv e := by
  obtain ⟨hsd, hT⟩ := hok
  have hsd : d.site = .matrixMove j := hsd
  have hpc' : d.site.pc = pc := by rw [hsd]; exact hpc
  obtain ⟨recv, hrecv⟩ := move_shape F he hσ (by rw [hpc']; exact hcode) hins hop hd hs
    (by rw [hpc']; simpa using hlive) (Form.bytes (mov_source hsrc hT) rfl)
  exact ⟨_, _, _, _, hrecv, fun s h => by cases h⟩

/-! ## `stmatrix` -/

/-- The Boolean check that the four source registers of a store have the forms of its source
in the table and are opaque. -/
def stCheck (T : Table) (rs : List ℕ) (s : StoreSrc) : Bool :=
  (List.range 4).all fun r =>
    T.has (rs.getD r 0) (s.forms.getD r (.logitZ 0)) && isOpaque (rs.getD r 0)

/-- **The source values of a store from the table**: the lane contributes the register bytes
of the store's fragments, four bytes per register. -/
theorem st_values {T : Table} {x : Inputs} {w l : ℕ} {d : D} {r0 r1 r2 r3 : ℕ} {s : StoreSrc}
    (hchk : stCheck T [r0, r1, r2, r3] s = true) (hT : T.Holds x w l d.x) :
    ownBytes ([r0, r1, r2, r3].map (valueOf d)) = regPart (fragRegs bf16Enc (s.frag x w)) l ∧
      ∀ r ∈ [r0, r1, r2, r3], (valueOf d r).bytes = 4 := by
  have get : ∀ r < 4, (s.forms.getD r (.logitZ 0)).Holds x w l
      (valueOf d ([r0, r1, r2, r3].getD r 0)) := by
    intro r hr
    have h := List.all_eq_true.mp hchk r (List.mem_range.mpr hr)
    simp only [Bool.and_eq_true] at h
    rw [valueOf_opaque h.2]
    exact hT.get h.1
  have h0 : (Form.rowPair (s.mat 0) 0).Holds x w l (valueOf d r0) := get 0 (by omega)
  have h1 : (Form.rowPair (s.mat 0) 1).Holds x w l (valueOf d r1) := get 1 (by omega)
  have h2 : (Form.rowPair (s.mat 1) 0).Holds x w l (valueOf d r2) := get 2 (by omega)
  have h3 : (Form.rowPair (s.mat 1) 1).Holds x w l (valueOf d r3) := get 3 (by omega)
  refine ⟨s.own h0 h1 h2 h3, ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Form.bytes h0 rfl
  · exact Form.bytes h1 rfl
  · exact Form.bytes h2 rfl
  · exact Form.bytes h3 rfl

/-- **The matrix event of an `stmatrix`**: from `Val` at `N` (every lane at the event holds the
four packed registers of the store's source), a lane that makes the event receives its row of
the arrays and moves to the row write with it; its data slots are unchanged. -/
theorem store_core (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) {j : Fin 18}
    (hord : ordSite n = .store j) {pc : ℕ} (hpc : (Site.matrixStore j).pc = pc) {ins : Instr}
    {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (st4 (storeSrc j).trans)) (hrule : i.rule = some .threadMatrix)
    {r0 r1 r2 r3 : ℕ} (hsrcs : i.srcs = [r0, r1, r2, r3].map .reg)
    (hlive : ([r0, r1, r2, r3].all fun r => (Flow.live pc).contains r) = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.st j, T))
    (hchk : stCheck T [r0, r1, r2, r3] (storeSrc j) = true)
    (hnext : ∀ (g : ℕ) (d : D) (own recv : List (Option Byte)), d.site = .matrixStore j →
      Thread.next L g d ⟨pc, .matrix (.move (st4 (storeSrc j).trans)) own recv⟩ =
        stRecv d recv (.matrixStoreWr j))
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    ∃ d e, X.get (w0 + l, k) = some e ∧ stateAt (code L) X (w0 + l) k = some (some d) ∧
      T.Holds (xs (N / 182)) w l d.x ∧
      Thread.next L (w0 + l) d e = some (some
        ⟨.matrixStoreWr j ((storeSrc j).row (xs (N / 182)) w l), d.w, d.p, d.x⟩) := by
  have hordN : ordSite (N % 182) = .store j := by rw [hN]; exact hord
  have hgood : ∀ l' < 32, ∀ k' d', X.MatrixK (w0 + l', k') N →
      stateAt (code L) X (w0 + l') k' = some (some d') →
      d'.site = .matrixStore j ∧ T.Holds (xs (N / 182)) w l' d'.x := fun l' hl' k' d' hk' hσ' =>
    ptOk_at_event R E W hN IH (by rw [hord]; rfl) hnd hT hl' hk' hσ'
  obtain ⟨own, he⟩ := store_event F R W hordN hpc hcode hins hop hrule hsrcs hlive
    (regs := fragRegs bf16Enc ((storeSrc j).frag (xs (N / 182)) w))
    (fun l' hl' k' d' hk' hσ' _ => st_values hchk (hgood l' hl' k' d' hk' hσ').2) hl hk
  obtain ⟨e, d, he', -, hσ⟩ := state_of_matrixK F hk
  obtain ⟨hsd, hTd⟩ := hgood l hl k d hk hσ
  refine ⟨d, _, he, hσ, hTd, ?_⟩
  rw [hnext _ d _ _ hsd, StoreSrc.recv, stRecv,
    ite_eq_left ⟨StoreSrc.row_length .., StoreSrc.row_all ..⟩]

/-- **The step across the matrix event of an `stmatrix`** (not the last of the tile): the lane
is alive after it, at the row write of the store. -/
theorem store_step (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) (hn : n + 1 < 182) {j : Fin 18}
    (hord : ordSite n = .store j) {pc : ℕ} (hpc : (Site.matrixStore j).pc = pc) {ins : Instr}
    {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (st4 (storeSrc j).trans)) (hrule : i.rule = some .threadMatrix)
    {r0 r1 r2 r3 : ℕ} (hsrcs : i.srcs = [r0, r1, r2, r3].map .reg)
    (hlive : ([r0, r1, r2, r3].all fun r => (Flow.live pc).contains r) = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (.st j, T))
    (hchk : stCheck T [r0, r1, r2, r3] (storeSrc j) = true)
    (hnext : ∀ (g : ℕ) (d : D) (own recv : List (Option Byte)), d.site = .matrixStore j →
      Thread.next L g d ⟨pc, .matrix (.move (st4 (storeSrc j).trans)) own recv⟩ =
        stRecv d recv (.matrixStoreWr j))
    (hq' : (Pt.wr j, T) ∈ pointsAt (n + 1))
    {xs : ℕ → Inputs} (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  obtain ⟨d, e, he, hσ, hTd, hnx⟩ := store_core F R E W hN hord hpc hcode hins hop hrule hsrcs
    hlive hnd hT hchk hnext IH hl hk
  exact step_done hN hn hk he hσ hnx hq' ⟨⟨_, rfl, rfl⟩, hTd⟩

/-- **The step across the matrix event of the last `stmatrix` of a tile.** The lane is alive
after it, at the row write of the store; all its carries are updated, so with the chain of
tiles (`Chain`) its data slots satisfy the table of ordinal 0 on the arrays of the next tile:
the invariant between two tiles (`TailOk`). -/
theorem store_last (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N : ℕ} (W : Warp L w0) (hN : N % 182 = 181) {pc : ℕ}
    (hord : ordSite 181 = .store 17) (hpc : (Site.matrixStore 17).pc = pc) {ins : Instr}
    {i : MatrixInstr} (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (st4 (storeSrc 17).trans)) (hrule : i.rule = some .threadMatrix)
    {r0 r1 r2 r3 : ℕ} (hsrcs : i.srcs = [r0, r1, r2, r3].map .reg)
    (hlive : ([r0, r1, r2, r3].all fun r => (Flow.live pc).contains r) = true)
    {T : Table} {ip : ℕ} (hnd : ((pointsAt 181).map Prod.fst).Nodup)
    (hT : (pointsAt 181)[ip]? = some (.st 17, T))
    (hchk : stCheck T [r0, r1, r2, r3] (storeSrc 17) = true)
    (hnext : ∀ (g : ℕ) (d : D) (own recv : List (Option Byte)), d.site = .matrixStore 17 →
      Thread.next L g d ⟨pc, .matrix (.move (st4 (storeSrc 17).trans)) own recv⟩ =
        stRecv d recv (.matrixStoreWr 17))
    (hnx0 : T.nextOf (tableAt 0) = true) (hw : w < 4)
    {xs : ℕ → Inputs} (hch : ∀ l < 32, Chain xs (tileCount P L (w0 + l)))
    (IH : Val (L := L) xs w X w0 N) {l k : ℕ} (hl : l < 32)
    (hk : X.MatrixK (w0 + l, k) N) :
    (∃ d', stateAt (code L) X (w0 + l) (k + 1) = some (some d')) ∧
      ValAt (L := L) xs w X w0 l (k + 1) := by
  obtain ⟨d, e, he, hσ, hTd, hnx⟩ := store_core F R E W hN hord hpc hcode hins hop hrule hsrcs
    hlive hnd hT hchk hnext IH hl hk
  have hσ' : stateAt (code L) X (w0 + l) (k + 1) = some (some
      ⟨.matrixStoreWr 17 ((storeSrc 17).row (xs (N / 182)) w l), d.w, d.p, d.x⟩) := by
    rw [stateAt_next he hσ]
    exact hnx
  refine ⟨⟨_, hσ'⟩, ?_⟩
  intro d' hd'
  have ho := ordinal_succ_of_matrixK hk
  have hdd : d' = _ := Option.some.inj (Option.some.inj (hd'.symm.trans hσ'))
  have hb : N / 182 < tileCount P L (w0 + l) := by
    have h2 := matrixK_lt_countP hk
    have h3 := (R.count (w0 + l) (W.compute l hl)).1
    omega
  have e1 : (N + 1) / 182 - 1 = N / 182 := by omega
  have e2 : (N + 1) / 182 = N / 182 + 1 := by omega
  rw [ho, hdd]
  refine .inr (.inl ⟨by omega, by omega, ?_⟩)
  rw [e1, e2]
  exact ⟨.inl ⟨_, rfl, rfl⟩, Table.next_holds (hch l hl (N / 182) hb) hw hl hTd hnx0⟩

/-- At the matrix event of an `stmatrix` only its matrix event occurs. -/
theorem st_event (F : Followed L mem0 X) {w0 w : ℕ} {j : Fin 18} {pc : ℕ}
    (hpc : (Site.matrixStore j).pc = pc) {ins : Instr} {i : MatrixInstr} {tr : Bool}
    (hcode : kernel.code[pc]? = some ins) (hins : ins.op = .matrix i)
    (hop : i.op = .move (st4 tr)) (hrule : i.rule = some .threadMatrix) {r0 r1 r2 r3 : ℕ}
    (hsrcs : i.srcs = [r0, r1, r2, r3].map .reg)
    (hlive : ([r0, r1, r2, r3].all fun r => (Flow.live pc).contains r) = true) {T : Table}
    {s : StoreSrc} (hchk : stCheck T [r0, r1, r2, r3] s = true) {x : Inputs} {l k : ℕ} {d : D}
    {e : Event} (hσ : stateAt (code L) X (w0 + l) k = some (some d))
    (he : X.get (w0 + l, k) = some e) (hok : PtOk x w l (.st j, T) d) : MoveEv e := by
  obtain ⟨hsd, hT⟩ := hok
  have hsd : d.site = .matrixStore j := hsd
  have hpc' : d.site.pc = pc := by rw [hsd]; exact hpc
  obtain ⟨recv, hrecv⟩ := store_shape F he hσ (by rw [hpc']; exact hcode) hins hop hrule rfl
    hsrcs (by rw [hsd]; rfl)
    (fun r hr => by rw [hpc']; simpa using List.all_eq_true.mp hlive r hr)
    (st_values hchk hT).2
  exact ⟨_, _, _, _, hrecv, fun s h => by cases h⟩

/-! ## No multiply-accumulate at the other matrix instructions -/

/-- `MmaClaim` at an ordinal of a load, a `movmatrix` or a store: no lane makes an `mma` event
there (`hev`: the event of a lane at the point of the ordinal), so there is no instance. -/
theorem move_claim (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w N n : ℕ} (W : Warp L w0) (hN : N % 182 = n) {pt : Pt} {T : Table} {ip : ℕ}
    (hpt : Pt.ofMSite (ordSite n) = pt) (hnd : ((pointsAt n).map Prod.fst).Nodup)
    (hT : (pointsAt n)[ip]? = some (pt, T)) {xs : ℕ → Inputs}
    (hev : ∀ (k : ℕ) (d : D) (e : Event), stateAt (code L) X (w0 + 0) k = some (some d) →
      X.get (w0 + 0, k) = some e → PtOk (xs (N / 182)) w 0 (pt, T) d → MoveEv e)
    (IH : Val (L := L) xs w X w0 N) : MmaClaim X w0 N := by
  intro pc s parts hI
  exfalso
  obtain ⟨j, recv, he, hk⟩ := hI 0 (by omega)
  obtain ⟨e, d, -, -, hσ⟩ := state_of_matrixK F hk
  have hok := ptOk_at_event R E W hN IH hpt hnd hT (by omega : 0 < 32) hk hσ
  obtain ⟨pc', op, own, recv', h, hop⟩ := hev j d _ hσ he hok
  injection h with h1 h2
  injection h2 with h3
  exact hop s h3.symm

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
