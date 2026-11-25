-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Values.Gen.Steps
public import Kernels.FlashKdaFwd.Proof.Values.TileClaim
public import Kernels.FlashKdaFwd.Proof.Values.StageReads
public import Kernels.FlashKdaFwd.Proof.Values.TileAlgebra
public import Kernels.FlashKdaFwd.Proof.Values.AccRows

@[expose] public section

/-!
# The induction over the tiles

`Gen/Steps.lean` has the steps inside a tile. This file adds the passage from one tile to the
next and assembles the induction.

* `tail_next`: a transition of the machine out of a control site of the tail of a tile
  (`TailSite`, but the site after the exit branch) stays in the tail or reaches the first
  `ldmatrix`, and changes no data slot but the one of the remote-address register of the
  `mapa` (slot 3434, which no table lists).
* `local_zero`: the local step for a lane whose number of matrix events is a multiple of 182.
  At the two points of the first load it is the generated step. In the tail it follows the
  machine: the row write of the last store, the control sites, and the arrival at the first
  load with the carries of the next tile (`TailOk`); at the site after the exit branch the
  lane leaves the loop (`Left`). Before the loop (no matrix event yet, `¬ Entered`) a lane
  that arrives at the first load satisfies its table by the base case (`Base`), and it cannot
  arrive at the second event of that load directly (`FirstLoad`).
* `val_hist`, `val_all`: `Val` for every number of matrix events, from the generated matrix
  steps (`Gen.mstep`), the generated local steps (`Gen.lpts` with `local_step`) and
  `local_zero`. The induction gives each local step the invariant at all earlier positions of
  the lane, which the read-back of the rows of `state_acc` needs.
* `tile_induction`: the statement `TileInduction` of `TileClaim.lean`. The chain of tiles is
  `tileInputs_chain`, the reads of the input stage are `rows_read_stage` and `scalars_read`,
  the reads of `state_acc` are `acc_rows` (from the invariant at the lane's earlier positions);
  the fields `matrix`, `alive` and `mma` of the claim are read off the generated lemmas.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Values
open PTX PTX.Flow PTX.Frame PTX.WarpMatrix
open PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Math.Fragments
open PTX.Kernels.FlashKdaFwd.Recurrence (tiles)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ## The tail of a tile -/

/-- **A transition out of a control site of the tail** keeps the lane in the tail or brings it
to the first `ldmatrix`, with the same data slots or with slot 3434 rewritten. -/
theorem tail_next {g : ℕ} {d d' : D} {e : Event} (h : Thread.next L g d e = some (some d'))
    (hs : TailSite d.site) (h7 : d.site ≠ .bar 7) :
    (TailSite d'.site ∨ d'.site = .matrixLoad 0) ∧
      (d'.x = d.x ∨ ∃ v, d'.x = valueEx d.x [(3434, v)]) := by
  obtain ⟨s, dw, dp, dx⟩ := d
  have hs' : s = .bar 6 ∨ s = .fenceProxy 2 ∨ s = .mbarArrive 4 ∨ s = .mbarArrive 5 ∨
      s = .mbarWait 7 ∨ s = .mbarWait 8 ∨ s = .bar 7 ∨ s = .trap 7 ∨ s = .trap 8 ∨ s = .trap 9 ∨
      s = .trap 10 ∨ s = .trap 11 := hs
  rcases hs' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [next_bar_6] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    exact ⟨.inl (by simp [TailSite, after_bar_6]), .inl rfl⟩
  · rw [next_fenceProxy_2] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    simp only [after_fenceProxy_2]
    split_ifs <;> simp [TailSite]
  · rw [next_mbarArrive_4] at h
    simp only [after_mbarArrive_4] at h
    split_ifs at h
    · simp only [tail_2927, mapaThen] at h
      split at h
      · obtain rfl := Option.some.inj (Option.some.inj h)
        exact ⟨.inl (by simp [TailSite]), .inr ⟨_, rfl⟩⟩
      · cases h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      exact ⟨.inl (by simp [TailSite]), .inl rfl⟩
  · rw [next_mbarArrive_5] at h
    obtain rfl := Option.some.inj (Option.some.inj h)
    simp only [after_mbarArrive_5]
    split_ifs <;> simp [TailSite]
  · rw [next_mbarWait_7] at h
    split at h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      simp only [after_mbarWait_7]
      split_ifs <;> simp [TailSite]
    · cases h
  · rw [next_mbarWait_8] at h
    split at h
    · obtain rfl := Option.some.inj (Option.some.inj h)
      simp only [after_mbarWait_8]
      split_ifs <;> simp [TailSite]
    · cases h
  · exact absurd rfl h7
  · rw [next_trap_7] at h; cases h
  · rw [next_trap_8] at h; cases h
  · rw [next_trap_9] at h; cases h
  · rw [next_trap_10] at h; cases h
  · rw [next_trap_11] at h; cases h

/-- A thread's first site is not the first `ldmatrix` of the tile loop. -/
theorem init_not_load (L : Launch) (g : ℕ) :
    ¬ ((code L g).init.site = .matrixLoad 0 ∨
      ∃ row, (code L g).init.site = .matrixLoadMx 0 row) := by
  simp only [init, entry]
  split_ifs <;> simp

/-- **The local step when the number of matrix events is a multiple of 182.** -/
theorem local_zero (R : ComputeRef P L X) {w0 w N : ℕ} (W : Warp L w0) (hN : N % 182 = 0)
    {xs : ℕ → Inputs} (hbase : Base (L := L) xs w X w0) (hfirst : FirstLoad (L := L) X w0)
    {l k : ℕ} (hl : l < 32) {e : Event} (he : X.get (w0 + l, k) = some e)
    (hnm : isMatrix e = false) (hk : ordinal X (w0 + l) k = N)
    (hrd : ∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
      RowRead (xs (N / 182)) w l d e)
    (hpts : AllOf (PtLocal (L := L) xs w X w0 l k N 0) (pointsAt 0))
    (IH : ValAt (L := L) xs w X w0 l k) : ValAt (L := L) xs w X w0 l (k + 1) := by
  intro d' hd'
  have hord' := ordinal_succ_of_not_matrix he hnm
  cases hσ : stateAt (code L) X (w0 + l) k with
  | none => rw [stateAt_succ (C := code L) he, hσ] at hd'; cases hd'
  | some σ =>
    cases σ with
    | none => rw [stateAt_succ (C := code L) he, hσ] at hd'; cases hd'
    | some d =>
      have hnx : Thread.next L (w0 + l) d e = some (some d') := by
        rw [← stateAt_next he hσ]
        exact hd'
      have hinv := IH d hσ
      rw [hord', hk]
      rw [hk] at hinv
      rcases hinv with ⟨q, hq, hok⟩ | ⟨h0, h1, hs, hT⟩ | ⟨h0, h1, k', hk', ho, hleft⟩ | ⟨h0, hne⟩
      · rw [hN] at hq
        obtain ⟨d'', hnx', q', hq', hok'⟩ :=
          (hpts.mem q hq).1 d e hσ he hnm hk (hrd d hσ) hok
        have hdd : d'' = d' := Option.some.inj (Option.some.inj (hnx'.symm.trans hnx))
        rw [← hdd]
        exact .inl ⟨q', by rw [hN]; exact hq', hok'⟩
      · rcases hs with ⟨row, hs, -⟩ | hs
        · obtain ⟨a, rfl, -, -⟩ := R.storeRow (w0 + l) k d _ 17 row (W.compute l hl) hσ hs he
          obtain ⟨s, dw, dp, dx⟩ := d
          cases hs
          rw [next_matrixStoreWr_17] at hnx
          obtain rfl := Option.some.inj (Option.some.inj hnx)
          exact .inr (.inl ⟨h0, h1, .inr (by simp [TailSite, after_matrixStoreWr_17]), hT⟩)
        · by_cases h7 : d.site = .bar 7
          · exact .inr (.inr (.inl ⟨h0, h1, k, Nat.lt_succ_self k, by rw [hord'], d, hσ, h7⟩))
          · obtain ⟨hs', hx'⟩ := tail_next hnx hs h7
            have hT' : (tableAt 0).Holds (xs (N / 182)) w l d'.x := by
              rcases hx' with hx' | ⟨v, hx'⟩
              · rw [hx']
                exact hT
              · rw [hx']
                exact Table.frame hT (ks := [3434]) rfl (by kernel_rfl)
            rcases hs' with hs' | hs'
            · exact .inr (.inl ⟨h0, h1, .inr hs', hT'⟩)
            · exact .inl ⟨(.rd 0, tableAt 0), by rw [hN]; exact pts_mem (ip := 0) rfl, hs', hT'⟩
      · exact .inr (.inr (.inl ⟨h0, h1, k', by omega, by rw [hord']; exact ho, hleft⟩))
      · by_cases hent : Entered (L := L) X (w0 + l) (k + 1)
        · obtain ⟨k', hk', d0, hσ0, hs0⟩ := hent
          have hk1 : k' = k + 1 := by
            by_contra hcon
            exact hne ⟨k', by omega, d0, hσ0, hs0⟩
          subst hk1
          have hdd : d0 = d' := Option.some.inj (Option.some.inj (hσ0.symm.trans hd'))
          subst hdd
          rcases hs0 with hs0 | ⟨row, hs0⟩
          · have hT := hbase l hl (k + 1) d0 (by rw [hord', hk, h0]) hd' hs0
            subst h0
            exact .inl ⟨(.rd 0, tableAt 0), pts_mem (ip := 0) rfl, hs0, hT⟩
          · obtain ⟨dp', hσp, hsp⟩ := hfirst l hl k e d0 row he hd' hs0
            exact absurd ⟨k, le_rfl, dp', hσp, .inl hsp⟩ hne
        · exact .inr (.inr (.inr ⟨h0, hent⟩))

/-! ## The induction -/

/-- **The invariant at every position**, from the matrix steps, the local steps and the first
state of each lane. The local step at a position may use the invariant at all earlier
positions of the lane (the row a lane reads from `state_acc` was written by the lane itself
one tile earlier). -/
theorem val_hist {xs : ℕ → Inputs} {w w0 : ℕ}
    (hm : ∀ N, Val (L := L) xs w X w0 N → ∀ l < 32, ∀ k, X.MatrixK (w0 + l, k) N →
      ValAt (L := L) xs w X w0 l (k + 1))
    (hloc : ∀ l < 32, ∀ k e, X.get (w0 + l, k) = some e → isMatrix e = false →
      (∀ k' ≤ k, ValAt (L := L) xs w X w0 l k') → ValAt (L := L) xs w X w0 l (k + 1))
    (h0 : ∀ l < 32, ValAt (L := L) xs w X w0 l 0) : ∀ N, Val (L := L) xs w X w0 N := by
  have key : ∀ N, ∀ l < 32, ∀ k, ordinal X (w0 + l) k ≤ N →
      ∀ k' ≤ k, ValAt (L := L) xs w X w0 l k' := by
    intro N
    induction N with
    | zero =>
      intro l hl k
      induction k with
      | zero =>
        intro _ k' hk'
        have hk0 : k' = 0 := by omega
        subst hk0
        exact h0 l hl
      | succ k ih =>
        intro hk k' hk'
        rcases Nat.lt_or_ge k' (k + 1) with hlt | hge
        · exact ih (le_trans (ordinal_mono (Nat.le_succ k)) hk) k' (by omega)
        · have hk1 : k' = k + 1 := by omega
          subst hk1
          have hist := ih (le_trans (ordinal_mono (Nat.le_succ k)) hk)
          cases he : X.get (w0 + l, k) with
          | none => exact (valAt_of_none he (hist k le_rfl)).2
          | some e =>
            cases hmx : isMatrix e
            · exact hloc l hl k e he hmx hist
            · have hK : X.MatrixK (w0 + l, k) (ordinal X (w0 + l) k) := ⟨⟨e, he, hmx⟩, rfl⟩
              have := ordinal_succ_of_matrixK hK
              omega
    | succ N ihN =>
      intro l hl k
      induction k with
      | zero =>
        intro _ k' hk'
        have hk0 : k' = 0 := by omega
        subst hk0
        exact h0 l hl
      | succ k ih =>
        intro hk k' hk'
        rcases Nat.lt_or_ge k' (k + 1) with hlt | hge
        · exact ih (le_trans (ordinal_mono (Nat.le_succ k)) hk) k' (by omega)
        · have hk1 : k' = k + 1 := by omega
          subst hk1
          have hist := ih (le_trans (ordinal_mono (Nat.le_succ k)) hk)
          cases he : X.get (w0 + l, k) with
          | none => exact (valAt_of_none he (hist k le_rfl)).2
          | some e =>
            cases hmx : isMatrix e
            · exact hloc l hl k e he hmx hist
            · have hK : X.MatrixK (w0 + l, k) (ordinal X (w0 + l) k) := ⟨⟨e, he, hmx⟩, rfl⟩
              have hsucc := ordinal_succ_of_matrixK hK
              have hval : Val (L := L) xs w X w0 (ordinal X (w0 + l) k) :=
                fun l' hl' k'' ho => ihN l' hl' k'' (by omega) k'' le_rfl
              exact hm _ hval l hl k hK
  exact fun N l hl k ho => key N l hl k (by omega) k le_rfl

/-- **The invariant holds for every number of matrix events.** `hrows` gives the row a lane
reads at the first event of an `ldmatrix`, from the invariant at the earlier positions of the
lane. -/
theorem val_all (F : Followed L mem0 X) (R : ComputeRef P L X) (E : LoopExit P L X)
    {w0 w : ℕ} (W : Warp L w0) (hw : w < 4) {xs : ℕ → Inputs}
    (hch : ∀ l < 32, Chain xs (tileCount P L (w0 + l)))
    (hrows : ∀ l < 32, ∀ k d e, (∀ k' ≤ k, ValAt (L := L) xs w X w0 l k') →
      stateAt (code L) X (w0 + l) k = some (some d) → X.get (w0 + l, k) = some e →
      RowRead (xs (ordinal X (w0 + l) k / 182)) w l d e)
    (hsc : ScalarsRead (L := L) xs X w0)
    (hbase : Base (L := L) xs w X w0) (hfirst : FirstLoad (L := L) X w0) :
    ∀ N, Val (L := L) xs w X w0 N := by
  refine val_hist (fun N ih l hl k hk => (Gen.mstep F R E W hw hch ih hl hk).2) ?_ ?_
  · intro l hl k e he hnm hist
    have hrd : ∀ d, stateAt (code L) X (w0 + l) k = some (some d) →
        RowRead (xs (ordinal X (w0 + l) k / 182)) w l d e :=
      fun d hσ => hrows l hl k d e hist hσ he
    by_cases h0 : ordinal X (w0 + l) k % 182 = 0
    · exact local_zero R W h0 hbase hfirst hl he hnm rfl hrd
        (Gen.lpts F R W (w := w) hsc hl (n := 0) (by decide)) (hist k le_rfl)
    · exact (local_step (n := ordinal X (w0 + l) k % 182) rfl h0 he hnm rfl hrd
        (Gen.lpts F R W (w := w) hsc hl (Nat.mod_lt _ (by decide))) (hist k le_rfl)).2
  · intro l hl d hd
    have h0 : ordinal X (w0 + l) 0 = 0 := by simp [ordinal]
    rw [h0]
    refine .inr (.inr (.inr ⟨rfl, ?_⟩))
    rintro ⟨k', hk', d0, hσ0, hs0⟩
    have hk0 : k' = 0 := by omega
    subst hk0
    rw [stateAt_zero] at hσ0
    have hdd : (code L (w0 + l)).init = d0 := Option.some.inj (Option.some.inj hσ0)
    rw [← hdd] at hs0
    exact init_not_load L (w0 + l) hs0

/-- A point whose site is a matrix site is a matrix point. -/
theorem Pt.isMatrix_of_site {pt : Pt} {s : Site} (h : pt.Shape s)
    (hm : (∃ j row, s = .matrixLoadMx j row) ∨ (∃ j, s = .warpMma j) ∨
      (∃ j, s = .matrixMove j) ∨ ∃ j, s = .matrixStore j) : pt.isMatrix = true := by
  cases pt with
  | rd j =>
    have h : s = .matrixLoad j := h
    subst h
    rcases hm with ⟨_, _, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  | wr j =>
    obtain ⟨row, rfl⟩ := h
    rcases hm with ⟨_, _, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  | ld i =>
    have h : s = .load i := h
    subst h
    rcases hm with ⟨_, _, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ | ⟨_, h'⟩ <;> cases h'
  | mx j => rfl
  | mma j => rfl
  | mov j => rfl
  | st j => rfl

/-- The thread block of a lane of a compute warp. -/
theorem lane_block (hb : L.block = 192) {c w l : ℕ} (hw : w < 4) (hl : l < 32) :
    (c * L.block + 32 * w + l) / L.block = c := by
  rw [hb]
  omega

/-- **The induction over the tiles** (`TileInduction`): the hypotheses of `TileHyps` give the
claim `TileClaim`. -/
theorem tile_induction : TileInduction P L mem0 X := by
  intro H
  have hF := H.followed
  have hR := H.ref
  have hE := H.exit
  have hsc : ∀ c w, c < L.grid → w < 4 →
      ScalarsRead (L := L) (blockInputs P mem0 c) X (c * L.block + 32 * w) :=
    fun c w hc hw => scalars_read H.pre hF hR H.back H.bound hc hw rfl
  have hrows : ∀ c w, c < L.grid → w < 4 → ∀ l < 32, ∀ k d e,
      (∀ k' ≤ k, ValAt (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w) l k') →
      stateAt (code L) X (c * L.block + 32 * w + l) k = some (some d) →
      X.get (c * L.block + 32 * w + l, k) = some e →
      RowRead (blockInputs P mem0 c (ordinal X (c * L.block + 32 * w + l) k / 182)) w l d e := by
    intro c w hc hw l hl k d e hist hσ he j hs
    by_cases hst : ∃ bi m, loadSrc j = .state bi m
    · obtain ⟨bi, m, hbm⟩ := hst
      exact acc_rows H.pre hF hR H.back hE H.bound hc hw (H.warp c w hc hw) (hsc c w hc hw) hl
        (H.early c w hc hw l hl) hist hσ he hbm hs
    · exact rows_read_stage H.pre hF hR H.back H.bound hc hw rfl l hl k d e j
        (fun bi m h' => hst ⟨bi, m, h'⟩) hσ hs he
  have hch : ∀ c w, c < L.grid → w < 4 → ∀ l < 32,
      Chain (blockInputs P mem0 c) (tileCount P L (c * L.block + 32 * w + l)) := by
    intro c w hc hw l hl
    have hg : c < P.sequences * P.heads := H.pre.grid ▸ hc
    have hs : c % P.sequences < P.sequences :=
      Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hg; omega)
    have hh : c / P.sequences < P.heads := Nat.div_lt_of_lt_mul hg
    have hT : tileCount P L (c * L.block + 32 * w + l) = tiles (P.length (c % P.sequences)) := by
      unfold tileCount seqOf
      rw [lane_block H.pre.block hw hl]
    rw [hT]
    exact tileInputs_chain H.pre hs hh
  have hval : ∀ c w, c < L.grid → w < 4 → ∀ N,
      Val (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w) N := fun c w hc hw =>
    val_all hF hR hE (H.warp c w hc hw) hw (hch c w hc hw) (hrows c w hc hw) (hsc c w hc hw)
      (H.base c w hc hw) (H.first c w hc hw)
  have hhist : ∀ c w (hc : c < L.grid) (hw : w < 4) l (hl : l < 32) k, ∀ k' ≤ k,
      ValAt (L := L) (blockInputs P mem0 c) w X (c * L.block + 32 * w) l k' :=
    fun c w hc hw l hl _ k' _ => hval c w hc hw _ l hl k' rfl
  refine ⟨hval, ?_, ?_, ?_⟩
  · intro c w hc hw l hl k d e hσ he hso hms
    obtain ⟨q, hq, hok⟩ := hso
    have hloc := (Gen.lpts hF hR (H.warp c w hc hw) (w := w) (hsc c w hc hw) hl
      (k := k) (N := ordinal X (c * L.block + 32 * w + l) k)
      (Nat.mod_lt _ (by decide))).mem q hq
    exact (hloc.2 (Pt.isMatrix_of_site hok.1.shape hms) d e hσ he hok).1
  · intro c w hc hw l hl k d e hσ he hcov
    cases hmx : isMatrix e
    · rcases hcov with ⟨q, hq, hok⟩ | ⟨-, -, ⟨row, hs⟩, -⟩
      · obtain ⟨d', hnx, -⟩ :=
          ((Gen.lpts hF hR (H.warp c w hc hw) (w := w) (hsc c w hc hw) hl
            (Nat.mod_lt _ (by decide))).mem q hq).1 d e hσ he hmx rfl
            (hrows c w hc hw l hl k d e (hhist c w hc hw l hl k) hσ he) hok
        exact ⟨d', by rw [stateAt_next he hσ]; exact hnx⟩
      · obtain ⟨a, rfl, -, -⟩ := hR.storeRow _ k d _ 17 row
          ((H.warp c w hc hw).compute l hl) hσ hs he
        obtain ⟨s, dw, dp, dx⟩ := d
        cases hs
        refine ⟨after_matrixStoreWr_17 L (c * L.block + 32 * w + l)
          ⟨.matrixStoreWr 17 row, dw, dp, dx⟩, ?_⟩
        rw [stateAt_next he hσ, next_matrixStoreWr_17]
    · have hK : X.MatrixK (c * L.block + 32 * w + l, k)
          (ordinal X (c * L.block + 32 * w + l) k) := ⟨⟨e, he, hmx⟩, rfl⟩
      exact (Gen.mstep hF hR hE (H.warp c w hc hw) hw (hch c w hc hw)
        (hval c w hc hw _) hl hK).1
  · intro c w hc hw n pc s parts hI
    exact Gen.mops hF hR hE (H.warp c w hc hw) (hval c w hc hw n) pc s parts hI

end

end PTX.Kernels.FlashKdaFwd.Proof.Values
