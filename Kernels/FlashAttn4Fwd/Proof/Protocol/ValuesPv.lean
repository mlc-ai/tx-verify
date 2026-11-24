-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesOperands
public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsBaseCausality

@[expose] public section

/-! # The accumulator chain

`pvChain` proves `PvChain`. Fix a correction thread `g` of stage `st`, its row's softmax thread
`h` (`SoftPartner`) and the probabilities `pv` `h` stores (`SoftPStores`). With `n = kvBlocks P`,
the accumulator `accR u d` of tile `u` at column `d` is the sum `pvSum u d` of the tile's products
plus a base (`accBase`): zero for the first tile of an item, the correction's rescale store of
credit `u` at the cell when there is one (unique: `OAccFacts.corr_st_one`), `accR (u - 1) d`
otherwise.

By induction along the MMA thread (`pv_value`), a completed PV MMA of tile `u` (`pPolls = u + 1`)
and step `j` (`MmaStepFacts.pv_step`) leaves at a cell of `g`'s row and column `d` the base plus
the products of keys `t < 16 (j + 1)`. Its A elements are the probabilities `pv u (16 j + kk)`
(`pv_a_value`: the A cell of element `kk` is column `128 st + 64 + 8 j + kk / 2` of the row,
`MmaStepFacts.pv_a`, written by the softmax store of the tile, `TcMmaSources.pvAStores`, whose
word holds keys `16 j + 2 (kk / 2)` and `+ 1`, Core `AReadOk`), its B elements the V elements of
the keys (`SmemInputs.pvB`). Its accumulator source is the previous step of its block
(`TcMmaSources.pv_accSource_tile`), or for step 0 of a loop tile the rescale store of credit `u`
(`OAcc.o_accSource_store`) or else the last MMA of tile `u - 1`, its step 7
(`OAcc.o_accSource_skip`, `MmaStepFacts.pv_next`).

A correction load of credit `q` reads the last PV MMA of tile `q - 1` writing the cell
(`OAcc.o_readSource`), step 7 (`CorrCoverLast`), so it returns `accR (q - 1) d`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma ValuesOps

noncomputable section

namespace ValuesPv

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The product of key `k` of tile `u` at column `d`, for correction thread `g`. -/
def pvTerm (P : Params) (L : Launch) (g : Nat) (pv : Nat → Nat → ℝ) (u k d : Nat) : ℝ :=
  pv u k * P.v (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
    (visitKey P (u % kvBlocks P) k) d

open Classical in
/-- The accumulator of tile `u` at column `d` of correction thread `g`'s row of stage `st`. -/
def accR (P : Params) (L : Launch) (X : Execution) (g st : Nat) (pv : Nat → Nat → ℝ) :
    Nat → Nat → ℝ
  | 0, d => pvSum P L g pv 0 d
  | u + 1, d =>
    (if (u + 1) % kvBlocks P = 0 then 0
      else if hy : ∃ y, CorrStored L X g st (u + 1) d y then hy.choose
      else accR P L X g st pv u d) + pvSum P L g pv (u + 1) d

/-- The base the PV MMAs of tile `u` accumulate onto. -/
def accBase (P : Params) (L : Launch) (X : Execution) (g st : Nat) (pv : Nat → Nat → ℝ)
    (u d : Nat) : ℝ :=
  accR P L X g st pv u d - pvSum P L g pv u d

theorem pvSum_eq (g : Nat) (pv : Nat → Nat → ℝ) (u d : Nat) :
    pvSum P L g pv u d = ∑ t ∈ Finset.range (16 * (7 + 1)), pvTerm P L g pv u t d := rfl

theorem accBase_first {g st : Nat} {pv : Nat → Nat → ℝ} {u d : Nat} (hu : u % kvBlocks P = 0) :
    accBase P L X g st pv u d = 0 := by
  unfold accBase
  cases u with
  | zero => simp [accR]
  | succ u => simp [accR, hu]

theorem accBase_store {g st : Nat} {pv : Nat → Nat → ℝ} {u d : Nat} {y : ℝ}
    (hu : u % kvBlocks P ≠ 0) (hy : CorrStored L X g st u d y)
    (huniq : ∀ y', CorrStored L X g st u d y' → y' = y) :
    accBase P L X g st pv u d = y := by
  unfold accBase
  cases u with
  | zero => simp at hu
  | succ u =>
    have he : ∃ y, CorrStored L X g st (u + 1) d y := ⟨y, hy⟩
    simp only [accR, hu, ↓reduceIte, he, ↓reduceDIte, add_sub_cancel_right]
    exact huniq _ he.choose_spec

theorem accBase_skip {g st : Nat} {pv : Nat → Nat → ℝ} {u d : Nat}
    (hu : u % kvBlocks P ≠ 0) (hy : ¬ ∃ y, CorrStored L X g st u d y) :
    accBase P L X g st pv u d = accR P L X g st pv (u - 1) d := by
  unfold accBase
  cases u with
  | zero => simp at hu
  | succ u => simp only [accR, hu, ↓reduceIte, hy, ↓reduceDIte, add_sub_cancel_right,
      Nat.add_sub_cancel]

/-- A correction thread's rescale store of a credit at a column holds one value. -/
theorem corrStored_unique (ho : OAccFacts L X) {g st u d : Nat} {y y' : ℝ} (hg : g < L.threads)
    (h8 : 8 ≤ warpOf L g) (h12 : warpOf L g < 12) (hd : d < 128)
    (hy : CorrStored L X g st u d y) (hy' : CorrStored L X g st u d y') : y' = y := by
  obtain ⟨i, a, p, vals, hs, hq, hp, hc, hv⟩ := hy
  obtain ⟨i', a', p', vals', hs', hq', hp', hc', hv'⟩ := hy'
  have hcell : tcDataCell32 L g a' p' = tcDataCell32 L g a p := by
    simp only [tcDataCell32, Cell.mk.injEq, true_and]
    simp only [tcDataCell32] at hc hc'
    omega
  have hO : InO st (tcDataCell32 L g a' p') := by
    unfold InO
    rw [hc']
    omega
  have hii := ho.corr_st_one hg h8 h12 hs' hs hp' hp hcell hO (hq'.trans hq.symm)
  subst hii
  obtain ⟨pc, he⟩ := hs
  obtain ⟨pc', he'⟩ := hs'
  have hk := Option.some.inj (he.symm.trans he')
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  obtain ⟨-, rfl, rfl, -⟩ := hk
  have hpp : p' = p := by
    simp only [tcDataCell32] at hc hc'
    omega
  subst hpp
  rw [hv] at hv'
  simpa using hv'.symm

/-- A thread's register lane is its row. -/
theorem lane_row (hpre : Pre P L mem0) (g : Nat) : laneBase L g + laneOf L g = rowOf L g := by
  have hb := hpre.block
  unfold laneBase laneOf rowOf
  rw [hb]
  omega

/-- **The A elements of a PV MMA** at a row of correction thread `g`: the probabilities of the
row's softmax thread for the keys of the MMA's step. -/
theorem pv_a_value (H : Ctx P L mem0 X) {g st h : Nat} {pv : Nat → Nat → ℝ}
    (hpart : SoftPartner L g st h) (hpv : SoftPStores L X h pv) {i : EvId} {d : Nat}
    {s : OperandSpec} {acc : Bool} {mask : List Nat} {ops : AsyncCopy.MmaOperands}
    {row col : Nat} {cell : Cell} (hst : st < 2) (hi : X.MmaIssue i d s acc mask)
    (hops : X.async.mmaOperands i = some ops) (hpos : writeCell s d mask row col = some cell)
    (hO : InO st cell) (hcta : cell.cta = ctaOf L g)
    (hlane : cell.lane = laneBase L g + laneOf L g) {kk : Nat} (hkk : kk < 16) :
    Assumption.idealMmaElement (.f16 .f16 .f32) .a ops.a row kk =
      .ok (pv (pPolls L X i.1 st i.2 - 1) (16 * pvStep L X i.1 st i.2 + kk)) := by
  have B := H.base
  have hpre := B.pre
  have hc : X.MmaCell i cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  obtain ⟨hrow, -, hceq, -⟩ := mma_geom B.thread B.tc hi hpos
  obtain ⟨address, haT, hadd⟩ := H.steps.pv_a hst hi hc hO
  have haT' : s.aTmem.isSome = true := by simp [haT]
  obtain ⟨hkd, hm, -, hg, hws, -⟩ := TcMmaSources.pv_desc B.thread hi haT'
  -- the A cell of the element's first byte
  have hbytes : 2 * (row * 16 + kk) < Operand.bytes .a s.descriptor := by
    simp only [Operand.bytes, Operand.rows, Operand.extent, hkd, hm, hws, Kind.k, Kind.width]
    simp
    omega
  obtain ⟨⟨c, pos⟩, hac⟩ : ∃ c, aCell s (2 * (row * 16 + kk)) = some c := by
    rcases (B.tc.mma_shape hi).2.2.2.2.2.2.2.2.2 .a _ hbytes with ⟨loc, hl⟩ | ⟨-, hc⟩
    · rw [byteLoc_a_tmem haT'] at hl
      cases hl
    · exact hc
  obtain ⟨hcc, hpos2⟩ := aCell_pair_elem hm hg haT hkk hac
  obtain ⟨hac1, -, -⟩ := aCell_pair hac
  -- the softmax store of the A cell
  obtain ⟨h', k', a', j', vals', value, hh', hw', hs', hj', hceq', hu, hval, hwr, hl⟩ :=
    TcMmaSources.pvAStores hpre B.cons B.score B.tc B.thread B.p2 B.pReady B.p2Handoff B.live
      asms hi hac
  have hj8 := (H.steps.pv_step hst hi hc hO).1
  have hP' := (B.score.soft_st hh' hw' hs').1 j' hj'
  rw [← hceq', hcc] at hP'
  have hw4 : warpOf L h' / 4 = st := by
    unfold InP at hP'
    dsimp only at hP'
    omega
  have hcellO : cell = ⟨rowCta s row, row % 128, d % 2 ^ 16 + col⟩ := hceq
  have hpart' : SoftPartner L g st h' := by
    have hc2 : c = tcDataCell32 L h' a' j' := hceq'
    rw [hcc] at hc2
    simp only [tcDataCell32, Cell.mk.injEq] at hc2
    rw [hcellO] at hcta hlane
    dsimp only at hcta hlane
    refine ⟨hh', hw', hw4, ?_, ?_⟩
    · show h' / L.block = g / L.block
      rw [← hc2.1, hcta]
      rfl
    · rw [← lane_row hpre, ← lane_row hpre, ← hc2.2.1, hlane]
  have hhh : h' = h := Stats.soft_unique hpre (hpart'.2.2.2.1.trans hpart.2.2.2.1.symm)
    hpart'.2.1 hpart.2.1 (hpart'.2.2.1.trans hpart.2.2.1.symm)
    (hpart'.2.2.2.2.trans hpart.2.2.2.2.symm)
  subst hhh
  -- the stored word
  have hp1 := (B.score.pv_polls hi hc hO).1
  rw [hw4] at hu
  have hst' := hpv hs' (u := pPolls L X i.1 st i.2 - 1) (by rw [hw4, hu]; omega) hj'
  rw [hval] at hst'
  have hvv := Option.some.inj hst'
  subst hvv
  have hkey : pKey L h' a' j' = 16 * pvStep L X i.1 st i.2 + 2 * (kk / 2) := by
    unfold pKey
    rw [← hceq', hcc, hw4]
    dsimp only
    rw [hadd]
    omega
  rw [hkey] at hwr
  rw [hceq'] at hwr hl hac hac1
  -- the two bytes of the element
  have hsrc := fun {index pos : Nat} (ha : aCell s index = some (tcDataCell32 L h' a' j', pos)) =>
    Score.p_aReadSource hpre B.score B.oacc B.pReady B.p2Gate B.sFull hi hc hO ha hh'
      hw' hs' hj' (by rw [hw4]; exact hu) hl
  have hb0 := B.cons.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac⟩ (hsrc hac) hwr hops
    (by simp [Value.bytes, FloatFmt.bytes]; omega)
  have hb1 := B.cons.tcRead.2 _ _ _ _ _ _ _ ⟨_, _, _, _, hi, hac1⟩ (hsrc hac1) hwr hops
    (by simp [Value.bytes, FloatFmt.bytes]; omega)
  have hl2 := take_two hb0 hb1
  rcases Nat.even_or_odd kk with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hp0 : pos = 0 := by omega
    subst hp0
    have hk2 : 16 * pvStep L X i.1 st i.2 + 2 * (kk / 2) = 16 * pvStep L X i.1 st i.2 + kk := by
      omega
    rw [← hk2]
    exact idealMmaElement_of_bytes (by
      rw [hl2]
      simp [Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ])
  · have hp0 : pos = 2 := by omega
    subst hp0
    have hk2 : 16 * pvStep L X i.1 st i.2 + 2 * (kk / 2) + 1 =
        16 * pvStep L X i.1 st i.2 + kk := by omega
    rw [← hk2]
    exact idealMmaElement_of_bytes (by
      rw [hl2]
      simp [Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, List.range_succ])

/-- One K step more adds its sixteen products. -/
theorem pvTerm_step (g : Nat) (pv : Nat → Nat → ℝ) (u j d : Nat) (b : ℝ) :
    ∑ kk ∈ Finset.range 16, pv u (16 * j + kk) *
      P.v (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
        (visitKey P (u % kvBlocks P) (16 * j + kk)) d +
      (b + ∑ t ∈ Finset.range (16 * j), pvTerm P L g pv u t d) =
    b + ∑ t ∈ Finset.range (16 * (j + 1)), pvTerm P L g pv u t d := by
  rw [Nat.mul_succ, Finset.sum_range_add]
  unfold pvTerm
  ring

/-- **The value of a completed PV MMA** at a cell of correction thread `g`'s row: the base of its
tile plus the products of its K steps so far. -/
theorem pv_value (H : Ctx P L mem0 X) {g st h : Nat} {pv : Nat → Nat → ℝ} (hg : g < L.threads)
    (h8 : 8 ≤ warpOf L g) (h12 : warpOf L g < 12) (hst : st < 2) (hpart : SoftPartner L g st h)
    (hpv : SoftPStores L X h pv) :
    ∀ k g' d s acc mask row col cell, X.MmaIssue (g', k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g', k) = true → InO st cell →
      cell.cta = ctaOf L g → cell.lane = laneBase L g + laneOf L g →
      Result L asms X (g', k) cell (.float .f32
        (accBase P L X g st pv (pPolls L X g' st k - 1) col +
          ∑ t ∈ Finset.range (16 * (pvStep L X g' st k + 1)),
            pvTerm P L g pv (pPolls L X g' st k - 1) t col)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g' d s acc mask row col cell hi hpos hd hO hcta hlane
  have B := H.base
  have hpre := B.pre
  have hc : X.MmaCell (g', k) cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  obtain ⟨-, hcol, hceq, -⟩ := mma_geom B.thread B.tc hi hpos
  have h0 := (col0_pv B.score B.thread B.tc hi hpos hO).1
  obtain ⟨ops, hops⟩ := TcMmaSources.operands_of_done B.cons hd
  have hlead : leadCta (ctaOf L g) = ctaOf L g' := by
    rw [← hcta]
    exact (Score.mma_o B.score hi hc hO cell hc).2
  have ha := fun kk (hkk : kk < 16) => pv_a_value H hpart hpv hst hi hops hpos hO hcta hlane hkk
  have hb : ∀ kk, kk < 16 → Assumption.idealMmaElement (.f16 .f16 .f32) .b ops.b col kk = .ok
      (P.v (tileBatch L g ((pPolls L X g' st k - 1) / kvBlocks P))
        (tileHead L g ((pPolls L X g' st k - 1) / kvBlocks P))
        (visitKey P ((pPolls L X g' st k - 1) % kvBlocks P) (16 * pvStep L X g' st k + kk))
          col) := by
    intro kk hkk
    rw [H.inputs.pvB hst hi hd hops hc hO hcol hkk]
    obtain ⟨t1, t2, -⟩ := pair_tile hpre hlead ((pPolls L X g' st k - 1) / kvBlocks P) st
    rw [t1, t2]
  obtain ⟨hj8, hfirst⟩ := H.steps.pv_step hst hi hc hO
  -- the earlier MMAs of the region write the cell
  have hreg : ∀ k', PvAt X g' st k' → ∃ d' s' a' m', X.MmaIssue (g', k') d' s' a' m' ∧
      writeCell s' d' m' row col = some cell := by
    rintro k' ⟨⟨d', s', a', m', hi'⟩, c', hc', hO'⟩
    refine ⟨d', s', a', m', hi', ?_⟩
    rw [region_cell B.score B.tc B.thread hst hi' hi hc' hc rfl (.inr ⟨hO', hO⟩) row col]
    exact hpos
  cases acc
  · -- the first tile of an item overwrites
    obtain ⟨hj0, hu0⟩ := hfirst.mp rfl
    refine .overwrite hi hpos hops ?_
    rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_none none), accBase_first hu0, hj0]
    have := pvTerm_step (P := P) (L := L) g pv (pPolls L X g' st k - 1) 0 col 0
    simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, add_zero,
      zero_add] at this ⊢
    rw [this]
  · classical
    have hne : ¬ (pvStep L X g' st k = 0 ∧ (pPolls L X g' st k - 1) % kvBlocks P = 0) :=
      fun h => by cases hfirst.mpr h
    obtain ⟨k0, hk0, hc0, hcnt0⟩ := B.thread.pv_acc hi hc hO
    let Q : Nat → Prop := fun k' => k' < k ∧ X.MmaCell (g', k') cell
    have hQ : Q (Nat.findGreatest Q k) := Nat.findGreatest_spec (m := k0) hk0.le ⟨hk0, hc0⟩
    have hmax : ∀ k', Q k' → k' ≤ Nat.findGreatest Q k := fun k' hk =>
      Nat.le_findGreatest hk.1.le hk
    set K := Nat.findGreatest Q k
    obtain ⟨hK, hcK⟩ := hQ
    have hm1 := TcMmaSources.pPolls_mono (L := L) (X := X) (g := g') (st := st)
      (hmax k0 ⟨hk0, hc0⟩)
    have hm2 := TcMmaSources.pPolls_mono (L := L) (X := X) (g := g') (st := st) hK.le
    simp only at hcnt0
    obtain ⟨dK, sK, aK, mK, rK, cK, hiK, hposK⟩ := id hcK
    have hposK' : writeCell sK dK mK row col = some cell := by
      rw [region_cell B.score B.tc B.thread hst hiK hi hcK hc rfl (.inr ⟨hO, hO⟩) row col]
      exact hpos
    have hdK := TcMmaSources.src_done B.cons B.score B.tc B.thread hi hc hK hcK hd
    have hPK : PvAt X g' st K := ⟨⟨_, _, _, _, hiK⟩, cell, hcK, hO⟩
    have hPk : PvAt X g' st k := ⟨⟨_, _, _, _, hi⟩, cell, hc, hO⟩
    have hIH := ih K hK g' dK sK aK mK row col cell hiK hposK' hdK hO hcta hlane
    by_cases htile : pPolls L X g' st K = pPolls L X g' st k
    · -- the previous step of the block
      have hsrc := TcMmaSources.pv_accSource_tile B.score B.oacc B.pReady B.oReady B.live hst hi
        hc hO hK hcK htile hmax
      have hstep : pvStep L X g' st k = pvStep L X g' st K + 1 := by
        unfold pvStep
        refine count_succ (A := PvAt X g' st) (f := pPolls L X g' st) hK hPK htile
          fun k' h1 h2 hq => ?_
        obtain ⟨d', s', a', m', hi', hp'⟩ := hreg k' hq
        have := hmax k' ⟨h2, ⟨_, _, _, _, _, _, hi', hp'⟩⟩
        omega
      rw [htile] at hIH
      refine .accumulate hi hpos hops hIH hsrc ?_
      rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_f32 _), hstep]
      rw [hstep] at ha
      rw [pvTerm_step]
    · -- step 0 of a loop tile
      have hprev : pPolls L X g' st K + 1 = pPolls L X g' st k := by omega
      have hj0 : pvStep L X g' st k = 0 := by
        unfold pvStep
        refine count_zero fun k' hk' hq heq => ?_
        obtain ⟨d', s', a', m', hi', hp'⟩ := hreg k' hq
        have := hmax k' ⟨hk', ⟨_, _, _, _, _, _, hi', hp'⟩⟩
        have := TcMmaSources.pPolls_mono (L := L) (X := X) (g := g') (st := st) this
        omega
      have hun : (pPolls L X g' st k - 1) % kvBlocks P ≠ 0 := fun h => hne ⟨hj0, h⟩
      have hp1 := (B.score.pv_polls hiK hcK hO).1
      have hu : pPolls L X g' st k - 1 = pPolls L X g' st K := by omega
      have hfirstX : ∀ x, IsMma X x → X.MmaCell x cell →
          pPolls L X g' st K + 1 ≤ pPolls L X x.1 st x.2 → x = (g', k) ∨ (g', k).2 < x.2 := by
        intro x hx hcx hle
        have hx1 : x.1 = g' := Floats.mma_thread B.score hx ⟨_, _, _, _, hi⟩ hcx hc
        obtain ⟨xg, xk⟩ := x
        simp only at hx1 hle ⊢
        subst hx1
        rcases Nat.lt_trichotomy xk k with h1 | rfl | h1
        · have := hmax xk ⟨h1, hcx⟩
          have := TcMmaSources.pPolls_mono (L := L) (X := X) (g := xg) (st := st) this
          omega
        · exact .inl rfl
        · exact .inr h1
      have hlive := TcMmaSources.sourceLive (src := (0, 0)) B.live ⟨_, _, _, _, hi⟩ (.inl hc)
      by_cases hex : ∃ g2 k2 a2 j2, ∃ vals2 : List Value, X.TSt (g2, k2) a2 vals2 .s32x32b ∧
          j2 < vals2.length ∧ tcDataCell32 L g2 a2 j2 = cell ∧
          pArr L X g2 st k2 = pPolls L X g' st K
      · -- the rescale store of credit `u`
        obtain ⟨g2, k2, a2, j2, vals2, hs2, hj2, hc2, hpa⟩ := hex
        obtain ⟨hg2, hw2⟩ := B.score.tc_role (.inr hs2)
        have h82 : 8 ≤ warpOf L g2 := by
          by_contra hlt
          have hP' := (B.score.soft_st hg2 (by omega) hs2).1 j2 hj2
          rw [hc2] at hP'
          unfold InP at hP'
          unfold InO at hO
          omega
        have hgg : g2 = g := by
          refine cell_thread hpre (a := a2) (a' := 0) (j := j2) (j' := cell.column)
            (by omega) ?_
          rw [hc2, hceq]
          rw [hceq] at hcta hlane
          simp only [tcDataCell32, Cell.mk.injEq] at hcta hlane ⊢
          exact ⟨hcta, hlane, by simp⟩
        subst hgg
        subst hc2
        obtain ⟨y, hy⟩ :=
          TcMmaSources.corrStore_f32 B hg h8 h12 hs2 vals2[j2] (List.getElem_mem hj2)
        have hcolc : (tcDataCell32 L g2 a2 j2).column = 256 + 128 * st + col := by
          rw [hceq, h0]
        have hCS : CorrStored L X g2 st (pPolls L X g' st k - 1) col y :=
          ⟨k2, a2, j2, vals2, hs2, by rw [hpa, hu], hj2, hcolc,
            by rw [List.getElem?_eq_getElem hj2, hy]⟩
        have hsrc := OAcc.o_accSource_store hpre B.score B.oacc B.pReady B.oReady hg h8 h12 hs2
          hj2 hO ⟨_, _, _, _, hi⟩ hc (by show pPolls L X g' st k = _; rw [hpa]; omega)
          (fun x hx hcx hle => hfirstX x hx hcx (by rw [← hpa]; exact hle))
          (TcMmaSources.sourceLive B.live ⟨_, _, _, _, hi⟩ (.inl hc))
        refine .accumulateStored hi hpos hops (old := .float .f32 y)
          ⟨a2, vals2, _, j2, hs2, by rw [List.getElem?_eq_getElem hj2, hy],
            (tcDataCell_s32x32b _ _ _ _).symm⟩ hsrc ?_
        rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_f32 _),
          accBase_store hun hCS (fun y' h' => corrStored_unique B.oacc hg h8 h12 hcol hCS h'),
          hj0]
        have := pvTerm_step (P := P) (L := L) g2 pv (pPolls L X g' st k - 1) 0 col y
        simp only [Nat.mul_zero, Nat.zero_add, Finset.range_zero, Finset.sum_empty,
          add_zero] at this ⊢
        rw [this]
      · -- no rescale: the last MMA of the tile before, its step 7
        have hskip : ∀ g2 k2 a2 j2 : Nat, ∀ vals2 : List Value, X.TSt (g2, k2) a2 vals2 .s32x32b →
            j2 < vals2.length → tcDataCell32 L g2 a2 j2 = cell →
            pArr L X g2 st k2 ≠ pPolls L X (g', K).1 st (g', K).2 :=
          fun g2 k2 a2 j2 vals2 hs2 hj2 hc2 hpa => hex ⟨g2, k2, a2, j2, vals2, hs2, hj2, hc2, hpa⟩
        have hlast : ∀ x, IsMma X x → X.MmaCell x cell →
            pPolls L X x.1 st x.2 ≤ pPolls L X (g', K).1 st (g', K).2 →
            x = (g', K) ∨ x.2 < (g', K).2 := by
          intro x hx hcx hle
          have hx1 : x.1 = g' := Floats.mma_thread B.score hx ⟨_, _, _, _, hi⟩ hcx hc
          obtain ⟨xg, xk⟩ := x
          simp only at hx1 hle ⊢
          subst hx1
          rcases Nat.lt_trichotomy xk K with h1 | rfl | h1
          · exact .inr h1
          · exact .inl rfl
          · exfalso
            by_cases hxk : xk < k
            · exact absurd (hmax xk ⟨hxk, hcx⟩) (by omega)
            · have := TcMmaSources.pPolls_mono (L := L) (X := X) (g := xg) (st := st)
                (show k ≤ xk by omega)
              omega
        have hsrc := OAcc.o_accSource_skip B.score B.oacc B.pReady B.oReady hO hst
          ⟨_, _, _, _, hiK⟩ hcK ⟨_, _, _, _, hi⟩ hc (by simp only; omega) hlast
          (fun x hx hcx hle => hfirstX x hx hcx hle) hskip
          (TcMmaSources.sourceLive B.live ⟨_, _, _, _, hi⟩ (.inl hc))
        have hK7 : pvStep L X g' st K = 7 := by
          have hK8 := (H.steps.pv_step hst hiK hcK hO).1
          by_contra hne7
          obtain ⟨k'', h1, h2, hq, -⟩ := H.steps.pv_next hst hPK (by simp only at hK8; omega)
            hPk hK (by omega)
          obtain ⟨d', s', a', m', hi', hp'⟩ := hreg k'' hq
          have := hmax k'' ⟨h2, ⟨_, _, _, _, _, _, hi', hp'⟩⟩
          omega
        have hnoCS : ¬ ∃ y, CorrStored L X g st (pPolls L X g' st k - 1) col y := by
          rintro ⟨y, i2, a2, p2, vals2, hs2, hpa, hp2, hcol2, -⟩
          refine hex ⟨g, i2, a2, p2, vals2, hs2, hp2, ?_, by rw [hpa, hu]⟩
          rw [hceq]
          rw [hceq] at hcta hlane
          simp only [tcDataCell32, Cell.mk.injEq] at hcta hlane hcol2 ⊢
          exact ⟨hcta.symm, hlane.symm, by rw [hcol2, h0]⟩
        rw [hK7, ← hu] at hIH
        refine .accumulate hi hpos hops hIH hsrc ?_
        rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_f32 _), accBase_skip hun hnoCS,
          hj0]
        have hR : accR P L X g st pv (pPolls L X g' st k - 1 - 1) col =
            accBase P L X g st pv (pPolls L X g' st k - 1 - 1) col +
              ∑ t ∈ Finset.range (16 * (7 + 1)),
                pvTerm P L g pv (pPolls L X g' st k - 1 - 1) t col := by
          rw [← pvSum_eq]
          unfold accBase
          ring
        rw [← hR]
        have := pvTerm_step (P := P) (L := L) g pv (pPolls L X g' st k - 1) 0 col
          (accR P L X g st pv (pPolls L X g' st k - 1 - 1) col)
        simp only [Nat.mul_zero, Nat.zero_add, Finset.range_zero, Finset.sum_empty,
          add_zero] at this ⊢
        rw [this]

/-- **The accumulator** (`PvChain`). -/
theorem pvChain (H : Ctx P L mem0 X) : PvChain P L X := by
  intro g st h pv hg h8 h12 hst hpart hpv
  have B := H.base
  have hpre := B.pre
  refine ⟨accR P L X g st pv, fun u d hu hd => ?_, fun u d y hu hd hy => ?_,
    fun u d hu hd hy => ?_, fun {i a p q vals} hld hq hp hO => ?_⟩
  · have := accBase_first (L := L) (X := X) (g := g) (st := st) (pv := pv) (d := d) hu
    unfold accBase at this
    linarith
  · have := accBase_store (pv := pv) hu hy
      (fun y' h' => corrStored_unique B.oacc hg h8 h12 hd hy h')
    unfold accBase at this
    linarith
  · have := accBase_skip (pv := pv) hu hy
    unfold accBase at this
    linarith
  · -- a correction load of credit `q` reads step 7 of tile `q - 1`
    obtain ⟨x0, hx0, hxc0, hn0, h7⟩ := H.corrCover hg h8 h12 hld hp hO
    obtain ⟨src, hsrc, hsc, hF, hlast⟩ := Floats.last_mma B.score
      (fun x => pPolls L X x.1 st x.2) (fun g k k' hk => TcMmaSources.pPolls_mono hk) hx0 hxc0
    have hthr : x0.1 = src.1 := Floats.mma_thread B.score hx0 hsrc hxc0 hsc
    obtain ⟨g0, k0⟩ := x0
    obtain ⟨g1, k1⟩ := src
    simp only at hthr
    subst hthr
    dsimp only at hn0 h7 hxc0 hsc
    have hF' : pPolls L X g0 st k1 = pPolls L X g0 st k0 := hF
    obtain ⟨d, s, acc, mask, row, col, hsi, hpos⟩ := id hsc
    have hstep : pvStep L X g0 st k1 = 7 := by
      rcases hlast (g0, k0) hx0 hxc0 hF'.symm.le with he | hlt
      · simp only [Prod.mk.injEq] at he
        rw [← he.2]
        exact h7
      · exfalso
        have hlt8 : pvStep L X g0 st k1 < 8 := (H.steps.pv_step hst hsi hsc hO).1
        have hc : pvStep L X g0 st k0 < pvStep L X g0 st k1 :=
          pvStep_lt hlt ⟨hx0, _, hxc0, hO⟩ hF'.symm
        omega
    have hcnt : pPolls L X g0 st k1 = pArr L X g st i := by omega
    obtain ⟨st', -, hcells, -, -⟩ := B.oacc.corr_ld hg h8 h12 hld
    have hst' : st' = st := by
      have := hcells p hp
      unfold InO at this hO
      omega
    rw [hst'] at hcells
    have hcs : ctaOf L g0 = leadCta (tcDataCell32 L g a p).cta := OAcc.mma_cta B.score hsi hsc hO
    have hdone : DoneBefore L X (g0, k1) (g, i) :=
      B.oReady hg h8 h12 hld hcells hsrc ⟨_, hsc, hO⟩ hcs hcnt.le
    have hd := hdone.done B.cons.tcCommit
    have hres := pv_value H hg h8 h12 hst hpart hpv k1 g0 d s acc mask row col _ hsi hpos hd hO
      rfl rfl
    have hla : Tmem.Pair.Access L X (g, i) (tcDataCell32 L g a p) :=
      .inr (.inl ⟨p, loadCell32 hld hp⟩)
    have hrs := OAcc.o_readSource hpre B.score B.oacc B.pReady B.oReady hg h8 h12 hld hp hO hsrc
      hsc hcnt hlast
      (fun cta r hr hcov rel hrel => .inl (H.base.tmemLive hla cta r hr hcov rel hrel))
    rw [LoadReadOk.f32 B.cons.tcRead.1 hld (loadCell32 hld hp) hrs (.inl hres)]
    obtain ⟨-, -, hceq, -⟩ := mma_geom B.thread B.tc hsi hpos
    have h0 := (col0_pv B.score B.thread B.tc hsi hpos hO).1
    have hk : (tcDataCell32 L g a p).column - (256 + 128 * st) = col := by
      rw [hceq, h0]
      simp only
      omega
    rw [hk, hstep, hcnt, hq, ← pvSum_eq]
    unfold accBase
    simp

end ValuesPv

end
end PTX.Kernels.FlashAttn4Fwd.Proof
