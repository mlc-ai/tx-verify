-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ValuesOperands

@[expose] public section

/-! # The scores a softmax load returns

`scoreLoads` proves `ScoreLoads`. With `n = kvBlocks P`, the QK MMAs of stage `st` and score tile
`u` (`sCommits = u`) form one block of eight K steps (`MmaStepFacts.qk_step`). By induction along
the MMA thread (`qk_value`), a completed QK MMA of step `j` leaves at output `(row, col)` the sum
over the head-dimension indices `t < 16 (j + 1)` of `Q(row', t) · K(key, t)` (`qkPrefix`), with
`row'` its tile's query row `row` and `key` the visit's key `col` (`SmemInputs`): step 0
overwrites; a later step accumulates onto the last MMA of its thread before it writing the cell
(`TcMmaSources.qk_accSource_last`), which is the previous step of its block (`count_succ`). The
ideal MMA adds the sixteen products of its K step (`eval_mma`).

A softmax load of tile `u` reads the last QK MMA of the tile writing the cell
(`Score.s_readSource`, `Floats.last_mma`); it is step 7 (`SoftCoverLast`, `count_lt`), so the load
returns the full dot product, which is the score of the thread's row (`cell_row`, `pair_tile`)
with the visit's key of the cell's column (`col0_qk`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma ValuesOps

noncomputable section

namespace ValuesScore

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The sum over the first `m` head-dimension indices of `Q · K` of output `(row, col)` of score
tile `u` of stage `st`, for the MMA thread `g`. -/
def qkPrefix (P : Params) (L : Launch) (g st u row col m : Nat) : ℝ :=
  ∑ t ∈ Finset.range m,
    P.q (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
      (tileRow L g (u / kvBlocks P) st + row) t *
    P.k (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
      (visitKey P (u % kvBlocks P) col) t

/-- One K step more adds its sixteen products. -/
theorem qkPrefix_step (g st u row col j : Nat) :
    ∑ kk ∈ Finset.range 16,
      P.q (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
        (tileRow L g (u / kvBlocks P) st + row) (16 * j + kk) *
      P.k (tileBatch L g (u / kvBlocks P)) (tileHead L g (u / kvBlocks P))
        (visitKey P (u % kvBlocks P) col) (16 * j + kk) + qkPrefix P L g st u row col (16 * j) =
      qkPrefix P L g st u row col (16 * (j + 1)) := by
  unfold qkPrefix
  rw [Nat.mul_succ, Finset.sum_range_add, add_comm]

/-- **The value of a completed QK MMA**: at output `(row, col)`, the prefix of the dot product
over its K steps so far. -/
theorem qk_value (H : Ctx P L mem0 X) :
    ∀ k g d s acc mask row col cell st, st < 2 → X.MmaIssue (g, k) d s acc mask →
      writeCell s d mask row col = some cell → X.async.mmaDone (g, k) = true → InS st cell →
      Result L asms X (g, k) cell (.float .f32
        (qkPrefix P L g st (sCommits L X g st k) row col (16 * (qkStep L X g st k + 1)))) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro g d s acc mask row col cell st hst hi hpos hd hS
  have B := H.base
  have hc : X.MmaCell (g, k) cell := ⟨_, _, _, _, _, _, hi, hpos⟩
  obtain ⟨hrow, hcol, -, -⟩ := mma_geom B.thread B.tc hi hpos
  obtain ⟨ops, hops⟩ := TcMmaSources.operands_of_done B.cons hd
  have ha := fun kk (hkk : kk < 16) => H.inputs.qkA hst hi hd hops hc hS hrow hkk
  have hb := fun kk (hkk : kk < 16) => H.inputs.qkB hst hi hd hops hc hS hcol hkk
  obtain ⟨-, hfirst⟩ := H.steps.qk_step hst hi hc hS
  cases acc
  · -- step 0 overwrites
    have h0 := hfirst rfl
    refine .overwrite hi hpos hops ?_
    rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_none none), h0]
    have := qkPrefix_step (P := P) (L := L) g st (sCommits L X g st k) row col 0
    simp only [Nat.mul_zero, Nat.zero_add] at this ⊢
    rw [← this]
    simp [qkPrefix]
  · -- a later step accumulates onto the previous step
    classical
    obtain ⟨k0, hk0, hc0, hcnt0⟩ := B.thread.qk_acc hi hc hS
    let Q : Nat → Prop := fun k' => k' < k ∧ X.MmaCell (g, k') cell
    have hQ : Q (Nat.findGreatest Q k) := Nat.findGreatest_spec (m := k0) hk0.le ⟨hk0, hc0⟩
    have hmax : ∀ k', Q k' → k' ≤ Nat.findGreatest Q k := fun k' hk =>
      Nat.le_findGreatest hk.1.le hk
    set K := Nat.findGreatest Q k
    obtain ⟨hK, hcK⟩ := hQ
    have hm1 := TcMmaSources.sCommits_mono (L := L) (X := X) (g := g) (st := st)
      (hmax k0 ⟨hk0, hc0⟩)
    have hm2 := TcMmaSources.sCommits_mono (L := L) (X := X) (g := g) (st := st) hK.le
    have hcntK : sCommits L X g st K = sCommits L X g st k := by simp only at hcnt0; omega
    have hsrc := TcMmaSources.qk_accSource_last B.score B.oacc B.sFull B.pReady B.p2Gate B.live
      hst hi hc hS hK hcK hcntK hmax
    obtain ⟨dK, sK, aK, mK, rK, cK, hiK, hposK⟩ := id hcK
    have hposK' : writeCell sK dK mK row col = some cell := by
      rw [region_cell B.score B.tc B.thread hst hiK hi hcK hc rfl (.inl ⟨hS, hS⟩) row col]
      exact hpos
    have hdK := TcMmaSources.src_done B.cons B.score B.tc B.thread hi hc hK hcK hd
    have hIH := ih K hK g dK sK aK mK row col cell st hst hiK hposK' hdK hS
    -- the step of `k` is one more than `K`'s
    have hstep : qkStep L X g st k = qkStep L X g st K + 1 := by
      unfold qkStep
      refine count_succ (A := QkAt X g st) (f := sCommits L X g st) hK
        ⟨⟨_, _, _, _, hiK⟩, cell, hcK, hS⟩ hcntK fun k' h1 h2 hq => ?_
      obtain ⟨⟨d', s', a', m', hi'⟩, c', hc', hS''⟩ := hq
      obtain ⟨_, _, _, _, r', co', hi'', hp'⟩ := id hc'
      have hpos' : writeCell s' d' m' row col = some cell := by
        rw [region_cell B.score B.tc B.thread hst hi' hi hc' hc rfl (.inl ⟨hS'', hS⟩) row col]
        exact hpos
      have := hmax k' ⟨h2, ⟨_, _, _, _, _, _, hi', hpos'⟩⟩
      omega
    rw [hcntK] at hIH
    refine .accumulate hi hpos hops hIH hsrc ?_
    rw [eval_mma B hi hops hpos ha hb (idealMmaAccumulator_f32 _), hstep]
    rw [hstep] at ha
    have := qkPrefix_step (P := P) (L := L) g st (sCommits L X g st k) row col
      (qkStep L X g st K + 1)
    rw [this]

/-- **The scores** (`ScoreLoads`): every softmax load returns the scores of its tile. -/
theorem scoreLoads (H : Ctx P L mem0 X) : ScoreLoads P L X := by
  intro h hh hw i a p u vals hld hpoll hp
  have B := H.base
  have hpre := B.pre
  set st := warpOf L h / 4 with hstdef
  have hst : st < 2 := by omega
  have hS' := (B.score.soft_ld hh hw hld).1 p hp
  obtain ⟨x0, hx0, hxc0, hn0, h7⟩ := H.softCover hh hw hld hp
  obtain ⟨src, hsrc, hsc, hF, hlast⟩ := Floats.last_mma B.score
    (fun x => sCommits L X x.1 st x.2) (fun g k k' hk => countP_take_mono _ (X.tr g) hk) hx0 hxc0
  have hthr : x0.1 = src.1 := Floats.mma_thread B.score hx0 hsrc hxc0 hsc
  obtain ⟨g0, k0⟩ := x0
  obtain ⟨g1, k1⟩ := src
  simp only at hthr
  subst hthr
  dsimp only at hn0 h7 hxc0 hsc
  rw [← hstdef] at hn0 h7
  have hF' : sCommits L X g0 st k1 = sCommits L X g0 st k0 := hF
  obtain ⟨d, s, acc, mask, row, col, hsi, hpos⟩ := id hsc
  -- the source is step 7
  have hstep : qkStep L X g0 st k1 = 7 := by
    rcases hlast (g0, k0) hx0 hxc0 hF'.symm.le with he | hlt
    · simp only [Prod.mk.injEq] at he
      rw [← he.2]
      exact h7
    · exfalso
      have hlt8 : qkStep L X g0 st k1 < 8 := (H.steps.qk_step hst hsi hsc hS').1
      have hc : qkStep L X g0 st k0 < qkStep L X g0 st k1 :=
        qkStep_lt hlt ⟨hx0, _, hxc0, hS'⟩ hF'.symm
      have h7' : qkStep L X g0 st k0 = 7 := h7
      omega
  -- the source is done before the load
  have hcnt : sCommits L X g0 st k1 + 1 = sPolls L X h st i := by omega
  have hlead : leadCta (ctaOf L g0) = leadCta (ctaOf L h) := by
    rw [(Score.mma_in B.score hsrc).2, ← (Score.mma_s B.score hsi hsc hS' hst _ hsc).2]
    rfl
  have hdone := Score.s_doneBefore B.score B.sFull hh hw hsrc hlead hcnt.le (Score.TLd.lt hld)
  have hd := hdone.done B.cons.tcCommit
  have hres := qk_value H k1 g0 d s acc mask row col _ st hst hsi hpos hd hS'
  -- the read
  have hla : Tmem.Pair.Access L X (h, i) (tcDataCell32 L h a p) :=
    .inr (.inl ⟨p, loadCell32 hld hp⟩)
  have hrs := Score.s_readSource hpre B.score B.oacc B.pReady B.p2Gate B.sFull hh hw hld hp
    hsrc hsc hcnt hlast
    (fun cta r hr hcov rel hrel => .inl (H.base.tmemLive hla cta r hr hcov rel hrel))
  rw [LoadReadOk.f32 B.cons.tcRead.1 hld (loadCell32 hld hp) hrs (.inl hres)]
  -- the cell's row and key
  obtain ⟨hrow, hcol, hceq, -⟩ := mma_geom B.thread B.tc hsi hpos
  have h0 := col0_qk B.score B.thread B.tc hsi hpos hS' hst
  obtain ⟨hlo, hhi, hev⟩ := mma_ctas hpre B.score B.tc B.thread hsi
  obtain ⟨hr, hl⟩ := cell_row hpre hlo hhi hev hrow hceq
  have hu : sCommits L X g0 st k1 = u := by omega
  have hk : (tcDataCell32 L h a p).column - 128 * st = col := by
    rw [hceq, h0]
    simp only
    omega
  rw [hk, hstep, hu]
  obtain ⟨t1, t2, t3⟩ := pair_tile hpre hl (u / kvBlocks P) st
  unfold qkPrefix tileScore score
  rw [t1, t2, hr, ← Nat.add_assoc, t3]

end ValuesScore

end
end PTX.Kernels.FlashAttn4Fwd.Proof
