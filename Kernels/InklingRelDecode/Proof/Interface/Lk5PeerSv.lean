-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5WPair
public import Kernels.InklingRelDecode.Proof.Interface.RdSmProg

@[expose] public section

/-!
# The exchange with the partner lane, by induction on the iteration (`Sv.ExchPrem`)

`Sv.sv_inv_at` takes the exchange with the partner lane at every shuffle of the row maximum. The
partner's visible scores at the shuffle of iteration `I` are its invariant's `own` clause, which
needs the exchange only at the partner's shuffles of earlier iterations. So:

* `rank`, `rank_mono`: `2 i` before the stage's second exchange of iteration `i`, `2 i + 1` from
  it on; a step does not lower it;
* `sv_inv_upto`: the iteration invariant at the states of rank at most `2 I`, from the exchange at
  the shuffles of iterations below `I`;
* `exchEv_at`: the exchange at one shuffle of the row maximum, from `PeerAt` there: the partner's
  states at the two shuffles of the iteration are found by the count of shuffles
  (`sm_shfl_peer_d`) and are its only states there (`sm_shfl_unique`);
* `exch_lt`: the exchange at every shuffle of an iteration below `I`, for every thread of a valid
  row, by induction on `I`: at iteration `I` the partner has `Sm.Peer` (`pair_iter`) and its
  visible scores are the other half's (`sv_inv_upto` for the partner);
* `exchPrem_full`: `Sv.ExchPrem`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Sv

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The stage of a state: `2 i` up to the row maximum's exchange of iteration `i`, `2 i + 1`
after it. -/
def rank (d : D) : Nat := 2 * d.i + (if Late d.site = true then 1 else 0)

theorem rank_mono {g : Nat} {d0 d : D} {e : Event} (hn : Sm.next L g d0 e = some (some d)) :
    rank d0 ≤ rank d := by
  unfold rank
  rcases next_iter hn with hi | ⟨hi, -, -⟩
  · by_cases hl : Late d0.site = true
    · have := late_next hn hl hi
      simp only [hl, this, ↓reduceIte, hi, le_refl]
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, hi]
      omega
  · split <;> split <;> omega

/-- The score premise, in the form of `Sv.SvPrem.score`. -/
def ScorePrem (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {d : D} {e : Event}, g < L.threads → ValidRow Q L g →
    X.get (g, k) = some e → St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    ScoreEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d.i e

/-- **The iteration invariant up to iteration `I`**, from the exchange at the shuffles of the
iterations below `I`. -/
theorem sv_inv_upto (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hM : SmMaxOk Q L X) (hS : ScorePrem Q L X) {g : Nat}
    (hg : g < L.threads)
    (hvr : ValidRow Q L g) {B : Nat → List (ℝ × ℝ)}
    (hB : ∀ b, b < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) → (B b).map Prod.fst =
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 0 ++
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 1) {I : Nat}
    (hx : ∀ {k1 : Nat} {d1 : D} {e5 e6 : Event}, X.get (g, k1) = some e5 →
      X.get (g, k1 + 1) = some e6 → St Q L X g k1 = some (some (.d (.sm d1))) →
      d1.site = .shfl5 → d1.i < I →
      ExchEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d1 e5 e6) :
    ∀ (k : Nat) (d : D), k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.sm d))) →
      rank d ≤ 2 * I →
      SvInv Q L g (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) B d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hk hσ hr
    rcases pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exact SvInv.init (entFull_entOf Q L g dt)
    · have he' : X.get (g, k0) = some e := he
      have hI0 := sm_inv_at hX hf he' hσ0
      have hr0 : rank d0 ≤ 2 * I := le_trans (rank_mono hn) hr
      by_cases h6 : d0.site = .shfl6
      · rcases pred_sm (by omega) hσ0 with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
        · simp [SmEntry.d0] at h6
        · have hs5 := prev_shfl6 hn1 h6
          have he1' : X.get (g, k1) = some e1 := he1
          have hr1 : rank d1 ≤ 2 * I := le_trans (rank_mono hn1) hr0
          have h1 := ih k1 (by omega) d1 (by omega) hσ1 hr1
          have hI1 := sm_inv_at hX hf he1' hσ1
          have hi1 : d1.i < I := by
            have hl : Late d0.site = true := by rw [h6]; rfl
            have hi : d0.i = d1.i := by
              rcases next_iter hn1 with h | ⟨-, h, -⟩
              · exact h
              · rw [hs5] at h
                simp at h
            unfold rank at hr0
            simp only [hl, ↓reduceIte] at hr0
            omega
          exact SvInv.pair hI1 h1 hs5 hB (hx he1' he' hσ1 hs5 hi1) (hM hg he1' hσ1 hs5) hn1 hn
      · have h0 := ih k0 (by omega) d0 (by omega) hσ0 hr0
        have hv := rowValid_of h0.ent hvr
        have hev := evOk_of hpre hX hf hg he' hσ0 hI0 (fun hs => hS hg hvr he' hσ0 hs)
        exact SvInv.step hI0 hv h0 h6 hev hn

/-! ### The partner's row -/

theorem partner_row : ∀ T < 128, tokOf (T ^^^ 16) = tokOf T ∧ remOf (T ^^^ 16) = remOf T ∧
    Sm.half (T ^^^ 16) = 1 - Sm.half T ∧ row (T ^^^ 16) = row T := by
  decide +kernel

/-- The blocks of a thread's row, from its two halves' visible logits. -/
def blocksOf (Q : Params) (L : Launch) (g : Nat) (b : Nat) : List (ℝ × ℝ) :=
  (halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
      (ProA.cta L g .y * 6 + remOf (g % L.block)) b 0 ++
    halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
      (ProA.cta L g .y * 6 + remOf (g % L.block)) b 1).map (fun z => (z, 0))

theorem blocksOf_fst (Q : Params) (L : Launch) (g b : Nat) :
    (blocksOf Q L g b).map Prod.fst =
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 0 ++
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 1 := by
  unfold blocksOf
  rw [List.map_map]
  exact List.map_id _

/-- **The value facts about the partner lane that the exchange needs**, at the shuffle of the row
maximum of thread `g` (state `d`): the lane `^ 16`'s state at the shuffle of the same iteration
has the thread's entry numbers and running maximum (`Sm.Peer`) and its visible scores are the
other half's. -/
def PeerAt (Q : Params) (L : Launch) (X : Execution) (g : Nat) (d : Sm.D) : Prop :=
  ∀ {x j : Nat} {dp : Sm.D} {ep : Event}, SameWarp L g x → x % L.block = (g % L.block) ^^^ 16 →
    X.get (x, j) = some ep → St Q L X x j = some (some (.d (.sm dp))) → dp.site = .shfl5 →
    dp.i = d.i →
    Sm.Peer d dp ∧ dp.ownScores = Sv.halfScores Q (ProA.cta L g .z)
      (ProA.cta L g .x) (Sm.tokOf (g % L.block))
      (ProA.cta L g .y * 6 + Sm.remOf (g % L.block)) d.i (1 - Sm.half (g % L.block))

/-- **The exchange of one shuffle of the row maximum, from `PeerAt` there.** -/
theorem exchEv_at (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hM : SmMaxOk Q L X) {g k : Nat} {d : Sm.D} {e5 e6 : Event}
    (hg : g < L.threads) (he5 : X.get (g, k) = some e5) (he6 : X.get (g, k + 1) = some e6)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs5 : d.site = .shfl5)
    (hP : PeerAt Q L X g d) :
    Sv.ExchEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d e5 e6 := by
  intro m5 a5 b5 c5 rv o5 m6 a6 b6 c6 recv o6 hk5 hk6
  have hb : L.block = 256 := hpre.block
  -- the thread's own exchange of the row maximum
  obtain ⟨rv0, ok0, he5', hm, hrv0, hall, hσ1⟩ := shfl5_succ hX hf hM hg he5 hσ hs5
  have hrv : rv0 = rv := by
    rw [he5'] at hk5
    exact shflKind_recv hk5
  -- the partner at the shuffle of the same iteration
  obtain ⟨recvB, okB, x, j, dp, heB, hw, hx, hσp, hsitep, hip, hrecvB, -, -, r2, o2, hev2⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := fun d => ownV fun k => (d.stg.fsv k).1) (k := 16)
      (by rw [hs5]; exact shflShape_5 L) hg he5 hσ
  have hsp5 : dp.site = .shfl5 := hsitep.trans hs5
  have hxm : x % L.block = (g % L.block) ^^^ 16 := by rw [hx]; exact src16_mod hb g
  have hsx : x < L.threads := hw.1.2.1
  -- the partner's own exchange received the thread's maximum
  have hr2 : r2 = erealValue .f32 d.ownE := by
    rw [recv_partner hpre hX hf hsx (sameWarp_symm hw) (partner_symm hxm) hσp hsp5 hev2 hσ hs5
      hip.symm he5]
    exact Sm.ownV_fsv hall
  -- the partner's state after its exchange
  obtain ⟨recvD, okD, he2', hmD, hrD, hallp, hσp1⟩ := shfl5_succ hX hf hM hsx hev2 hσp hsp5
  have hmaxW : rv = erealValue .f32 dp.ownE := by
    rw [← hrv, shflEv_recv (he5'.symm.trans heB), hrecvB, Sm.ownV_fsv hallp]
  have hrD2 : recvD = erealValue .f32 d.ownE := (shflEv_recv he2').symm.trans hr2
  -- the thread's exchange of the sum, with the partner at its state after the maximum
  obtain ⟨recvE, okE, x6, j6, dp6, heE, -, hx6, hσ6, hsite6, hi6, hrecvE, -, -, r6, o6', hev6⟩ :=
    sm_shfl_peer_d hpre hX hf hb (fld := fun d => d.stg.sw) (k := 16) (d := d.afterMax rv0)
      (shflShape_6 L) hg he6 hσ1
  have hx6x : x6 = x := by rw [hx6, hx]
  rw [hx6x] at hσ6 hev6
  have hj6 : j6 = j + 1 :=
    sm_shfl_unique hpre hX hf hsx hev6
      (by have := (List.getElem?_eq_some_iff.mp hev2).1; simp only at this; omega)
      hσ6 hσp1 (by rw [hsite6]; rfl) (by rw [hsite6]; rfl) (by rw [hi6]; exact hip)
  subst j6
  have hdp6 : dp6 = dp.afterMax recvD := by
    have := hσ6.symm.trans hσp1
    simp only [Option.some.injEq, TSt.d.injEq, DComp.St.sm.injEq] at this
    exact this
  subst dp6
  have hrecv : recv = recvE := shflKind_recv_eq heE hk6
  have hrecvW : recv = .float .f32 (dp.afterMax (erealValue .f32 d.ownE)).sumP := by
    rw [hrecv, hrecvE, hrD2]; rfl
  obtain ⟨hpeer, hscores⟩ := hP hw hxm hev2 hσp hsp5 hip
  exact ⟨_, hrecvW, dp, ⟨hpeer, hall, hallp, hmaxW, rfl⟩, hscores⟩

/-- **The exchange at every shuffle of the row maximum of an iteration below `I`.** -/
theorem exch_lt (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hM : SmMaxOk Q L X) (hz : Rs.SmBaseZero Q L X)
    (hS : ScorePrem Q L X) :
    ∀ I, ∀ {g k : Nat} {d : D} {e5 e6 : Event}, g < L.threads → ValidRow Q L g →
      X.get (g, k) = some e5 → X.get (g, k + 1) = some e6 →
      St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 → d.i < I →
      ExchEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d e5 e6 := by
  intro I
  induction I with
  | zero => intro g k d e5 e6 _ _ _ _ _ _ h; omega
  | succ I ih =>
    intro g k d e5 e6 hg hvr he5 he6 hσ hs5 hlt
    by_cases hI : d.i < I
    · exact ih hg hvr he5 he6 hσ hs5 hI
    have hiI : d.i = I := by omega
    refine exchEv_at hpre hX hf hM hg he5 he6 hσ hs5 ?_
    intro x j dp ep hw hx hep hσp hsp hip
    have hj : j ≤ (X.tr x).length := event_le hep
    refine ⟨?_, ?_⟩
    · have h := pair_iter hpre hX hf hz d.i hg hw.1.2.1 hw.1.2.2 hx he5 hep hσ hσp hs5 hsp rfl hip
      unfold pf at h
      simp only [Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.1.symm⟩
    -- the partner's visible scores
    have hT : g % L.block < 128 := (sm_inv_at hX hf he5 hσ).tid
    obtain ⟨htok, hrem, hhalf, hrow⟩ := partner_row (g % L.block) hT
    have hcta : ∀ c, ProA.cta L x c = ProA.cta L g c := by
      intro c
      unfold ProA.cta
      rw [hw.1.2.2]
    have hxv : ValidRow Q L x := by
      unfold ValidRow at hvr ⊢
      rw [hx, htok, hrow, hcta]
      exact hvr
    have hxl : x < L.threads := hw.1.2.1
    have hexx : ∀ {k1 : Nat} {d1 : D} {f5 f6 : Event}, X.get (x, k1) = some f5 →
        X.get (x, k1 + 1) = some f6 → St Q L X x k1 = some (some (.d (.sm d1))) →
        d1.site = .shfl5 → d1.i < I →
        ExchEv Q (ProA.cta L x .z) (ProA.cta L x .x) (ProA.cta L x .y) (x % L.block) d1 f5 f6 :=
      fun h1 h2 h3 h4 h5 => ih hxl hxv h1 h2 h3 h4 h5
    have hinv := sv_inv_upto hpre hX hf hM hS hxl hxv (fun b _ => blocksOf_fst Q L x b) hexx j dp hj
      hσp (by unfold rank; rw [hsp]; simp [Late, hip, hiI])
    have hown := hinv.own hsp
    have hfin := own_fin (fun k => dp.stg.fsv k) hown
    refine hfin.trans ?_
    rw [hx, htok, hrem, hhalf, hcta, hcta, hcta, hip]

/-- **`Sv.ExchPrem`**, from the base word and the score premise. -/
theorem exchPrem_full (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hM : SmMaxOk Q L X) (hz : Rs.SmBaseZero Q L X)
    (hS : ScorePrem Q L X) : ExchPrem Q L X where
  exch := fun {_ _ d _ _} hg hvr he5 he6 hσ hs5 =>
    exch_lt hpre hX hf hM hz hS (d.i + 1) hg hvr he5 he6 hσ hs5 (Nat.lt_succ_self _)

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
