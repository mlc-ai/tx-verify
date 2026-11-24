-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SmBw
public import Kernels.InklingRelDecode.Proof.Result.SwStore
public import Kernels.InklingRelDecode.Proof.Result.OutProb
public import Kernels.InklingRelDecode.Proof.Interface.KkBar
public import Kernels.InklingRelDecode.Proof.Interface.FrShfl
public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign
public import Kernels.InklingRelDecode.Proof.Interface.PxLayer

@[expose] public section

/-!
# The factor of a cell that no rescale store covers is 1 (`Rs.OAccPrem.skip`)

`skip_of`: for a cell of `O` in a valid row `r`, column `n`, of CTA `c`, and an iteration `b` with
`1 ≤ b < num_iters`, if no rescale store (`Sr.OSt`) of iteration `b` covers the cell, then
`Out.alphaRow` of the row and iteration is 1. For `b ≥ num_iters` the statement is false
(the development notes, row Vx4), and `OAccPrem.skip` asks for `b < num_iters` only.

The proof follows the softmax thread `t` of row `r` and half `n / 64` of the CTA:

* it reaches `bar20` of iteration `b` (`Kk.sm_reaches_bar20`, a complete execution). The state
  before `bar20` is at `shfl6` of iteration 0, at `waitStO` or at `shfl12` with a true rescale test
  (`prev_bar20`). Iteration 0 is excluded by `1 ≤ b`. At `waitStO` the state before is `stO` of
  iteration `b`, whose store has `OSt` coordinates (`Hs.ost_of`) and covers the cell
  (`Rs.stO_cell`): excluded by the premise.
* At `shfl12` the test is `min W ≥ 1` over the four warps' scratch words (`Lk.p170_value_d`), for
  the words `W r` that the lanes of warp `r` store at `store10` (`Lk.storeWordB`); the loaded word
  is the stored one (`Lk.ldL_value`).
* The word `t`'s warp stores is at most `t`'s own `alpha` (`cm4_le_al`: each of the four butterfly
  steps takes a minimum with the lane's own word), and `t`'s `alpha` is `alphaRow` (`Sv.alr_eq`).
  So `alphaRow ≥ 1`, and a factor of `Softmax.step` that is at least 1 is 1 (`alphaOf_eq_one`:
  otherwise it is `2 ^ a` with `a < -8`, or 0).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Px
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)
open PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
  (Lev lv lval lev_pred lev_reads lev_upto ScratchW Wmin min_ne_top')
open PTX.Kernels.InklingRelDecode.Softmax (Keep pow2)

noncomputable section
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The factor of a step -/

/-- **A factor of `Softmax.step` that is at least 1 is 1**: the factor is 1 where the rescale is
lazy, and otherwise `2 ^ a` with `a < -8` (or 0 for `a = ⊥`). -/
theorem alphaOf_eq_one {sl : ℝ} {blk : List (ℝ × ℝ)} {st : Softmax.St}
    (h : 1 ≤ alphaOf sl blk st) : alphaOf sl blk st = 1 := by
  unfold alphaOf at h ⊢
  split_ifs at h ⊢ with hk
  · rfl
  · exfalso
    set a := Softmax.alphaLog2 sl st.m (max st.m (Softmax.blockMax blk))
    have hlt : a < ((-8 : ℝ) : EReal) := lt_of_not_ge hk
    unfold pow2 at h
    split_ifs at h with hb
    · norm_num at h
    · have htop : a ≠ ⊤ := ne_top_of_lt hlt
      have hr : a.toReal < -8 := by
        have := EReal.coe_toReal htop hb
        rw [← this] at hlt
        exact EReal.coe_lt_coe_iff.mp hlt
      have : (2 : ℝ) ^ a.toReal < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith)
      linarith

/-- `alphaOf_eq_one` for the factor of a row. -/
theorem alphaRow_eq_one {g b r : Nat} (h : 1 ≤ alphaRow Q L g b r) : alphaRow Q L g b r = 1 := by
  unfold alphaRow alphaE at h ⊢
  exact alphaOf_eq_one h

/-! ### The states before `bar20` and `waitStO` -/

/-- **The state before `bar20`**: `shfl6` of iteration 0, `waitStO`, or `shfl12` with a true
rescale test; the iteration is kept. -/
theorem prev_bar20 {g : Nat} {d d' : Sm.D} {e : Event} (hn : Sm.next L g d e = some (some d'))
    (hb : d'.site = .bar20) :
    d'.i = d.i ∧ ((d.site = .shfl6 ∧ d.i = 0) ∨ d.site = .waitStO ∨
      (d.site = .shfl12 ∧ ∃ (m : ShflMode) (a : Value) (b c : Nat) (recv : Value) (ok : Bool),
        e.kind = .shfl m a b c recv ok ∧ d.p170 recv = .ok true)) := by
  have hsite : d.site = .shfl6 ∨ d.site = .shfl12 ∨ d.site = .waitStO := by
    unfold Sm.next at hn
    repeat' split at hn
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (simp_all; done)
      | (simp only [Option.some.injEq] at hn; subst hn; simp_all)
      | (have := Sv.afterSetup_site hn; rcases this with h' | h' <;> simp_all)
  rcases hsite with hs | hs | hs
  · simp only [Sm.next, hs] at hn
    repeat' split at hn
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (simp only [Option.some.injEq] at hn; subst hn; simp [Sm.D.afterSum] at hb)
      | (obtain ⟨h1, -⟩ := Sm.toBar20_rank hn
         refine ⟨by rw [h1]; rfl, .inl ⟨hs, by assumption⟩⟩)
  · obtain ⟨m, a, b, c, r, ok, hk⟩ := Sm.shfl12_kind hn hs
    obtain ⟨hp, -⟩ := (Sm.branchBar20_iff hs hk).mp ⟨d', hn, hb⟩
    simp only [Sm.next, hs, hk, hp, ↓reduceIte] at hn
    exact ⟨(Sm.toBar20_rank hn).1, .inr (.inr ⟨hs, m, a, b, c, r, ok, hk, hp⟩)⟩
  · simp only [Sm.next, hs] at hn
    exact ⟨(Sm.toBar20_rank hn).1, .inr (.inl hs)⟩

/-- **The state before `waitStO`** is at `stO`, with the iteration kept, and the event is a
`tcgen05.st`. -/
theorem prev_waitStO {g : Nat} {d d' : Sm.D} {e : Event} (hn : Sm.next L g d e = some (some d'))
    (hw : d'.site = .waitStO) :
    d.site = .stO ∧ d'.i = d.i ∧ ∃ a vals sh, e.kind = .tc (.st a vals sh) := by
  have hs : d.site = .stO := by
    unfold Sm.next at hn
    repeat' split at hn
    all_goals first
      | (simp only [Option.some.injEq, reduceCtorEq] at hn; done)
      | (simp_all; done)
      | (simp only [Option.some.injEq] at hn; subst hn; simp_all; done)
      | (simp only [Option.some.injEq] at hn; subst hn; simp [Sm.D.afterSum] at hw)
      | (have := Sv.afterSetup_site hn; rcases this with h' | h' <;> simp_all)
      | (have := Sv.toBar20_site hn; simp_all)
  refine ⟨hs, ?_⟩
  simp only [Sm.next, hs] at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    exact ⟨rfl, _, _, _, by assumption⟩
  · cases hn

/-! ### The warp's stored word is at most the lane's `alpha` -/

/-- **The word of level `k` of a lane is at most the lane's `alpha`**: it reads as a number that
is at most `alr` at the lane's state at `shfl7` of the iteration. -/
theorem cm_le_al (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hz : Rs.SmBaseZero Q L X) {c i : Nat} :
    ∀ k, k ≤ 4 → ∀ (y kk : Nat) (d : Sm.D), y < L.threads → y / L.block = c →
      St Q L X y kk = some (some (.d (.sm d))) → d.site = lv k → d.i = i →
      kk ≤ (X.tr y).length → (k = 0 → ∃ e, X.get (y, kk) = some e) →
      ∃ x : EReal, Sm.ReadsAs (lval k d) x ∧ ∃ (p : Nat) (dp : Sm.D),
        St Q L X y p = some (some (.d (.sm dp))) ∧ dp.site = .shfl7 ∧ dp.i = i ∧
        p ≤ (X.tr y).length ∧ x ≤ (dp.stg.alr : EReal)
  | 0, _ => fun y kk d hy hc hσ hs hi hk hev => by
    obtain ⟨e, he⟩ := hev rfl
    obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    have hI : Sm.Inv L y d := hinv.2
    exact ⟨_, hI.four.al, kk, d, hσ, hs, hi, hk, le_rfl⟩
  | k + 1, hk4 => fun y kk d hy hc hσ hs hi hk _ => by
    obtain ⟨p, j, dp, d2, ep, e2, hep, hσp, hpk, hdp, hip, he2, hσ2, hj, hw, hs2, hi2, hmin⟩ :=
      lev_pred hpre hX hf (by omega) hy hσ hs hk
    obtain ⟨xa, hra, q, dq, hσq, hsq, hiq, hqk, hle⟩ :=
      cm_le_al hpre hX hf hz k (by omega) y p dp hy hc hσp hdp (hip.trans hi) hpk
        (fun _ => ⟨ep, hep⟩)
    have H : Lev Q L X c i k := lev_upto hpre hX hf hz c i k (by omega)
    obtain ⟨xb, hxb, hrb⟩ := lev_reads H hw.1.2.1 (hw.1.2.2.symm.trans hc) hσ2 hs2
      (hi2.trans hi) hj (fun _ => ⟨e2, he2⟩)
    have hxa : xa ≠ ⊤ := by
      intro h
      rw [h] at hle
      exact absurd (top_le_iff.mp hle) (EReal.coe_ne_top _)
    have hval : lval (k + 1) d = erealValue .f32 (min xa xb) := by
      rw [Sm.minE_readsAs hra hrb] at hmin
      exact (Except.ok.inj hmin).symm
    refine ⟨min xa xb, ?_, q, dq, hσq, hsq, hiq, hqk, le_trans (min_le_left _ _) hle⟩
    rw [hval]
    exact Sm.ReadsAs.of_erealValue (min_ne_top' hxa)

/-! ### The skip -/

/-- **`Rs.OAccPrem.skip`** for the package's data (`Hs.p0Of`, `Sr.SoftOf`, `Hs.tmOf`), for
`1 ≤ b < num_iters`, in a complete execution. -/
theorem skip_of (hpre : Pre Q L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hcomp : Complete L X) (hbw : Interface.BaseWordRead L X)
    (hR : Interface.RoleReads L X) (hI : ∀ i, Interface.Lk.ScratchIt Q L X i)
    (P : Sv.SvPrem Q L X) :
    ∀ c, c < L.grid → ∀ {g b r n : Nat}, g / L.block = c → 1 ≤ b →
      b < Q.numIters (reqOf L g) (splitOf L g) → QRowValid Q L g r → n < 128 →
      (¬ ∃ (t sk a : Nat) (vals : List Value) (sh : TcShape) (j : Nat),
        X.TSt (t, sk) a vals sh ∧
          Sr.OSt L X c (Hs.p0Of L c) (Sr.SoftOf L c) (Hs.tmOf c) t sk b a vals sh ∧
          j < 64 ∧ oCell c (Hs.tmOf c) r n = tcDataCell L t (.s16x32bx2 64) a j) →
      alphaRow Q L g b r = 1 := by
  intro c hc g b r n hgc hb1 hbn hr hn hno
  have hb256 : L.block = 256 := hpre.block
  have hr60 : r < 60 := hr.1
  set T := r / 16 * 32 + n / 64 * 16 + r % 16 with hTdef
  have hT : T < 128 := by omega
  set t := c * L.block + T with htdef
  have ht : t < L.threads := NamedBar.cta_thread_lt hc (by omega)
  have htm : t % L.block = T := by
    rw [htdef, show c * L.block + T = T + L.block * c by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  have htc : t / L.block = c := by
    rw [htdef, show c * L.block + T = T + L.block * c by ring,
      Nat.add_mul_div_left _ _ (by omega)]
    have : T / L.block = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hrow : Sm.row T = r := by unfold Sm.row; omega
  have hhalf : Sm.half T = n / 64 := by unfold Sm.half; omega
  have hcta : ∀ dim, ProA.cta L t dim = ProA.cta L g dim := by
    intro dim; unfold ProA.cta; rw [htc, hgc]
  have hbn' : b < Q.numIters (ProA.cta L t .z) (ProA.cta L t .x) := by
    rw [hcta, hcta]; exact hbn
  have hD : ∀ c j, Interface.Lk.DecAgree Q L X c j := Interface.Lk.decAgree_every hpre hX hf hI
  have hz : Rs.SmBaseZero Q L X := Rs.smBaseZero hpre hX hf hbw
  obtain ⟨kB, dB, ds, pcB, hσB, hsB, hiB, heB, -⟩ :=
    Interface.Kk.sm_reaches_bar20 hpre hX hf hcomp ht (by rw [htm]; omega) hbn'
  rcases Sv.pred_sm (Interface.event_le heB) hσB with ⟨dt, h⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
  · subst h; simp [SmEntry.d0] at hsB
  have he1' : X.get (t, k1) = some e1 := he1
  obtain ⟨hi1, hcase⟩ := prev_bar20 hn1 hsB
  rcases hcase with ⟨-, hi0⟩ | hsw | ⟨hs12, m, a0, b0, c0, recv, ok, hk, hp⟩
  · omega
  · -- the rescale store of iteration `b` covers the cell
    exfalso
    rcases Sv.pred_sm (Interface.event_le he1') hσ1 with ⟨dt, h⟩ |
      ⟨k2, d2, e2, rfl, he2, hσ2, hn2⟩
    · subst h; simp [SmEntry.d0] at hsw
    obtain ⟨hs2, hi2, a, vals, sh, hk2⟩ := prev_waitStO hn2 hsw
    obtain ⟨pc2, kd2⟩ := e2
    simp only at hk2
    subst hk2
    have hget : X.get (t, k2) = some ⟨pc2, .tc (.st a vals sh)⟩ := he2
    obtain ⟨d3, hσ3, hcs⟩ := Interface.Lk.tcst_event hX hf ht hget
    have hd3 : d3 = d2 := by
      have := hσ3.symm.trans hσ2
      simp only [Option.some.injEq, Interface.TSt.d.injEq, DComp.St.sm.injEq] at this
      exact this
    subst hd3
    rcases hcs with ⟨hs3, -⟩ | ⟨-, ha, hsh, hl⟩
    · rw [hs2] at hs3; cases hs3
    have hO := Hs.ost_of hpre hX hf hbw (Hs.stRdv_of hpre hX hf hD c) hget htc hσ2 hs2 ha hsh hl
    have hbi : d3.i = b := by omega
    rw [hbi] at hO
    have htm0 : d3.e.tm = 0 := Interface.smBaseZero_of hpre hX hf hbw ht hσ2
    refine hno ⟨t, k2, a, vals, sh, n % 64, ⟨pc2, hget⟩, hO, Nat.mod_lt _ (by omega), ?_⟩
    have hdef : t % L.block < 128 := by rw [htm]; exact hT
    rw [ha, Sm.oAddr_eq hdef (by rw [htm0]; norm_num)
        (Interface.sm_bw' hpre hX hf ht hσ2 (by rw [hs2]; trivial)), htm0,
      Rs.stO_cell L t (tm := 0) (by norm_num) (n % 64), htm, htc, hrow, hhalf]
    unfold Hs.tmOf
    congr 1
    omega
  · -- the rescale test is true: the minimum of the warps' words is at least 1
    have hU := Interface.Lk.storeWordB hpre hX hf hz c b
    let W : Nat → EReal := fun q => if h : q < 4 then Classical.choose (hU q h) else 0
    have hWt : ∀ q, W q ≠ ⊤ := by
      intro q
      by_cases h : q < 4
      · simp only [W, h, ↓reduceDIte]
        exact (Classical.choose_spec (hU q h)).1
      · simp only [W, h, ↓reduceDIte]
        exact EReal.zero_ne_top
    have hWs : ∀ {q : Nat} (h : q < 4), ∀ {y k : Nat} {d : Sm.D}, y < L.threads →
        y / L.block = c → y % L.block / 32 = q → St Q L X y k = some (some (.d (.sm d))) →
        d.site = .store10 → d.i = b → d.stg.cm4 = erealValue .f32 (W q) := by
      intro q h y k d hy hyc hyq hσ hs hi
      have : W q = Classical.choose (hU q h) := by simp only [W, h]; rfl
      rw [this]
      exact (Classical.choose_spec (hU q h)).2 hy hyc hyq hσ hs hi
    have hScr : ScratchW Q L X c b W := by
      intro y k d hy hyc hσ hs hi
      have hq : y % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
      obtain ⟨k', hk', hσ'⟩ := Interface.Lk.st_norm hσ
      rw [Interface.Lk.ldL_value hpre hX hf hR (Interface.B0N.b0At_of hpre hX hf
        (fun j _ => hD c j)) (fun j _ => Interface.B0N.b0Pos_of hpre hX hf
        (fun j' _ => hD c j')) hq (hWs hq) hy hyc rfl hk' hσ' hs hi]
      exact Sm.ReadsAs.of_erealValue (hWt _)
    obtain ⟨recv', ok', hev, hp'⟩ := Interface.Lk.p170_value_d hpre hX hf hb256 hWt hScr ht htc
      he1' hσ1 hs12 (by omega)
    have hrr : recv = recv' := by
      rw [hev] at hk
      simp only [Kind.shfl.injEq] at hk
      exact hk.2.2.2.2.1.symm
    subst hrr
    have h1 : Sm.ReadsAs (b32 1065353216) ((1 : ℝ) : EReal) :=
      readEReal_of_valFloat Sm.valFloat_b32_one'
    have hmin : (1 : EReal) ≤ Wmin W := by
      have h0 : Sm.ReadsAs (erealValue .f32 (Wmin W)) (Wmin W) :=
        Sm.ReadsAs.of_erealValue (min_ne_top' (min_ne_top' (hWt 0)))
      rw [hp', Interface.Lk.setpE_readsAs (Or.inr rfl) h0 h1] at hp
      have := Except.ok.inj hp
      simpa [erealCompare] using this
    -- back from `shfl12` to `store10` of the iteration
    have hk1 : k1 ≤ (X.tr t).length := Interface.event_le he1'
    rcases Sv.pred_sm hk1 hσ1 with ⟨dt, h⟩ | ⟨k2, d2, e2, rfl, -, hσ2, hn2⟩
    · subst h; simp [SmEntry.d0] at hs12
    have hs2 : d2.site = .shfl11 := Interface.Lk.prev_shfl12 hn2 hs12
    have hi2 : d1.i = d2.i := (Interface.Lk.shfl11_succ_i hn2 hs2)
    rcases Sv.pred_sm (by omega) hσ2 with ⟨dt, h⟩ | ⟨k3, d3, e3, rfl, -, hσ3, hn3⟩
    · subst h; simp [SmEntry.d0] at hs2
    obtain ⟨hs3, hi3⟩ := Sm.prev_shfl11 hn3 hs2
    rcases Sv.pred_sm (by omega) hσ3 with ⟨dt, h⟩ | ⟨k4, d4, e4, rfl, -, hσ4, hn4⟩
    · subst h; simp [SmEntry.d0] at hs3
    obtain ⟨hs4, hi4⟩ := Sm.prev_ldL hn4 hs3
    rcases Sv.pred_sm (by omega) hσ4 with ⟨dt, h⟩ | ⟨k5, d5, e5, rfl, -, hσ5, hn5⟩
    · subst h; simp [SmEntry.d0] at hs4
    obtain ⟨hs5, hi5⟩ := Sm.prev_bar23 hn5 hs4
    have hib : d5.i = b := by omega
    have hq : T / 32 < 4 := by omega
    have hcm := hWs hq ht htc (by rw [htm]) hσ5 hs5 hib
    obtain ⟨x, hx, p, dp, hσp, hsp, hip, hpk, hle⟩ :=
      cm_le_al hpre hX hf hz (c := c) (i := b) 4 le_rfl t k5 d5 ht htc hσ5 hs5 hib (by omega)
        (fun h => absurd h (by decide))
    have hxW : x = W (T / 32) := by
      have : lval 4 d5 = d5.stg.cm4 := rfl
      rw [this, hcm] at hx
      exact Sm.ReadsAs.unique hx (Sm.ReadsAs.of_erealValue (hWt _))
    have hWle : Wmin W ≤ W (T / 32) := by
      unfold Wmin
      have : T / 32 = 0 ∨ T / 32 = 1 ∨ T / 32 = 2 ∨ T / 32 = 3 := by omega
      rcases this with h | h | h | h <;> rw [h]
      · exact le_trans (min_le_left _ _) (min_le_left _ _)
      · exact le_trans (min_le_left _ _) (min_le_right _ _)
      · exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hvr : Sv.ValidRow Q L t := by
      refine ⟨by rw [htm, hrow]; exact hr60, ?_⟩
      rw [htm, ← Sv.row_div6, hrow, hcta]
      exact hr.2
    have hal := Sv.alr_eq hpre hX hf P ht hvr hpk hσp (by rw [hsp]; trivial)
    rw [hal, hip, htm, hrow] at hle
    have hrowEq : alphaRow Q L t b r = alphaRow Q L g b r := by
      unfold alphaRow reqOf splitOf kvhOf
      rw [hcta, hcta, hcta]
    rw [hrowEq] at hle
    apply alphaRow_eq_one
    have h2 : (1 : EReal) ≤ (alphaRow Q L g b r : EReal) :=
      le_trans hmin (le_trans hWle (hxW ▸ hle))
    exact_mod_cast h2

end
end PTX.Kernels.InklingRelDecode.Proof.Px
