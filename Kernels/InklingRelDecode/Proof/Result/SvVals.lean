-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Result.SvScoreLoad

@[expose] public section

/-!
# The softmax region's rescale factor and stored probabilities are the specification's

From the iteration invariant (`Sv.sv_inv_at`) at a state of a valid row's thread:

* `alr_eq`: at the stage's sites (the rescale load and store among them) the number `alpha` the
  stage left (`D.stg.alr`, the factor the rescale multiplies the loaded `O` words by) is
  `Out.alphaRow` of the thread's tile row and iteration: `Softmax.step`'s `alpha`;
* `pf_eq`: from the stage's two shuffles to the arrival on `p_ready`, the 64 probabilities the
  thread holds (`D.pf`, the numbers the `P` store packs into `bf16` pairs) are `Out.pElemE` of the
  thread's tile row, iteration and key column `64 · half + k`: `2 ^ (sl · logit - m_use · sl)` for a
  visible key, `0` for a masked one.

Both are for the iteration `d.i` of the state; the premises are `Sv.SvPrem` and a valid row.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Result.Out
open PTX.Kernels.InklingRelDecode.Proof.Result.Mma
  (reqOf splitOf kvhOf blockOf alphaOf mUseOf before)
open PTX.Kernels.InklingRelDecode.Proof.Interface (St ThreadFacts)

noncomputable section
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The blocks of the thread's row, with every value `0`, in `blocks0`'s terms. -/
def blkRow (Q : Params) (L : Launch) (g : Nat) : Nat → List (ℝ × ℝ) :=
  blk Q (ProA.cta L g .z) (ProA.cta L g .x) (Sm.tokOf (g % L.block))
    (ProA.cta L g .y * 6 + Sm.remOf (g % L.block)) (fun _ _ => 0)

/-- **The invariant at every softmax state of a valid row's thread**, for `blkRow`. -/
theorem svInv_row (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (hg : g < L.threads) (hvr : ValidRow Q L g)
    {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) :
    SvInv Q L g (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (blkRow Q L g) d :=
  sv_inv_at hpre hX hf P hg hvr (B := blkRow Q L g)
    (fun b _ => blk_fst_halves Q _ _ _ _ _ b) k d hk hσ

theorem row_head (L : Launch) (g : Nat) :
    group * kvhOf L g + Sm.row (g % L.block) % 6 =
      ProA.cta L g .y * 6 + Sm.remOf (g % L.block) := by
  unfold group kvhOf
  rw [row_mod6]
  omega

/-- **The rescale factor the stage leaves is `Softmax.step`'s `alpha`** (`Out.alphaRow`): at the
stage's sites of iteration `d.i` of a valid row's thread. -/
theorem alr_eq (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (hg : g < L.threads) (hvr : ValidRow Q L g)
    {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : StageSite d.site) :
    d.stg.alr = alphaRow Q L g d.i (Sm.row (g % L.block)) := by
  have h := (svInv_row hpre hX hf P hg hvr hk hσ).stage hs
  rw [h.alr]
  unfold alphaRow alphaE alphaOf before blkRow
  rw [row_div6, row_head]
  rfl

/-- **The probabilities the thread stores are `Out.pElemE`.** -/
theorem pf_eq (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (hg : g < L.threads) (hvr : ValidRow Q L g)
    {k : Nat} {d : Sm.D} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : PfSite d.site) :
    ∀ c < 64, d.pf c =
      pElemE Q L g (Sm.row (g % L.block)) d.i (64 * Sm.half (g % L.block) + c) := by
  intro c hc
  have h := (svInv_row hpre hX hf P hg hvr hk hσ).pf hs c hc
  rw [h]
  unfold pElemE probE muE mUseOf before blkRow
  rw [row_div6, row_head]
  have hkey : keyB Q (ProA.cta L g .x) d.i (Sm.half (g % L.block)) c =
      key Q (splitOf L g) d.i (64 * Sm.half (g % L.block) + c) := by
    unfold splitOf keyB key
    omega
  have hv : visB Q (ProA.cta L g .z) (ProA.cta L g .x) (Sm.tokOf (g % L.block)) d.i
      (Sm.half (g % L.block)) c ↔
      Vis Q (reqOf L g) (splitOf L g) (Sm.tokOf (g % L.block)) d.i
        (64 * Sm.half (g % L.block) + c) := by
    unfold visB Vis
    rw [hkey]
    rfl
  by_cases hV : Vis Q (reqOf L g) (splitOf L g) (Sm.tokOf (g % L.block)) d.i
      (64 * Sm.half (g % L.block) + c)
  · simp only [hV, hv.mpr hV, ↓reduceIte]
    congr 1
    unfold logitB logit muStage slQ sl
    rw [hkey]
    rfl
  · simp only [hV, mt hv.mp hV, ↓reduceIte]

/-- **The words of the `P` store are the `bf16` pairs of the exact probabilities.** The thread's
`tcgen05.st` of iteration `d.i` stores 32 words, word `w` the pair of `bf16` numbers of the key
columns `64 · half + 2 w` and `64 · half + 2 w + 1` (`Out.pElemE`: `Softmax.step`'s `p_k` on a
visible key, `0` on a masked one). -/
theorem pstore_words (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (hre : Interface.Lk.SmReal Q L X)
    (hg : g < L.threads) (hvr : ValidRow Q L g)
    {k pc a : Nat} {d : Sm.D} {vals : List Value} {sh : TcShape} (hk : k ≤ (X.tr g).length)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .tmemSt)
    (he : X.get (g, k) = some ⟨pc, .tc (.st a vals sh)⟩) :
    a = Sm.tileAddr L g d ∧ sh = .s16x32bx2 32 ∧ vals.length = 32 ∧
      ∀ w < 32, vals[w]? = some (.pair
        (.float .bf16 (pElemE Q L g (Sm.row (g % L.block)) d.i
          (64 * Sm.half (g % L.block) + 2 * w)))
        (.float .bf16 (pElemE Q L g (Sm.row (g % L.block)) d.i
          (64 * Sm.half (g % L.block) + (2 * w + 1))))) := by
  obtain ⟨u, hF⟩ := Interface.fired_cont hX hf hg he hσ (by simp [Interface.ExitState])
  obtain ⟨vals', hl, hw, -, hev⟩ := Sm.shape_tmemSt (Interface.fired_sm hF) hs
  simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.st.injEq] at hev
  obtain ⟨-, ha, hv, hsh⟩ := hev
  subst ha hv hsh
  refine ⟨rfl, rfl, hl, ?_⟩
  intro w hw'
  have hR : Sm.RealSt d.stg d.m d.pf := by
    obtain ⟨t0, ins0, o0, -, hinv0, -, -⟩ := Frame.fired_site hf.sound hX he hσ
    exact hinv0.2.re (hre hσ)
  rw [hw w hw', Sm.pwV_real hR.pv]
  have hp := pf_eq hpre hX hf P hg hvr hk hσ (Or.inr (by simp [PostSite, hs])) (2 * w) (by omega)
  have hp' := pf_eq hpre hX hf P hg hvr hk hσ (Or.inr (by simp [PostSite, hs])) (2 * w + 1)
    (by omega)
  simp only [Sm.D.pw, hp, hp']

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
