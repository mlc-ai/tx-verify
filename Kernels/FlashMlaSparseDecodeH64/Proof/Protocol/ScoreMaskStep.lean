-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MaskReadback
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreTracking
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSources
import Lemmas.Tcgen05.TcDataCell
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

/-! # The softmax mask successor from the actual QK results -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreMaskStep

open PTX PTX.Flow GemmRing

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Only the values written to the score cells by this block's actual final QK issue need to
be supplied. Their representation and their attribution to the actual loads follow separately. -/
def QkScoreValues (P : Params) (L : Launch) (X : Execution)
    (cta issuer block : Nat) (lane : Fin 128) : Prop :=
  ∀ (part : Fin 2) (reg : Fin 32) (src : Nat),
    Frame.stateAt (Machine.code P L) X issuer src =
      some (some (.mma ⟨.qkMma 15, block⟩)) →
    X.MmaIssue (issuer, src) Wg1Mma.tmemP (MmaDataTrace.qkOperands L issuer block 15)
      (MmaDataTrace.qkAccum 15) [0, 0, 0, 0] →
    ∃ value, TcMma.Result L Assumptions.all X (issuer, src)
      (tcDataCell L (softmax L cta lane) .s32x32b (Wg0.scoreLoadColumn part) reg.val) value

private theorem score_column_ge {g : Nat} (part : Fin 2) (reg : Fin 32) :
    400 ≤ (tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val).column := by
  rw [tcDataCell_s32x32b]
  have hBase : Wg0.scoreLoadColumn part < 2 ^ 16 := by
    have := part.isLt
    unfold Wg0.scoreLoadColumn
    omega
  change 400 ≤ Wg0.scoreLoadColumn part % 2 ^ 16 + reg.val
  rw [Nat.mod_eq_of_lt hBase]
  unfold Wg0.scoreLoadColumn
  omega

variable {cta issuer j : Nat} {lane : Fin 128} {d : Wg0.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (hmma : MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (softmax L cta lane) j = some (some (.wg0 d)))
    (hsite : d.site = .maskRead) (hlen : j ≤ (X.tr (softmax L cta lane)).length)
include hpre hX hs hmma hd hsite hlen

private theorem loaded_fp32_sources (hvalues : QkScoreValues P L X cta issuer d.block lane) :
    let g := softmax L cta lane
    let arm : Fin 2 := ⟨Wg0.arm L g, Wg0.armLt L g⟩
    ∃ i lo hi,
      Wg0.ScoreLoadVisit P L X g (i + 1) d.block arm 0 lo ∧
      Wg0.ScoreLoadVisit P L X g (i + 2) d.block arm 1 hi ∧
      ((d.ownScores, d.peerScores) = if Wg0.arm L g = 0 then (lo, hi) else (hi, lo)) ∧
      ∀ (k : Fin 2) (reg : Fin 32), ∃ (src : EvId) (score : ℝ),
        let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn k) reg.val
        TcMma.ReadSource L X .ld src (g, i + 1 + k.val) cell ∧
        TcMma.Result L Assumptions.all X src cell (.float .f32 score) := by
  let g := softmax L cta lane
  obtain ⟨w, _, entry, _, _, _, _, hw, _, _, _, _, hentry, heSite, _, _, _, _, _⟩ :=
    Wg0ScoreEventHistory.waits_of_mask hpre hX hs hd hsite hlen
  have hlen' : w + 1 + 5 ≤ (X.tr g).length := by
    rw [← hw] at hlen
    exact hlen
  have hstate : Frame.stateAt (Machine.code P L) X g (w + 1 + 5) = some (some (.wg0 d)) := by
    rw [← hw] at hd
    exact hd
  obtain ⟨lo, hi, _, _, hlo, hhi, hwords⟩ :=
    Wg0.maskRead_score_history hpre hX hs hentry heSite hstate hlen'
  refine ⟨w + 1, lo, hi, hlo, hhi, hwords, ?_⟩
  intro k reg
  let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn k) reg.val
  obtain ⟨src, ld, _, hIndex, hSrcState, _, hIssue, _, hRead⟩ :=
    ScoreLifetime.final_qk_score_read_source_at hpre hX hs hmma hd hsite hlen k reg
  have hk := k.isLt
  have hld : ld = w + 1 + 1 + k.val := by omega
  obtain ⟨value, hresult⟩ := hvalues k reg src hSrcState hIssue
  have hIssuer := Frame.lt_of_get hX hIssue.choose_spec
  obtain ⟨score, _, hFp32⟩ :=
    Wg0ScoreSources.score_writer_f32 hpre hX (hs issuer hIssuer) hSrcState
      (show 400 ≤ cell.column from score_column_ge k reg) (.inl hresult)
  rw [hld] at hRead
  exact ⟨(issuer, src), score, hRead, hFp32⟩


/-- Replay both score loads and use their actual per-cell writers to close the FP32 guard. -/
theorem exchange_ready_of_qk_values (hvalues : QkScoreValues P L X cta issuer d.block lane)
    : Wg0.exchangeReady d = true := by
  obtain ⟨_, _, _, hlo, hhi, hwords, hsources⟩ :=
    loaded_fp32_sources hpre hX hs hmma hd hsite hlen hvalues
  exact Wg0.exchangeReady_of_score_sources hX hlo hhi hwords hsources

omit hpre hX hs hmma hd hsite hlen in
private theorem loaded_value {g ld block : Nat} {a k : Fin 2} {words : List Value}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hv : Wg0.ScoreLoadVisit P L X g ld block a k words)
    (hsource : ∀ reg : Fin 32, ∃ (src : EvId) (score : ℝ),
      let cell := tcDataCell L g .s32x32b (Wg0.scoreLoadColumn k) reg.val
      TcMma.ReadSource L X .ld src (g, ld) cell ∧
      TcMma.Result L Assumptions.all X src cell (.float .f32 score)) :
    ∀ j < 32, ∃ score : ℝ, words.getD j (PTX.Proof.b32 0) = .float .f32 score := by
  obtain ⟨_, _, _, _, hload, hlen⟩ := hv
  intro j hj
  obtain ⟨src, score, hread, hval⟩ := hsource ⟨j, hj⟩
  have hcell : TcMma.LoadCell L X (g, ld) j
      (tcDataCell L g .s32x32b (Wg0.scoreLoadColumn k) j) :=
    ⟨_, _, _, hload, by rwa [hlen], rfl⟩
  have hw := TcMma.LoadReadOk.f32 hX.tcRead.1 hload hcell hread (.inl hval)
  exact ⟨score, by rw [List.getD_eq_getElem?_getD, hw]; rfl⟩

/-- The two recorded lists contain real FP32 values for each of the 32 own and peer entries. -/
theorem real_scores_of_qk_values (hvalues : QkScoreValues P L X cta issuer d.block lane) :
    (∀ k < 32, ∃ x : ℝ, d.ownScores.getD k (PTX.Proof.b32 0) = .float .f32 x) ∧
    (∀ k < 32, ∃ x : ℝ, d.peerScores.getD k (PTX.Proof.b32 0) = .float .f32 x) := by
  obtain ⟨_, lo, hi, hlo, hhi, hwords, hsource⟩ :=
    loaded_fp32_sources hpre hX hs hmma hd hsite hlen hvalues
  have hLo := loaded_value hX hlo (hsource 0)
  have hHi := loaded_value hX hhi (hsource 1)
  by_cases har : Wg0.arm L (softmax L cta lane) = 0
  · rw [ite_eq_left har, Prod.mk.injEq] at hwords
    rw [hwords.1, hwords.2]
    exact ⟨hLo, hHi⟩
  · rw [ite_eq_right har, Prod.mk.injEq] at hwords
    rw [hwords.1, hwords.2]
    exact ⟨hHi, hLo⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreMaskStep
