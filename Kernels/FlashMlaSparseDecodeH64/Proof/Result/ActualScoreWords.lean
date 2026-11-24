-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualQkBlock
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.ScoreLifetime
import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreLoads
import Lemmas.Tcgen05.TcMmaRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreTracking

@[expose] public section

/-! # The actual WG0 score words before exchanging their second half -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.Proof Protocol MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem words_of_load {i : EvId} {col : Nat} {words pieces : List Value}
    (hw : X.TLd i col words .s32x32b) (hp : X.TLd i col pieces .s32x32b) :
    words = pieces := by
  obtain ⟨_, he⟩ := hw
  obtain ⟨_, hf⟩ := hp
  have hk := congrArg Event.kind (Option.some.inj (he.symm.trans hf))
  cases hk
  rfl

/-- An actual score word at the mask boundary is the matching datapath half of the
logical dot product. The two halves are attributed to the same final QK issuer and block. -/
theorem qk_word_of_mask {cta issuer j : Nat} {lane : Fin 128} {out : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X cta issuer)
    (hd : Frame.stateAt (Machine.code P L) X (GemmRing.softmax L cta lane) j =
      some (some (.wg0 out))) (hsite : out.site = .maskRead)
    (hlen : j ≤ (X.tr (GemmRing.softmax L cta lane)).length)
    (part : Fin 2) (reg : Fin 32) :
    let g := GemmRing.softmax L cta lane
    let words := if part.val = Wg0.arm L g then out.ownScores else out.peerScores
    let head : Fin 64 := ⟨lane.val % 64, by omega⟩
    let slot : Fin 64 := ⟨32 * part.val + reg.val, by omega⟩
    ∃ src lo hi,
      Frame.stateAt (Machine.code P L) X issuer src =
        some (some (.mma ⟨.qkMma 15, out.block⟩)) ∧
      TcMma.Result L Assumptions.all X (issuer, src)
        ⟨cta, lane.val % 64, Wg1Mma.tmemP + (32 * part.val + reg.val)⟩ (.float .f32 lo) ∧
      TcMma.Result L Assumptions.all X (issuer, src)
        ⟨cta, lane.val % 64 + 64, Wg1Mma.tmemP + (32 * part.val + reg.val)⟩ (.float .f32 hi) ∧
      words[reg.val]? = some (.float .f32 (if lane.val < 64 then lo else hi)) ∧
      lo + hi = blockDot P L issuer (lane.val % 64) (32 * part.val + reg.val)
        (Wg2.gatheredByte P L issuer out.block) ∧
      lo = blockHalfDot P L issuer head slot 0 (Wg2.gatheredByte P L issuer out.block) ∧
      hi = blockHalfDot P L issuer head slot 1 (Wg2.gatheredByte P L issuer out.block) := by
  dsimp only
  let g := GemmRing.softmax L cta lane
  have hCta : ctaOf L g = cta := by
    have := lane.isLt
    simp only [g, GemmRing.softmax, ctaOf, hpre.block]
    omega
  have hTid : tidOf L g = lane.val := by
    have := lane.isLt
    simp only [g, GemmRing.softmax, tidOf_eq hpre, hpre.block]
    omega
  let head : Fin 64 := ⟨lane.val % 64, by omega⟩
  let slot : Fin 64 := ⟨32 * part.val + reg.val, by
    have := part.isLt
    have := reg.isLt
    omega⟩
  obtain ⟨src, ld, words, hLd, hState, hLoad, hIssue, hCell, hSource⟩ :=
    ScoreLifetime.final_qk_score_read_source_at hpre hX hs hmma hd hsite hlen part reg
  obtain ⟨lo, hi, hLo, hHi, hSum, hLower, hHigher⟩ :=
    qk_pair_for_mask hpre hX hs hmma hd hsite hlen hState hIssue head slot
  have hCellLoc : tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val =
      ⟨cta, lane.val, Wg1Mma.tmemP + slot.val⟩ := by
    rw [scoreLoad_cell hpre (g := g) (by rw [hTid]; exact lane.isLt), hTid]
    exact congrArg (fun c => (⟨c, lane.val, Wg1Mma.tmemP + slot.val⟩ : TcMma.Cell)) hCta
  have hVal : TcMma.Result L Assumptions.all X (issuer, src)
      (tcDataCell L g .s32x32b (Wg0.scoreLoadColumn part) reg.val)
      (.float .f32 (if lane.val < 64 then lo else hi)) := by
    rw [hCellLoc]
    by_cases h : lane.val < 64
    · have he : head.val = lane.val := Nat.mod_eq_of_lt h
      rw [he] at hLo
      simpa only [ite_eq_left h] using hLo
    · have he : head.val + 64 = lane.val := by
        have := lane.isLt
        dsimp [head]
        omega
      rw [he] at hHi
      simpa only [ite_eq_right h] using hHi
  have hWord := TcMma.LoadReadOk.f32 hX.tcRead.1 hLoad hCell hSource (.inl hVal)
  have hWords : (if part.val = Wg0.arm L g then out.ownScores else out.peerScores) = words := by
    obtain ⟨w, _, entry, _, _, _, _, hw, _, _, _, _, hEntry, hEntrySite, _, _, _, _, _⟩ :=
      Wg0ScoreEventHistory.waits_of_mask hpre hX hs hd hsite hlen
    have hmask : Frame.stateAt (Machine.code P L) X g (w + 1 + 5) = some (some (.wg0 out)) := by
      rw [← hw] at hd
      exact hd
    have hlen' : w + 1 + 5 ≤ (X.tr g).length := by
      rw [← hw] at hlen
      exact hlen
    obtain ⟨lower, upper, _, _, hlo, hhi, hList⟩ :=
      Wg0.maskRead_score_history hpre hX hs hEntry hEntrySite hmask hlen'
    change (out.ownScores, out.peerScores) =
      (if Wg0.arm L g = 0 then (lower, upper) else (upper, lower)) at hList
    change (if part.val = Wg0.arm L g then out.ownScores else out.peerScores) = words
    have har := Wg0.armLt L g
    have hArm : Wg0.arm L g = 0 ∨ Wg0.arm L g = 1 := by omega
    have hPart : part = 0 ∨ part = 1 := by
      have hp := part.isLt
      rcases (show part.val = 0 ∨ part.val = 1 by omega) with h | h
      · exact .inl (Fin.ext h)
      · exact .inr (Fin.ext h)
    rw [← hw] at hLd
    rcases hPart with rfl | rfl
    · have hpos : ld = w + 1 + 1 := by
        change ld + 4 = w + 6 at hLd
        omega
      rw [hpos] at hLoad
      rw [words_of_load hLoad hlo.choose_spec.2.2.2.1]
      rcases hArm with h | h
      · simp [h] at hList ⊢
        exact hList.1
      · simp [h] at hList ⊢
        exact hList.2
    · have hpos : ld = w + 1 + 2 := by
        change ld + 3 = w + 6 at hLd
        omega
      rw [hpos] at hLoad
      rw [words_of_load hLoad hhi.choose_spec.2.2.2.1]
      rcases hArm with h | h
      · simp [h] at hList ⊢
        exact hList.2
      · simp [h] at hList ⊢
        exact hList.1
  exact ⟨src, lo, hi, hState, hLo, hHi, by rw [hWords]; exact hWord, hSum, hLower, hHigher⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
