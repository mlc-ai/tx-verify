-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualMaskWord
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.ActualScoreWords
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.GemmScoreMask
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ScoreSumsHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerWordsHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Wg0PeerReadback

@[expose] public section

/-! # Actual softmax score pairs are the validity-masked logical QK scores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow PTX.Proof Protocol Wg0 MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem arm_eq_half {g : Nat} (hw : warpOf L g < 4) :
    Wg0.arm L g = Wg0.half L g := by
  unfold Wg0.arm Wg0.half
  split_ifs <;> omega

theorem partner_coordinates {g : Nat} (hpre : Pre P L mem0)
    (hw : warpOf L g < 4) :
    let partner := Wg0PeerSources.partner L g
    ctaOf L partner = ctaOf L g ∧ Wg0.head L partner = Wg0.head L g ∧
      Wg0.half L partner = 1 - Wg0.half L g ∧ warpOf L partner < 4 := by
  let mate := Wg0PeerSources.partner L g
  let w := warpOf L g
  let l := laneOf L g
  let t := 32 * (w ^^^ 2) + l
  have hXor : ∀ k : Fin 4, (k.val ^^^ 2) < 4 ∧
      (k.val ^^^ 2) = if k.val < 2 then k.val + 2 else k.val - 2 := by decide
  obtain ⟨hW, hx⟩ := hXor ⟨w, hw⟩
  change w ^^^ 2 < 4 at hW
  change w ^^^ 2 = (if w < 2 then w + 2 else w - 2) at hx
  have hl : l < 32 := Nat.mod_lt _ (by decide)
  have ht : t < 384 := by dsimp [t]; omega
  have hCta : ctaOf L mate = ctaOf L g := by
    change (ctaOf L g * L.block + t) / L.block = _
    rw [hpre.block]
    omega
  have hTid : tidOf L mate = t := by
    rw [tidOf_eq hpre]
    change (ctaOf L g * L.block + t) % 384 = _
    rw [hpre.block]
    omega
  have hTidOwn : tidOf L g = 32 * w + l := by
    dsimp [w, l, warpOf, laneOf]
    omega
  have hWarp : warpOf L mate = w ^^^ 2 := by
    change tidOf L mate / 32 = _
    rw [hTid]
    dsimp [t]
    omega
  refine ⟨hCta, ?_, ?_, hWarp ▸ hW⟩
  · change tidOf L mate % 64 = tidOf L g % 64
    rw [hTid, hTidOwn]
    dsimp [t]
    split_ifs at hx <;> omega
  · change warpOf L mate / 2 = 1 - w / 2
    rw [hWarp]
    split_ifs at hx <;> omega

private theorem score_word_at_exchange {g i issuer : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hg : g < L.threads)
    (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : ScoreExchangeSite d.site) (part : Fin 2) (reg : Fin 32) :
    let half : Fin 2 := ⟨Wg0.half L g % 2, Nat.mod_lt _ (by decide)⟩
    let head : Fin 64 := ⟨Wg0.head L g, Wg0.head_lt _ _⟩
    let slot : Fin 64 := ⟨32 * part.val + reg.val, by omega⟩
    (if part.val = Wg0.arm L g then d.ownScores else d.peerScores).getD reg.val (b32 0) =
      .float .f32
        (blockHalfDot P L issuer head slot half (Wg2.gatheredByte P L issuer d.block)) := by
  have hG : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hd
  obtain ⟨lane, hLane⟩ := GemmRing.softmax_thread hpre (cta := ctaOf L g) rfl hG
  have hTid : tidOf L g = lane.val := by
    have h := lane.isLt
    rw [hLane, tidOf_eq hpre]
    simp only [GemmRing.softmax, hpre.block]
    omega
  obtain ⟨j, q, hj, hq, hMask, hSame, hOwn, hPeer⟩ :=
    Wg0.mask_words_before_exchange hi hd hsite
  have hjLen : j ≤ (X.tr g).length := by omega
  rw [hLane] at hq hjLen
  obtain ⟨_, lo, hi, _, _, _, hWord, _, hLo, hHi⟩ :=
    qk_word_of_mask hpre hX hs hmma hq hMask hjLen part reg
  rw [← hLane] at hWord
  let head : Fin 64 := ⟨Wg0.head L g, Wg0.head_lt _ _⟩
  let slot : Fin 64 := ⟨32 * part.val + reg.val, by omega⟩
  let half : Fin 2 := ⟨Wg0.half L g % 2, Nat.mod_lt _ (by decide)⟩
  have hHead : (⟨lane.val % 64, by omega⟩ : Fin 64) = head := by
    apply Fin.ext
    change lane.val % 64 = tidOf L g % 64
    rw [hTid]
  have hLo' : lo = blockHalfDot P L issuer head slot 0 (Wg2.gatheredByte P L issuer d.block) :=
    by rw [← hHead, hSame]; exact hLo
  have hHi' : hi = blockHalfDot P L issuer head slot 1 (Wg2.gatheredByte P L issuer d.block) :=
    by rw [← hHead, hSame]; exact hHi
  change (if part.val = Wg0.arm L g then d.ownScores else d.peerScores).getD reg.val (b32 0) =
    .float .f32 (blockHalfDot P L issuer head slot half (Wg2.gatheredByte P L issuer d.block))
  rw [hOwn, hPeer, List.getD, hWord]
  have hHalf : Wg0.half L g = lane.val / 64 := by
    change tidOf L g / 32 / 2 = _
    rw [hTid]
    omega
  by_cases h : lane.val < 64
  · have he : half = 0 := Fin.ext (by dsimp [half]; rw [hHalf]; omega)
    rw [ite_eq_left h, hLo', he]
    rfl
  · have hl := lane.isLt
    have he : half = 1 := Fin.ext (by dsimp [half]; rw [hHalf]; omega)
    rw [ite_eq_right h, hHi', he]
    rfl

private theorem actual_score_pair_from_history {g i issuer : Nat} {d : Wg0.D}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer)
    (hIssuer : ctaOf L issuer = ctaOf L g) (hg : g < L.threads)
    (k : Fin 16)
    (hHistory : Wg0ScoreSumsHistory.PairFromPeerReads P L X g i d.block k (d.scoreSums k.val))
    (hBack : ∀ {j q a bs grp}, j < i → X.Reads (g, j) a bs →
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) →
      q.site = .peerRead grp →
      ∃ (w : Nat) (src : Wg0.D) (fp : Acc),
        let mate := Wg0PeerSources.partner L g
        Frame.stateAt (Machine.code P L) X mate w = some (some (.wg0 src)) ∧
        src.site = .exchStore grp ∧ src.block = q.block ∧
        X.Writes (mate, w) fp (exchangeValue src grp.val).toBytes ∧
        rebuild 3 bs = .ok (peerReadValue src grp.val q.sub) ∧
        splitValue 64 (peerReadValue src grp.val q.sub) =
          (src.peerScores.getD (4 * grp.val + 2 * q.sub) (b32 0),
            src.peerScores.getD (4 * grp.val + 2 * q.sub + 1) (b32 0)))
    (valid : Nat → Bool)
    (hm : ∀ {j : Nat} {q : Wg0.D} {group : Fin 8} {a : Acc} {bs : List (Option Byte)},
      j < i → X.Reads (g, j) a bs →
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) →
      q.site = .peerRead group → q.block = d.block →
      ∀ n : Fin 32, q.maskWord.toNat.testBit n.val = valid (32 * Wg0.half L g + n.val)) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (blockScore P L g (Wg0.head L g) (base + 2 * k.val) raw valid))
        (Wg0.peakVal (blockScore P L g (Wg0.head L g) (base + 2 * k.val + 1) raw valid)) := by
  obtain ⟨j, q, r, a0, a1, bs0, bs1, first, second, hj, hr, hq, hrSite, hqSite,
    _, _, hrBlock, hqBlock, hRead0, hRead1, hFirst, hSecond, hTotal⟩ := hHistory
  let group : Fin 8 := ⟨k.val / 2, by omega⟩
  let even := k.val % 2 = 0
  let jRead := if even then j else j + 1
  let dRead := if even then r else q
  let aRead := if even then a0 else a1
  let bsRead := if even then bs0 else bs1
  have hRead : X.Reads (g, jRead) aRead bsRead := by
    dsimp [jRead, aRead, bsRead]
    split_ifs
    · exact hRead0
    · exact hRead1
  have hDRead : Frame.stateAt (Machine.code P L) X g jRead = some (some (.wg0 dRead)) := by
    dsimp [jRead, dRead]
    split_ifs
    · exact hr
    · exact hq
  have hSite : dRead.site = .peerRead group := by
    dsimp [dRead]
    split_ifs
    · exact hrSite
    · exact hqSite
  have hBlock : dRead.block = d.block := by
    dsimp [dRead]
    split_ifs
    · exact hrBlock
    · exact hqBlock
  have hSub : dRead.sub = k.val % 2 := by
    dsimp [dRead]
    split_ifs <;> omega
  have hRebuild : rebuild 3 bsRead = .ok (if even then first else second) := by
    dsimp [bsRead]
    split_ifs
    · exact hFirst
    · exact hSecond
  have hBefore : jRead < i := by unfold jRead; split <;> omega
  let mate := Wg0PeerSources.partner L g
  obtain ⟨w, source, fp, hSource, hSourceSite, hSourceBlock, hWrite, hValue, _⟩ :=
    hBack hBefore hRead hDRead hSite
  have hObserved := Except.ok.inj (hRebuild.symm.trans hValue)
  have hQG : wgOf L g = 0 := RingRoleGeometry.of_trace hX hg (hs g hg).machine hq
  have hWarp := Wg0.warpLt hpre hQG
  obtain ⟨hMateCta, hMateHead, hMateHalf, hMateWarp⟩ := partner_coordinates hpre hWarp
  have hHalf := Wg0.halfLt hWarp
  have hHalfMate := Wg0.halfLt hMateWarp
  have hArm := arm_eq_half hWarp
  have hMateArm := arm_eq_half hMateWarp
  let part : Fin 2 := ⟨Wg0.half L g, hHalf⟩
  let head : Fin 64 := ⟨Wg0.head L g, Wg0.head_lt _ _⟩
  let z0 : Fin 32 := ⟨2 * k.val, by omega⟩
  let z1 : Fin 32 := ⟨2 * k.val + 1, by omega⟩
  let slot0 : Fin 64 := ⟨32 * part.val + z0.val, by omega⟩
  let slot1 : Fin 64 := ⟨32 * part.val + z1.val, by omega⟩
  let otherPart : Fin 2 := ⟨Wg0.half L mate, hHalfMate⟩
  let raw := Wg2.gatheredByte P L issuer d.block
  let lo0 := blockHalfDot P L issuer head slot0 part raw
  let lo1 := blockHalfDot P L issuer head slot1 part raw
  let hi0 := blockHalfDot P L issuer head slot0 otherPart raw
  let hi1 := blockHalfDot P L issuer head slot1 otherPart raw
  have own (z : Fin 32) :
      q.ownScores.getD z.val (b32 0) =
        .float .f32 (blockHalfDot P L issuer head ⟨32 * part.val + z.val, by omega⟩ part raw) := by
    have hWord := score_word_at_exchange hpre hX hs hmma hg
      (PTX.len_of_get hRead1.choose_spec).le hq (by rw [hqSite]; trivial) part z
    have hPart : part.val = Wg0.arm L g := hArm.symm
    have hPart' : (⟨Wg0.half L g % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = part :=
      Fin.ext (Nat.mod_eq_of_lt hHalf)
    simpa only [ite_eq_left hPart, hPart', hqBlock, raw] using hWord
  have hw := Frame.lt_of_get hX hWrite.choose_spec
  have hmmaMate : GemmRing.MmaIssuer P L X (ctaOf L mate) issuer := by rw [hMateCta]; exact hmma
  have hSourceBlock' : source.block = d.block := hSourceBlock.trans hBlock
  have peer (z : Fin 32) :
      source.peerScores.getD z.val (b32 0) =
        .float .f32
          (blockHalfDot P L issuer head ⟨32 * part.val + z.val, by omega⟩ otherPart raw) := by
    have hWord := score_word_at_exchange hpre hX hs hmmaMate hw
      (PTX.len_of_get hWrite.choose_spec).le hSource (by rw [hSourceSite]; trivial) part z
    have hPart : part.val ≠ Wg0.arm L mate := by
      dsimp [part]
      rw [hMateArm]
      omega
    have hPart' : (⟨Wg0.half L mate % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = otherPart :=
      Fin.ext (Nat.mod_eq_of_lt hHalfMate)
    have hHead : (⟨Wg0.head L mate, Wg0.head_lt _ _⟩ : Fin 64) = head := Fin.ext hMateHead
    simpa only [ite_eq_right hPart, hPart', hHead, hSourceBlock', raw] using hWord
  have hReg : 4 * group.val + 2 * dRead.sub = z0.val := by
    rw [hSub]
    dsimp [group, z0]
    omega
  have hPeer : (if even then first else second) = .pair (.float .f32 hi0) (.float .f32 hi1) := by
    rw [hObserved]
    unfold peerReadValue
    rw [hReg, peer z0, show z0.val + 1 = z1.val from rfl, peer z1]
    rfl
  have hBatch : Wg1Mma.batchOf L issuer = Wg1Mma.batchOf L g := by
    change ctaidY L issuer = ctaidY L g
    simp only [ctaidY, hIssuer]
  have hQuery : Wg1Mma.queryOf L issuer = Wg1Mma.queryOf L g := by
    change ctaidX L issuer = ctaidX L g
    simp only [ctaidX, hIssuer]
  have hsum (slot : Fin 64) :
      blockHalfDot P L issuer head slot part raw + blockHalfDot P L issuer head slot otherPart raw =
        blockDot P L g (Wg0.head L g) slot.val raw := by
    have hEq : blockDot P L issuer head.val slot.val raw =
        blockDot P L g (Wg0.head L g) slot.val raw := by
      simp only [blockDot, hBatch, hQuery, head]
    have hOpp : otherPart.val = 1 - part.val := hMateHalf
    by_cases h : part.val = 0
    · have hp : part = 0 := Fin.ext h
      have hm : otherPart = 1 := Fin.ext (by rw [hOpp, h]; rfl)
      rw [hp, hm, blockHalfDot_sum, hEq]
    · have hv : part.val = 1 := by have := part.isLt; omega
      have hp : part = 1 := Fin.ext hv
      have hm : otherPart = 0 := Fin.ext (by rw [hOpp, hv]; rfl)
      rw [hp, hm, add_comm, blockHalfDot_sum, hEq]
  rw [hPeer] at hTotal
  have hExpected := scorePair_blockScore (P := P) (L := L) (g := g) q raw valid k
    lo0 lo1 hi0 hi1 (own z0) (own z1) (hm hj hRead1 hq hqSite hqBlock z0)
    (hm hj hRead1 hq hqSite hqBlock z1)
    (hsum slot0) (hsum slot1)
  exact Except.ok.inj (hTotal.symm.trans hExpected)

section
variable {g i issuer : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hg : g < L.threads) (hi : i ≤ (X.tr g).length)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
include hpre hX hs ht hmma hIssuer hg hi hd

/-- Each actual vote score pair is the matching block dot product with its actual mask.
The caller relates the two bits used by that pair to the logical validity function. -/
theorem actual_vote_score_pair (hsite : d.site = .rescaleVote) (k : Fin 16) (valid : Nat → Bool)
    (hm : ∀ {j : Nat} {q : Wg0.D} {group : Fin 8},
      Frame.stateAt (Machine.code P L) X g j = some (some (.wg0 q)) →
      q.site = .peerRead group → q.block = d.block →
      ∀ n : Fin 32, q.maskWord.toNat.testBit n.val = valid (32 * Wg0.half L g + n.val)) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (blockScore P L g (Wg0.head L g) (base + 2 * k.val) raw valid))
        (Wg0.peakVal (blockScore P L g (Wg0.head L g) (base + 2 * k.val + 1) raw valid)) :=
  actual_score_pair_from_history hpre hX hs hmma hIssuer hg k
    (Wg0ScoreSumsHistory.pairs_at_vote hX hs hg hi hd hsite k)
    (fun _ hr hq hqSite => Wg0PeerReadback.readback_value hpre hX hs ht hr hq hqSite)
    valid (fun _ _ hq hqSite hb => hm hq hqSite hb)

/-- The actual vote's score pairs incorporate the real index validity and both QK halves. -/
theorem actual_vote_scores_from_indices (hsite : d.site = .rescaleVote) (k : Fin 16) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let score := fun pos => blockScore P L g (Wg0.head L g) pos raw
      (gatheredValid P L g d.block)
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (score (base + 2 * k.val)))
        (Wg0.peakVal (score (base + 2 * k.val + 1))) :=
  actual_vote_score_pair hpre hX hs ht hmma hIssuer hg hi hd hsite k _ (by
    intro j q group hq hqSite hBlock bit
    rw [← hBlock]
    exact exchange_mask_bit hpre hX hs ht hq (by rw [hqSite]; trivial) bit)

/-- The local maximum sees the actual index validity and both QK halves. -/
theorem actual_rowMax_scores_from_indices (hsite : d.site = .rowMax) (k : Fin 16) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let score := fun pos => blockScore P L g (Wg0.head L g) pos raw
      (gatheredValid P L g d.block)
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (score (base + 2 * k.val)))
        (Wg0.peakVal (score (base + 2 * k.val + 1))) :=
  actual_score_pair_from_history hpre hX hs hmma hIssuer hg k
    (Wg0ScoreSumsHistory.pairs_at_rowMax hX hs hg hi hd hsite k)
    (fun _ hr hq hqSite => Wg0PeerReadback.readback_value hpre hX hs ht hr hq hqSite) _ (by
    intro j q group a bytes _ _ hq hqSite hBlock bit
    rw [← hBlock]
    exact exchange_mask_bit hpre hX hs ht hq (by rw [hqSite]; trivial) bit)
end

variable {g i issuer cut : Nat} {d : Wg0.D} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (hmma : GemmRing.MmaIssuer P L X (ctaOf L g) issuer) (hIssuer : ctaOf L issuer = ctaOf L g)
    (hg : g < L.threads) (hCut : i ≤ cut) (hLen : cut < (X.tr g).length)
    (hPrior : ∀ t, baseCausality L X t (g, cut) → ¬ MachineTracking.Dismisses P L X t)
include hpre hX hs hmma hIssuer hg hCut hLen hPrior

private theorem causal_scores_from_history (k : Fin 16)
    (hHistory : Wg0ScoreSumsHistory.PairFromPeerReads P L X g i d.block k (d.scoreSums k.val)) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let score := fun pos => blockScore P L g (Wg0.head L g) pos raw
      (gatheredValid P L g d.block)
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (score (base + 2 * k.val)))
        (Wg0.peakVal (score (base + 2 * k.val + 1))) :=
  actual_score_pair_from_history hpre hX hs hmma hIssuer hg k hHistory
    (fun hj hr hq hSite =>
      Wg0PeerReadback.actual_readback_value hpre hX hs hr hq hSite
        (hj.le.trans hCut) hLen hPrior) _ (by
      intro j q grp a bs hj hr hq hSite hBlock bit
      rw [← hBlock]
      exact exchange_mask_bit_of_peer_read hpre hX hs hr hq hSite (hj.le.trans hCut)
        hLen hPrior bit)

/-- The actual vote's scores use the paired QK cells and causally prior validity mask. -/
theorem causal_vote_scores_from_indices
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d)))
    (hsite : d.site = .rescaleVote) (k : Fin 16) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let score := fun pos => blockScore P L g (Wg0.head L g) pos raw
      (gatheredValid P L g d.block)
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (score (base + 2 * k.val)))
        (Wg0.peakVal (score (base + 2 * k.val + 1))) :=
  causal_scores_from_history hpre hX hs hmma hIssuer hg hCut hLen hPrior k
    (Wg0ScoreSumsHistory.pairs_at_vote hX hs hg (hCut.trans hLen.le) hd hsite k)

/-- The row-maximum writer's scores use the paired QK cells and causally prior mask. -/
theorem causal_rowMax_scores_from_indices
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.wg0 d))) (hsite : d.site = .rowMax)
    (k : Fin 16) :
    let raw := Wg2.gatheredByte P L issuer d.block
    let score := fun pos => blockScore P L g (Wg0.head L g) pos raw
      (gatheredValid P L g d.block)
    let base := 32 * Wg0.half L g
    d.scoreSums k.val =
      .pair (Wg0.peakVal (score (base + 2 * k.val)))
        (Wg0.peakVal (score (base + 2 * k.val + 1))) :=
  causal_scores_from_history hpre hX hs hmma hIssuer hg hCut hLen hPrior k
    (Wg0ScoreSumsHistory.pairs_at_rowMax hX hs hg (hCut.trans hLen.le) hd hsite k)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
