-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleRound
import Lemmas.Flow.CountTake
public import Kernels.TmlFa4Fwd.Proof.Thread.TmemStoreCompletion
public import Kernels.TmlFa4Fwd.Proof.Thread.Correction

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Proof PTX.Flow PTX.TcMma Thread

noncomputable section

/-- The lane's actual rendezvous, alpha read, vote, optional eight products, and releases. -/
structure RescaleVisit (l : Launch) (X : Execution) (g pos : Nat) (stage : Fin 2)
    (alpha : ℝ) (old : Fin 8 → Nat → ℝ) (word : BitVec 32)
    (coefficient : Value := fl alpha) : Prop where
  rendezvous : X.get (g, pos) = some
    ⟨statsBarrierPc stage true, .bar (statsBarrierId l g stage) (some 64) .sync⟩
  alphaRead : X.get (g, pos + 1) = some ⟨statsPc stage .alpha,
    .rd { loc := statsLoc l g stage .alpha, size := 4 } (coefficient.toBytes.map some)⟩
  ballot : X.get (g, pos + 2) = some
    ⟨statsPc stage .alpha + 2, .vote (2 ^ 32 - 1) (decide (alpha < 1)) word⟩
  products : word ≠ 0 →
    (∀ chunk : Fin 8, RescaleChunkEffects l X g (pos + 3 + 3 * chunk.val)
      stage chunk (old chunk) alpha) ∧
      X.get (g, pos + 3 + 24) = some ⟨rescaleStorePc stage 7 + 1, .tc .waitSt⟩
  credit : X.get (g, pos + 3 + rescaleBodyEvents word) = some
    ⟨rescaleSignalPc stage + 1, .arrive (creditLoc l g stage) 0 1 true .cta⟩
  release : X.get (g, pos + 3 + rescaleBodyEvents word + 1) = some
    ⟨rescaleSignalPc stage + 2, .arrive (rescaleReuseLoc l g stage) 0 1 true .cta⟩

section
variable {l : Launch} {X : Execution} {g pos : Nat} {stage : Fin 2} {alpha : ℝ}
    {old : Fin 8 → Nat → ℝ} {word : BitVec 32} {coefficient : Value}

private theorem RescaleVisit.countTmem (h : RescaleVisit l X g pos stage alpha old word coefficient)
    (q : Event → Bool) (hTc : ∀ pc op, q ⟨pc, .tc op⟩ = false) (n : Nat)
    (hn : n ≤ rescaleBodyEvents word) :
    ((X.tr g).take (pos + 3 + n)).countP q = ((X.tr g).take (pos + 3)).countP q := by
  induction n with
  | zero => rw [Nat.add_zero]
  | succ n ih =>
    have hw : word ≠ 0 := by
      intro hw
      simp only [rescaleBodyEvents, ite_eq_left hw] at hn
      omega
    have h25 : n < 25 := by
      simp only [rescaleBodyEvents, ite_eq_right hw] at hn
      omega
    have ⟨e, he, hq⟩ : ∃ (e : Event), X.get (g, pos + 3 + n) = some e ∧ q e = false := by
      by_cases hn24 : n = 24
      · rw [hn24]
        exact ⟨_, (h.products hw).2, hTc _ _⟩
      · let chunk : Fin 8 := ⟨n / 3, by omega⟩
        have hc := (h.products hw).1 chunk
        have hSum : n = 3 * chunk.val + n % 3 := by dsimp [chunk]; omega
        have hMod : n % 3 < 3 := Nat.mod_lt _ (by decide)
        cases hm : n % 3 with
        | zero =>
          have hEq : pos + 3 + n = pos + 3 + 3 * chunk.val := by omega
          rw [hEq]
          exact ⟨_, hc.1, hTc _ _⟩
        | succ m =>
          cases m with
          | zero =>
            have hEq : pos + 3 + n = (pos + 3 + 3 * chunk.val) + 1 := by omega
            rw [hEq]
            exact ⟨_, hc.2.1, hTc _ _⟩
          | succ m =>
            have hm' : m = 0 := by omega
            subst m
            have hEq : pos + 3 + n = (pos + 3 + 3 * chunk.val) + 2 := by omega
            rw [hEq]
            exact ⟨_, hc.2.2, hTc _ _⟩
    rw [Nat.add_succ, countP_take_succ_false he hq, ih (by omega)]

/-- The full-warp vote at the end of the rendezvous prefix has the entry ordinal. -/
theorem RescaleVisit.ballotOrdinal (h : RescaleVisit l X g pos stage alpha old word coefficient) :
    X.MaskK voteClass (g, pos + 2) (2 ^ 32 - 1)
      (((X.tr g).take pos).countP isFullWarpVote) := by
  have h0 := countP_take_succ_false (p := isFullWarpVote) h.rendezvous rfl
  have h1 := countP_take_succ_false (p := isFullWarpVote) h.alphaRead rfl
  exact ⟨⟨_, _, h.ballot, rfl, rfl⟩, h1.trans h0⟩

private theorem countVisitBallot {X : Execution} {g j pc mask : Nat} {input : Bool}
    {word : BitVec 32} (he : X.get (g, j) = some ⟨pc, .vote mask input word⟩) :
    ((X.tr g).take (j + 1)).countP (isWarpVote mask) =
      ((X.tr g).take j).countP (isWarpVote mask) + 1 := by
  apply countP_take_succ he
  simp only [isWarpVote, voteClass, Option.any_some, beq_self_eq_true]

/-- The trace segment contains exactly one full-mask vote. -/
theorem RescaleVisit.voteCount (h : RescaleVisit l X g pos stage alpha old word coefficient) :
    ((X.tr g).take (pos + 3 + rescaleBodyEvents word + 2)).countP isFullWarpVote =
      ((X.tr g).take pos).countP isFullWarpVote + 1 := by
  have h2 := countVisitBallot h.ballot
  have h3 := h.countTmem isFullWarpVote (fun _ _ => rfl) _ (Nat.le_refl _)
  have h4 := countP_take_succ_false (p := isFullWarpVote) h.credit rfl
  have h5 := countP_take_succ_false (p := isFullWarpVote) h.release rfl
  exact h5.trans (h4.trans (h3.trans (h2.trans (congrArg (· + 1) h.ballotOrdinal.2))))

/-- The trace segment leaves the shuffle ordinal unchanged. -/
theorem RescaleVisit.shuffleCount (h : RescaleVisit l X g pos stage alpha old word coefficient) :
    ((X.tr g).take (pos + 3 + rescaleBodyEvents word + 2)).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl := by
  have h0 := countP_take_succ_false (p := Execution.isShfl) h.rendezvous rfl
  have h1 := countP_take_succ_false (p := Execution.isShfl) h.alphaRead rfl
  have h2 := countP_take_succ_false (p := Execution.isShfl) h.ballot rfl
  have h3 := h.countTmem Execution.isShfl (fun _ _ => rfl) _ (Nat.le_refl _)
  have h4 := countP_take_succ_false (p := Execution.isShfl) h.credit rfl
  have h5 := countP_take_succ_false (p := Execution.isShfl) h.release rfl
  exact h5.trans (h4.trans (h3.trans (h2.trans (h1.trans h0))))

/-- The taken rescale visit writes every output column on its issuing lane
under the same statistics grant as the named-barrier return. -/
theorem RescaleVisit.storeOfColumn (h : RescaleVisit l X g pos stage alpha old word coefficient)
    (hTake : word ≠ 0) (col : Fin 128) :
    ∃ store, store.1 = g ∧ OutputRescaleStore X store stage ∧
      StoreCell l X store ⟨g/l.block,laneBase l g+laneOf l g,outputColumn stage+col.val⟩ ∧
      (correctionBefore X store).barrier (statsBarrierId l g stage) =
        (correctionBefore X (g,pos)).barrier (statsBarrierId l g stage)+1 := by
  let chunk : Fin 8 := ⟨col.val/16,by have := col.isLt; omega⟩
  let j := col.val%16
  let index := pos+3+3*chunk.val+2
  let addr := outputAddress l g stage (16*chunk.val)
  let values := List.ofFn fun i : Fin 16 => fl (old chunk i.val*alpha)
  have he := ((h.products hTake).1 chunk).2.2
  have hWord : j < values.length := by simp [values,j,Nat.mod_lt _ (by decide : 0 < 16)]
  have hCol : outputColumn stage + 16*chunk.val < 512 := by
    have := outputColumn_range stage
    have := chunk.isLt
    omega
  have hCell : ⟨g/l.block,laneBase l g+laneOf l g,outputColumn stage+col.val⟩ =
      tcDataCell l g .s32x32b addr j := by
    unfold addr outputAddress
    rw [tcDataCell_warp32 l g j hCol]
    have hIndex : col.val = 16*chunk.val+j := by dsimp [chunk,j]; omega
    rw [hIndex,Nat.add_assoc]
  refine ⟨(g,index),rfl,OutputRescaleStore.ofDecoded stage chunk he,
    ⟨addr,values,.s32x32b,j,⟨_,he⟩,hWord,hCell⟩,?_⟩
  let q := Execution.isBarId (statsBarrierId l g stage)
  have hMark : q ⟨statsBarrierPc stage true,
      .bar (statsBarrierId l g stage) (some 64) .sync⟩ = true := by
    simp [q,Execution.isBarId]
  have h0 := countP_take_succ h.rendezvous hMark
  have h1 := countP_take_succ_false (p := q) h.alphaRead rfl
  have h2 := countP_take_succ_false (p := q) h.ballot rfl
  have hN : 3*chunk.val+2 ≤ rescaleBodyEvents word := by
    simp only [rescaleBodyEvents,ite_eq_right hTake]
    have := chunk.isLt
    omega
  have h3 := h.countTmem q (fun _ _ => rfl) (3*chunk.val+2) hN
  rw [correctionBarrierOrdinal,correctionBarrierOrdinal]
  change ((X.tr g).take index).countP q = ((X.tr g).take pos).countP q+1
  rw [show index = pos+3+(3*chunk.val+2) by dsimp [index]; omega,h3]
  exact h2.trans (h1.trans h0)
end

/-- Enter at the actual statistics barrier and leave immediately after both release arrivals.
The statistics and TMEM input values come from the producer witnesses for this visit. -/
theorem observeRescaleVisitOfWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    {g pos : Nat} {t : TState} {F : List (Nat × Value)} (hp : Pre p l m)
    (stage : Fin 2) (coefficient : Value) (alpha : ℝ) (old : Fin 8 → Nat → ℝ)
    (hFactor : Thread.Correction.RescaleFactorWord coefficient alpha)
    (ht : At t (statsBarrierPc stage true) F)
    (hBar : t.regs (statsBarrierReg stage) = some (b32 (statsBarrierId l g stage)))
    (hAddress : t.regs 1627 = some (b32 (l.sharedBase + 4 * rowOf l g)))
    (hAddr : ∀ rv ∈ rescaleStageAddresses l g stage, rv ∈ F)
    (hCredit : (outputCreditReg stage, b32 (creditLoc l g stage).addr) ∈ F)
    (hReuse : (rescaleReuseReg stage, b32 (rescaleReuseLoc l g stage).addr) ∈ F)
    (hControl : ∀ rv ∈ F, rv.1 ≠ statsReg stage .alpha ∧ rv.1 ≠ rescalePredReg stage ∧
      rv.1 ≠ rescaleVoteReg stage ∧ rv.1 ≠ maskZeroReg stage)
    (hFrame : ∀ chunk : Fin 8, ∀ r ∈ F.map Prod.fst, r ∉ rescaleDataRegs stage chunk ∧
      rescaleLocalKeeps stage chunk r)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rescaleCountReg stage ∧
      pair.1 ≠ rescaleSignalDst stage ∧ pair.1 ≠ rescaleSignalDst stage + 1)
    (hAlpha : ∀ bs, X.get (g, pos + 1) = some
      ⟨statsPc stage .alpha, .rd { loc := statsLoc l g stage .alpha, size := 4 } bs⟩ →
      bs = coefficient.toBytes.map some)
    (hRead : ∀ word : BitVec 32, word ≠ 0 → X.get (g, pos + 2) =
      some ⟨statsPc stage .alpha + 2, .vote (2 ^ 32 - 1) (decide (alpha < 1)) word⟩ →
      ∀ (chunk : Fin 8) vals, X.get (g, pos + 3 + 3 * chunk.val) =
      some ⟨rescaleLoadPc stage chunk,
        .tc (.ld (outputAddress l g stage (16 * chunk.val)) vals .s32x32b)⟩ →
      vals = List.ofFn (fun i : Fin 16 => fl (old chunk i.val)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    ∃ word u, RescaleVisit l X g pos stage alpha old word coefficient ∧
      At u (rescaleSignalPc stage + 3) F ∧
      Run kernel Assumptions.all l g u
        ((X.tr g).drop (pos + 3 + rescaleBodyEvents word + 2)) none := by
  obtain ⟨word, s, he, ha, hv, _, hs, hR⟩ :=
    observeRescaleControlOfWord hp stage coefficient alpha hFactor
      ht hBar hAddress hControl hAlpha rfl hr
  have hAddr' : Holds s.regs (rescaleStageAddresses l g stage) := by
    have hAll := hs.2.2.2.2.2
    generalize rescaleStageAddresses l g stage = pairs at hAddr ⊢
    induction pairs with
    | nil => trivial
    | cons pair pairs ih =>
      exact ⟨holds_mem hAll (hAddr pair (List.mem_cons_self)), ih
        (fun rv hm => hAddr rv (List.mem_cons_of_mem _ hm))⟩
  obtain ⟨u, hProducts, hCreditEvent, hReleaseEvent, hu, hU⟩ := observeRescaleBodyOfWord hp stage
    word old coefficient alpha hFactor hs hAddr' hCredit hReuse hFrame hFresh
    (fun hw => hRead word hw hv) hR
  exact ⟨word, u, ⟨he, ha, hv, hProducts, hCreditEvent, hReleaseEvent⟩, hu, hU⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
