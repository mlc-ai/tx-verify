-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.PvProbabilityReadback
public import Kernels.FlashMlaSparseDecodeH64.Proof.Result.Probability
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUpdateHistory
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0VoteBranch
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityUnique
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0ProbabilityBytes
import Lemmas.Tcgen05.MmaOperandObservations

@[expose] public section

/-! # Actual PV A operand values from the softmax probability states -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX PTX.Flow AsyncCopy MmaDataTrace

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- For this observed PV issue, the only numerical premise is the weight produced at each
actual same-block probability store selected by the operand's geometry. -/
theorem actual_pv_probability {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hops : X.async.mmaOperands (g, i) = some ops)
    (row : Fin 128) (weight : Nat → ℝ)
    (hweight : ∀ (k : Fin 16) {j : Nat} {w : Wg0.D} {e : Event},
      let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
      let lane := probabilityLane L (ctaOf L g) row slot
      let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
      X.get (lane, j) = some e →
      Frame.stateAt (Machine.code P L) X lane j = some (some (.wg0 w)) →
      w.block = d.i → w.site = .pStore site → w.sub = slot.val / 2 % 4 →
      w.pw (row.val % 64) slot.val = weight slot.val) :
    Bf16Operand ops.a row.val (fun k => weight (16 * (issue.val / 2) + k)) := by
  apply pvA_from_probability hpre hX hi hops row weight
  intro k b
  obtain ⟨value, hr, _⟩ :=
    hX.mma_read_exists hi hops (isB := false) (pvProbabilityByte L g d.i issue row k b)
  obtain ⟨j, w, e, u, he, hw, hblock, hwsite, hsub, hf, hrf⟩ :=
    pv_probability_byte_source hpre hX hs ht hi hd hsite row k b hr
  exact ⟨j, w, e, u, hwsite, hsub, hblock, he, hf,
    hweight k he hw hblock hwsite hsub, hrf⟩

private theorem probability_update_weight {g slot : Nat} {old out : Wg0.D}
    (hpre : Pre P L mem0) (hUpdate : Wg0.probabilityUpdate L g old = some out)
    (scores : Nat → WithBot ℝ)
    (hScores : ∀ p : Fin 16, old.scoreSums p.val =
      .pair (Wg0.peakVal (scores (32 * Wg0.half L g + 2 * p.val)))
        (Wg0.peakVal (scores (32 * Wg0.half L g + 2 * p.val + 1))))
    (hlo : 32 * Wg0.half L g ≤ slot) (hhi : slot < 32 * Wg0.half L g + 32) :
    out.pw (Wg0.head L g) slot = shiftedWeight P.scale (Wg0.reference old) (scores slot) := by
  let base := 32 * Wg0.half L g
  let lo := fun p : Fin 16 => scores (base + 2 * p.val)
  let hi := fun p : Fin 16 => scores (base + 2 * p.val + 1)
  have hGain : ∃ gain, valFloat .f32 old.gainWord = .ok gain := by
    have hp := hUpdate
    simp only [Wg0.probabilityUpdate, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hp
    obtain ⟨_, _, gain, hgain, _⟩ := hp
    change (valFloat .f32 old.gainWord).toOption = some gain at hgain
    exact ⟨gain, by cases hx : valFloat .f32 old.gainWord <;> simp_all [Except.toOption]⟩
  obtain ⟨gain, hgain⟩ := hGain
  obtain ⟨actual, hActual, _, _, hWeights⟩ :=
    probabilityUpdate_terms hpre old lo hi gain hScores hgain
  have hSame := Option.some.inj (hActual.symm.trans hUpdate)
  subst actual
  let j : Fin 16 := ⟨(slot - base) / 2, by dsimp [base]; omega⟩
  let pair := fun p : Fin 16 =>
    (shiftedWeight P.scale (Wg0.reference old) (lo p),
      shiftedWeight P.scale (Wg0.reference old) (hi p))
  have hl : j.val < (List.finRange 16).length := by simp
  have hFin : (List.finRange 16)[j.val]? = some j := by
    rw [List.getElem?_eq_getElem hl, List.getElem_finRange]
    rfl
  have hp : ((List.finRange 16).map pair).getD j.val (0, 0) = pair j := by
    simp only [List.getD, List.getElem?_map, hFin, Option.map_some, Option.getD_some]
  have hW := hWeights slot hlo hhi
  change out.pw (Wg0.head L g) slot =
    (if (slot - base) % 2 = 0 then (((List.finRange 16).map pair).getD j.val (0, 0)).1
     else (((List.finRange 16).map pair).getD j.val (0, 0)).2) at hW
  rw [hp] at hW
  rw [hW]
  split_ifs with he
  · have hIdx : base + 2 * j.val = slot := by dsimp [j, base] at *; omega
    exact congrArg (fun n => shiftedWeight P.scale (Wg0.reference old) (scores n)) hIdx
  · have hIdx : base + 2 * j.val + 1 = slot := by dsimp [j, base] at *; omega
    exact congrArg (fun n => shiftedWeight P.scale (Wg0.reference old) (scores n)) hIdx

/-- The actual PV A operand is the shifted weight of each score. It suffices to identify
the packed score pairs and the finite reference at the actual preceding softmax vote. -/
theorem actual_pv_probability_of_vote {g i : Nat} {d : Wg1Mma.D} {issue : Fin 8} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hops : X.async.mmaOperands (g, i) = some ops)
    (row : Fin 128) (scores : Nat → WithBot ℝ) (ref : ℝ)
    (hvalues : ∀ (k : Fin 16) {j : Nat} {v mid : Wg0.D} {e : Event} {take : Bool},
      let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
      let lane := probabilityLane L (ctaOf L g) row slot
      let base := 32 * Wg0.half L lane
      X.get (lane, j) = some e →
      (∃ mode mask arg, e.kind = .voteMode mode mask arg take) →
      Frame.stateAt (Machine.code P L) X lane j = some (some (.wg0 v)) →
      v.site = .rescaleVote → v.block = d.i → Wg0.afterReferenceVote v take = some mid →
      Wg0.reference mid = ref ∧ ∀ p : Fin 16, v.scoreSums p.val =
        .pair (Wg0.peakVal (scores (base + 2 * p.val)))
          (Wg0.peakVal (scores (base + 2 * p.val + 1)))) :
    Bf16Operand ops.a row.val
      (fun k => shiftedWeight P.scale ref (scores (16 * (issue.val / 2) + k))) := by
  apply actual_pv_probability hpre hX hs ht hi hd hsite hops row
    (fun k => shiftedWeight P.scale ref (scores k))
  intro k j w e
  dsimp only
  intro he hw hblock hwsite _
  obtain ⟨vote, v, f, mode, mask, arg, take, mid, out, _, hv, hk, hstate, hvsite, hvblock,
    hRef, hUpdate, hPW⟩ := Wg0ProbabilityUpdateHistory.probability_update_of_store
      ht (Frame.lt_of_get hX he) (PTX.len_of_get he).le hw hwsite
  obtain ⟨href, hScores⟩ :=
    hvalues k hv ⟨mode, mask, arg, hk⟩ hstate hvsite (hvblock.trans hblock) hRef
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let lane := probabilityLane L (ctaOf L g) row slot
  let old : Wg0.D := {mid with voteTaken := take}
  have hp (p : Fin 16) : old.scoreSums p.val =
      .pair (Wg0.peakVal (scores (32 * Wg0.half L lane + 2 * p.val)))
        (Wg0.peakVal (scores (32 * Wg0.half L lane + 2 * p.val + 1))) := by
    change mid.scoreSums p.val = _
    rw [Wg0.afterReferenceVote_fields hRef]
    exact hScores p
  obtain ⟨_, hHead, hHalf⟩ := probabilityLane_coords hpre (ctaOf L g) row slot
  have hlo : 32 * Wg0.half L lane ≤ slot.val := by rw [hHalf]; omega
  have hhi : slot.val < 32 * Wg0.half L lane + 32 := by rw [hHalf]; omega
  change w.pw (row.val % 64) slot.val = shiftedWeight P.scale ref (scores slot.val)
  rw [hPW, ← hHead, probability_update_weight hpre hUpdate scores hp hlo hhi]
  change shiftedWeight P.scale (Wg0.reference mid) (scores slot.val) = _
  rw [href]

/-- The actual probability bytes of a PV issue encode a real vector. -/
theorem actual_pv_probability_finite {g i consumer cut : Nat}
    {d : Wg1Mma.D} {issue : Fin 8} {ops : MmaOperands}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hCut : Protocol.PvCausalCut.Cut P L X consumer cut d.i)
    (hCta : ctaOf L g = ctaOf L consumer)
    (hi : X.MmaIssue (g, i) (Wg1Mma.pvDest issue) (pvOperands L g d.i issue)
      (pvAccum d.i issue) [0, 0, 0, 0])
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.mma d)))
    (hsite : d.site = .pvMma issue) (hops : X.async.mmaOperands (g, i) = some ops)
    (row : Fin 128) :
    ∃ weight : Nat → ℝ, Bf16Operand ops.a row.val
      (fun k => weight (16 * (issue.val / 2) + k)) := by
  have read (k : Fin 16) (b : Fin 2) :
      let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
      let h := probabilityLane L (ctaOf L g) row slot
      let site : Fin 4 := ⟨slot.val % 32 / 8, by omega⟩
      ∃ j w e u, X.get (h, j) = some e ∧
        Frame.stateAt (Machine.code P L) X h j = some (some (.wg0 w)) ∧
        w.block = d.i ∧ w.site = .pStore site ∧ w.sub = slot.val / 2 % 4 ∧
        (Wg0.code P L h).toMachine.Fired (some w) e (some u) ∧
        X.rf (.async (g, i) (.mmaRead false (2 * (row.val * 16 + k.val) + b.val))) 0 =
          some (.thread (h, j)) := by
    obtain ⟨value, hr, _⟩ :=
      hX.mma_read_exists hi hops (isB := false) (pvProbabilityByte L g d.i issue row k b)
    exact actual_pv_probability_byte_source hpre hX hs hCut hCta hi hd hsite row k b hr
  choose src state emit final hState using fun k : Fin 16 => read k 0
  let base := 16 * (issue.val / 2)
  let weight := fun n : Nat => if hn : n - base < 16 then
    (state ⟨n - base, hn⟩).pw (row.val % 64) n else 0
  refine ⟨weight, pvA_from_probability hpre hX hi hops row weight ?_⟩
  intro k b
  obtain ⟨j, w, ev, u, he, hw, hBlock, hSite, hSub, hFired, hRF⟩ := read k b
  obtain ⟨he0, hs0, hBlock0, hSite0, hSub0, hFired0, _⟩ := hState k
  let slot : Fin 64 := ⟨pvSlot issue k, by unfold pvSlot; omega⟩
  let h := probabilityLane L (ctaOf L g) row slot
  have written {j : Nat} {d : Wg0.D} {e : Event} {u : TState} {site : Fin 4}
      (he : X.get (h, j) = some e) (hd : d.site = .pStore site)
      (hf : (Wg0.code P L h).toMachine.Fired (some d) e (some u)) :
      ∃ a bytes, X.Writes (h, j) a bytes := by
    obtain ⟨a, hk, _, _, _⟩ := Wg0.fired_pStore_event hpre hd hf
    obtain ⟨tag, kind⟩ := e
    change kind = _ at hk
    subst kind
    exact ⟨a, _, tag, he⟩
  obtain ⟨a, bs, hWr⟩ := written he hSite hFired
  obtain ⟨a0, bs0, hWr0⟩ := written he0 hSite0 hFired0
  have hH := Frame.lt_of_get hX he
  have hj := Wg0ProbabilityUnique.actual_write_unique hpre hX (hs h hH).machine
    hWr hWr0 hw hs0 hSite hSite0 (hBlock.trans hBlock0.symm) (hSub.trans hSub0.symm)
  have hSame : state k = w := by
    rw [← hj, hw] at hs0
    exact Machine.ThreadD.wg0.inj (Option.some.inj (Option.some.inj hs0.symm))
  refine ⟨j, w, ev, u, hSite, hSub, hBlock, he, hFired, ?_, hRF⟩
  have hIdx : pvSlot issue k - base = k.val := by unfold pvSlot; dsimp [base]; omega
  dsimp only [weight]
  rw [dite_eq_left (hIdx ▸ k.isLt)]
  have hArg : (⟨pvSlot issue k - base, hIdx ▸ k.isLt⟩ : Fin 16) = k := Fin.ext hIdx
  rw [hArg, hSame]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
