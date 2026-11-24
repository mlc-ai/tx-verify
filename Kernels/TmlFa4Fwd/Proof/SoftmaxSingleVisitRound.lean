-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstFmaOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitBiasWordOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption Thread.Scores Epilogue

noncomputable section

/-- The phase-zero wait, Bias addresses and geometry that remain live until the first FMA. -/
def singleVisitRoundFacts (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (batch tile biasCap pastTile : Nat) : List (Nat × Value) :=
  let stage := stageOf warp
  [(2769, b32 (waitLoc l g stage 1).addr), (2771, b32 (waitLoc l g stage 2).addr),
    (2770, b32 0), (2788, b32 (scoreAddress l g stage 0)),
    (2789, b32 (scoreAddress l g stage 2)), (5127, b32 (3 + warp.val))] ++
    (List.finRange 16).map
      (fun i => ((biasReadSite false i).base, b32 (biasVectorBase l g stage false i))) ++
    biasFenceFacts l g warp false ++
    [(1229, b32 0), (1224, b32 (p.kLength batch)), (2868, b32 (128 * (2 * tile + stage.val))),
      (1223, maskSigned (-(p.qLength batch : Int)))] ++
    firstLoopGeometry 1 biasCap pastTile

private theorem singleVisitFrameKeeps (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (batch tile biasCap pastTile : Nat) {r : Nat}
    (hr : r ∈ (singleVisitRoundFacts p l g warp batch tile biasCap pastTile).map Prod.fst) :
    (r ≠ 9751 ∧ firstScoreKeeps r) ∧ (r ≠ 9752 ∧ ∀ i, biasVectorKeeps false i r) := by
  let rs := [2769, 2771, 2770, 2788, 2789, 5127, 2784, 2846, 2842, 2838, 2834, 2830, 2826,
    2822, 2784, 2818, 2814, 2810, 2806, 2802, 2798, 2794, 481, 482, 1062, 2535, 1229,
    1224, 2868, 1223, 1225, 1226, 1228, 1229]
  change r ∈ rs at hr
  have hScore : rs.all (fun d => @decide (d ≠ 9751 ∧ firstScoreKeeps d)
      (by unfold firstScoreKeeps; infer_instance)) = true := by
    decide +kernel
  have hBias (i : Fin 16) :
      rs.all (fun d => @decide (d ≠ 9752 ∧ biasVectorKeeps false i d)
        (by unfold biasVectorKeeps; infer_instance)) = true := by
    fin_cases i <;> decide +kernel
  have hScoreFrame : r ≠ 9751 ∧ firstScoreKeeps r :=
    @of_decide_eq_true _ (by unfold firstScoreKeeps; infer_instance)
      (List.all_eq_true.mp hScore r hr)
  have hBiasFrame (i : Fin 16) : r ≠ 9752 ∧ biasVectorKeeps false i r :=
    @of_decide_eq_true _ (by unfold biasVectorKeeps; infer_instance)
      (List.all_eq_true.mp (hBias i) r hr)
  exact ⟨hScoreFrame, (hBiasFrame 0).1, fun i => (hBiasFrame i).2⟩

/-- For a tile with one key visit, the actual successful Bias acquire and the subsequent
shared reads supply all Bias operands of the numerical round. The QK premise refers to the
score loads observed in the same thread trace. -/
theorem singleVisitRoundOfScoreLoads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    (warp : Fin 8) {g j batch tile head biasCap pastTile : Nat}
    {t : TState}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hCoords : assignedCoordinates p batch (g / l.block) = (tile, head))
    (hTrip : Mma.trips p batch tile = 1)
    (hRow : 128 * (2 * tile + (stageOf warp).val) + (g % l.block) % 128 < p.qLength batch)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (ht : At t 3425 (singleVisitRoundFacts p l g warp batch tile biasCap pastTile))
    (hDots : ∀ pos (q : Fin 4) vals, X.get (g, pos) = some
        ⟨scorePc .first q, .tc (.ld (scoreAddress l g (stageOf warp) q) vals .s32x32b)⟩ →
      ∀ word : Fin 32, vals[word.val]? = some (.float .f32
        (firstScoreDot p l g batch head
          (p.qOffset batch + 128 * (2 * tile + (stageOf warp).val)) 0 q word)))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    ∃ qkFails biasFails,
      let fence := j + qkFails + 1 + 4 + biasFails + 1 + 64
      X.get (g, fence) = some ⟨3581, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, fence + 1) = some ⟨3583, .bar (11 + (stageOf warp).val) (some 128) .sync⟩ ∧
      (laneOf l g = 0 → X.get (g, fence + 2) = some
        ⟨3590, .arrive (signalLoc l g (stageOf warp) 0) 0 1 true .cta⟩) ∧
      FirstRoundProgress p l X warp g (if laneOf l g = 0 then fence + 3 else fence + 2)
        batch head (128 * (2 * tile + (stageOf warp).val) + (g % l.block) % 128)
        1 biasCap pastTile := by
  let stage := stageOf warp
  let base := 2 * tile + stage.val
  let row := 128 * base + (g % l.block) % 128
  let bias := firstVisitBiasValue p batch row head
  have hAssigned := assignedCoordinates_valid hp hLo hHi
  rw [hCoords] at hAssigned
  have hh : head < p.heads := hAssigned.2
  have hSources (wait : Nat) (hWait : FirstBiasAcquire l X g wait stage) :
      ∃ tensor : Fin 2 → EvId,
        (∀ half, FirstBiasBox p l X stage g wait (firstVisitBiasBoxColumn half)
          (p.qOffset batch + 128 * base) head half (tensor half)) ∧
        (∀ i (word : Fin 4),
          BiasWordOrder p l X stage false i word g (wait + 1 + 4 * i.val + word.val)
            (tensor (biasVectorHalf i))) := by
    have h := singleVisitFirstBiasSources hp hX hComplete hb hLo hHi
      (by rw [hCoords]; exact hTrip) writes hWait
    simpa only [hCoords] using h
  have hBytes pos (q : Fin 4) vals (he : X.get (g, pos) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l g stage q) vals .s32x32b)⟩) :
      ∀ k < 32, (vals.getD k (b32 0)).bytes = 4 := by
    intro k hk
    rw [List.getD_eq_getElem?_getD, hDots pos q vals he ⟨k, hk⟩, Option.getD_some]
    rfl
  let F := singleVisitRoundFacts p l g warp batch tile biasCap pastTile
  have hBase (i : Fin 16) :
      ((biasReadSite false i).base, b32 (biasVectorBase l g stage false i)) ∈ F := by
    simp only [F, singleVisitRoundFacts, List.mem_append]
    exact .inl (.inl (.inl (.inr (List.mem_map_of_mem (List.mem_finRange i)))))
  have hFrame (x : Nat × Value) (hx : x ∈ F) :=
    singleVisitFrameKeeps p l g warp batch tile biasCap pastTile (List.mem_map_of_mem hx)
  obtain ⟨qkFails, biasFails, u, scores, _, _, hu, hScores, hBias, hRun⟩ :=
    firstQkBiasInputsOfBoxes hp hX writes stage (row := p.qOffset batch + 128 * base)
      firstVisitBiasBoxColumn firstVisitBiasBoxColumnBounds hh ht
      (by simp [singleVisitRoundFacts, stage]) (by simp [singleVisitRoundFacts, stage])
      (by simp [singleVisitRoundFacts]) (by simp [singleVisitRoundFacts, stage])
      (by simp [singleVisitRoundFacts, stage]) (fun x hx => (hFrame x hx).1)
      (fun x hx => (hFrame x hx).2) hBytes hBase hSources hr
  have hUnpacked := firstVisitBiasUnpackedOfBoxes (fun i => (hBias i).2)
  have hTile : row < 256 * (tile + 1) := by
    have hs := stage.isLt
    have hl := Nat.mod_lt (g % l.block) (by decide : 0 < 128)
    dsimp [row, base]
    omega
  have hLive col (hc : col < 128) (hKey : visitKey 1 0 col < p.keyCount batch row) :
      let bc := p.biasColumn batch row (visitKey 1 0 col)
      0 ≤ bc ∧ bc < 1280 ∧ bias col = p.bias (p.qOffset batch + row) head bc.toNat := by
    simpa only [hTrip] using
      (firstVisitLiveBiasValue hp hb hRow hTile hc (by simpa only [hTrip] using hKey))
  have hKeep {G : List (Nat × Value)} (hSub : ∀ rv ∈ G, rv ∈ F) : Holds u.regs G := by
    induction G with
    | nil => trivial
    | cons rv rest ih =>
      exact ⟨holds_mem hu.2.2.2.2 (hSub rv (List.mem_cons_self ..)),
        ih (fun v hv => hSub v (List.mem_cons_of_mem _ hv))⟩
  have hWords (q : Fin 4) (word : Fin 32) := hDots _ q (scores q) (hScores.1 q).2 word
  refine ⟨qkFails, biasFails, ?_⟩
  exact firstRoundFromFenceOperands hp warp (blocks := 1) (base := base) bias hb hh hRow
    (by simp) (hu.mono (hKeep (fun x hx => by simp [F, singleVisitRoundFacts, hx])))
    (hKeep (fun _ hx => by
      apply List.mem_append_left
      apply List.mem_append_right
      exact hx)) hScores hWords hUnpacked hLive
    (hKeep (fun x hx => by simp [F, singleVisitRoundFacts, hx]))
    (holds_mem hu.2.2.2.2 (by simp [singleVisitRoundFacts])) hRun

end
end PTX.Kernels.TmlFa4Fwd.Softmax
