-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvPred

@[expose] public section

/-!
# The softmax region's iteration invariant along a thread of an execution

`sv_inv_at`: at every state of the softmax region a followed thread of a valid row is in
(`St Q L X g k = .d (.sm d)`), `SvInv` holds: by induction along the trace, from the region's first
state (`SvInv.init`) through `SvInv.step` at every event and `SvInv.pair` at the second shuffle of
the stage. The premises are:

* `SvPrem.score`: the S tile's load returns the exact scores of the keys of the thread's half
  (`Spec.score`): the protocol layer's `ReadSource` of the last QK MMA with `Mma.score_load`;
* `SvPrem.exch`: **the exchange with the partner lane**: for the two shuffle events of one iteration
  the partner lane's state has the thread's entry numbers and running maximum, returned its row
  maximum and its sum of probabilities (`Sm.PeerExchange`), and its visible scores are the other
  half's. The protocol layer supplies it;
* `hB`: the row's block in key order has the two halves' visible logits as its scores;
* the row is a valid row.

`sm_exit_corr`: the region's state that hands over to the epilogue holds the running maximum and
sum of all the row's blocks and the launch's scale.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000
open Classical

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The thread's tile row is a row of a valid query token of its request. -/
def ValidRow (Q : Params) (L : Launch) (g : Nat) : Prop :=
  row (g % L.block) < 60 ∧ tokOf (g % L.block) < Q.qLen (ProA.cta L g .z)

/-- **What the protocol layer supplies to the softmax region's iteration invariant.** -/
structure SvPrem (Q : Params) (L : Launch) (X : Execution) : Prop where
  /-- The S tile's load returns the exact scores. -/
  score : ∀ {g k : Nat} {d : D} {e : Event}, g < L.threads → ValidRow Q L g →
    X.get (g, k) = some e → St Q L X g k = some (some (.d (.sm d))) → d.site = .ldS →
    ScoreEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d.i e
  /-- The exchange with the partner lane. -/
  exch : ∀ {g k : Nat} {d : D} {e5 e6 : Event}, g < L.threads → ValidRow Q L g →
    X.get (g, k) = some e5 → X.get (g, k + 1) = some e6 →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 →
    ExchEv Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) (g % L.block) d e5 e6
  /-- The exchange of the row maximum receives score words (`Interface.Lk.SmMaxOk`). -/
  real : ∀ {g k : Nat} {d : D} {e : Event}, g < L.threads → X.get (g, k) = some e →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .shfl5 →
    ∀ m av bv cv r o, e.kind = .shfl m av bv cv r o → d.RealIn r

/-- The invariant of the softmax region's state before an event. -/
theorem sm_inv_at (hX : Consistent L kernel Interface.asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    {k : Nat} {d : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) : Sm.Inv L g d := by
  obtain ⟨t, ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX he hσ
  exact hinv.2

/-- The entry numbers the prologue leaves are the launch's. -/
theorem entFull_entOf (Q : Params) (L : Launch) (g : Nat) (dt : ProA.Dat) :
    EntFull Q (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y)
      (SmEntry.entOf Q L g dt) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem rowValid_of {Q : Params} {r s kvh : Nat} {e : Ent} (h : EntFull Q r s kvh e) {T : Nat}
    (hv : row T < 60 ∧ tokOf T < Q.qLen r) : rowValid e T = true := by
  unfold rowValid
  rw [h.qlen]
  simpa using hv

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel Interface.asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (P : SvPrem Q L X) (hg : g < L.threads) (hvr : ValidRow Q L g)
    {B : Nat → List (ℝ × ℝ)}
    (hB : ∀ b, b < Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) → (B b).map Prod.fst =
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 0 ++
      halfScores Q (ProA.cta L g .z) (ProA.cta L g .x) (tokOf (g % L.block))
        (ProA.cta L g .y * 6 + remOf (g % L.block)) b 1)
include hpre hX hf P hg hvr hB

/-- **The iteration invariant along a thread.** -/
theorem sv_inv_at :
    ∀ (k : Nat) (d : D), k ≤ (X.tr g).length → St Q L X g k = some (some (.d (.sm d))) →
      SvInv Q L g (ProA.cta L g .z) (ProA.cta L g .x) (ProA.cta L g .y) B d := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro d hk hσ
    rcases pred_sm hk hσ with ⟨dt, rfl⟩ | ⟨k0, d0, e, rfl, he, hσ0, hn⟩
    · exact SvInv.init (entFull_entOf Q L g dt)
    · have hk0 : k0 < (X.tr g).length := by omega
      have he' : X.get (g, k0) = some e := he
      have hI0 := sm_inv_at hX hf he' hσ0
      by_cases h6 : d0.site = .shfl6
      · rcases pred_sm (by omega) hσ0 with ⟨dt, rfl⟩ | ⟨k1, d1, e1, rfl, he1, hσ1, hn1⟩
        · simp [SmEntry.d0] at h6
        · have hs5 := prev_shfl6 hn1 h6
          have he1' : X.get (g, k1) = some e1 := he1
          have h1 := ih k1 (by omega) d1 (by omega) hσ1
          have hI1 := sm_inv_at hX hf he1' hσ1
          exact SvInv.pair hI1 h1 hs5 hB (P.exch hg hvr he1' he' hσ1 hs5) (P.real hg he1' hσ1 hs5)
            hn1 hn
      · have h0 := ih k0 (by omega) d0 (by omega) hσ0
        have hv := rowValid_of h0.ent hvr
        have hev := evOk_of hpre hX hf hg he' hσ0 hI0
          (fun hs => P.score hg hvr he' hσ0 hs)
        exact SvInv.step hI0 hv h0 h6 hev hn

omit hpre hX hf P hg hvr hB in
/-- The event that ends the loop is one of the sites `LeaveSite` names. -/
theorem leaveSite_of_leaves {d : D} {e : Event} (h : DComp.leaves L g d e) : LeaveSite d := by
  unfold DComp.leaves at h
  cases hs : d.site <;> rw [hs] at h <;> simp only [LeaveSite] at *
  · exact Or.inl ⟨hs, h.2⟩
  · rename_i j
    exact Or.inr (Or.inl ⟨j, hs, h.2.2⟩)
  · exact Or.inr (Or.inr ⟨Or.inl hs, h.2⟩)
  · exact Or.inr (Or.inr ⟨Or.inr hs, h.2⟩)

/-- **The region's state that hands over to the epilogue.** The softmax state before the event
that ends the loop (the state before the epilogue's first) holds the launch's scale and the
running maximum and sum of all the row's blocks. -/
theorem sm_exit_corr (hnI : Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 31) {k : Nat}
    {dsm : D} {d : Epi.D} (hσ : St Q L X g k = some (some (.d (.sm dsm))))
    (hσ' : St Q L X g (k + 1) = some (some (.d (.epi d)))) :
    dsm.e.sc = Q.scale ∧ Corr (slQ Q)
      ((List.range (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))).map B) dsm := by
  have hk : k < (X.tr g).length := by
    by_contra hh
    have h1 : Frame.stateAt (code L Q) X g (k + 1) = Frame.stateAt (code L Q) X g k := by
      rw [Frame.stateAt_of_le (by omega : (X.tr g).length ≤ k + 1),
        Frame.stateAt_of_le (by omega : (X.tr g).length ≤ k)]
    have h2 : St Q L X g (k + 1) = St Q L X g k := h1
    rw [h2, hσ] at hσ'
    cases Option.some.inj (Option.some.inj hσ')
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  have he' : X.get (g, k) = some e := he
  have hSv := sv_inv_at hpre hX hf P hg hvr hB k dsm (by omega) hσ
  have hI := sm_inv_at hX hf he' hσ
  have hs' := hσ'
  rw [St, Frame.stateAt_succ he] at hs'
  have hs0 : Frame.stateAt (code L Q) X g k = some (some (.d (.sm dsm))) := hσ
  rw [hs0] at hs'
  have hn : (threadCode L g Q).next (.d (.sm dsm)) e = some (some (.d (.epi d))) := hs'
  rw [next_d] at hn
  obtain ⟨a, ha, h⟩ := map_map_eq_some_some hn
  cases h
  change DComp.smNext L g dsm e = _ at ha
  unfold DComp.smNext at ha
  split at ha
  · rename_i hl
    exact ⟨hSv.ent.sc, hSv.exit_corr hI hnI (leaveSite_of_leaves hl)⟩
  · obtain ⟨a', -, hs⟩ := map_map_eq_some_some ha
    cases hs

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
