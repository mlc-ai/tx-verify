-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvSetup

@[expose] public section

/-!
# The update and the two shuffles of the stage

* `SvInv.toBar20`: the edge into the `P` store takes the stage's numbers into the running maximum
  and sum, which are then `Softmax.run` over one block more (`corr_step_stage`);
* `ExchEv`: **the premise on the exchange with the partner lane**, stated on the two shuffle events
  of one iteration: the partner lane's state `dp` has the thread's entry numbers and running
  maximum, the first shuffle returned its row maximum, the second its sum of probabilities
  computed with the thread's maximum (`Sm.PeerExchange`), and its own visible scores are the
  other half's. The protocol layer supplies it (the development notes: "Sv: the exchange with the
  partner");
* `SvInv.pair`: the two shuffles take the invariant from the first to the state after the second:
  the stage's numbers are `Softmax.step`'s (`stage_pair`), and for the first iteration the update
  follows at once.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX.Kernels.InklingRelDecode.Softmax

noncomputable section
open Classical
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {B : Nat → List (ℝ × ℝ)}

/-- **The update at the edge into the `P` store** keeps the invariant: the new running maximum and
sum are `Softmax.run` over one more block. -/
theorem SvInv.toBar20 {x d' : D} (h : SvInv Q L g r s kvh B x) (hs : StageSite x.site)
    (hn : Sm.toBar20 x = some (some d')) : SvInv Q L g r s kvh B d' := by
  unfold Sm.toBar20 at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst hn
    have hx : nDone x = x.i := by
      unfold nDone
      have : ¬ PostSite x.site := by
        revert hs
        cases x.site <;> simp [StageSite, PostSite]
      simp [this]
    have hd : nDone { x.upd with site := .bar20 } = x.i + 1 := by simp [nDone, PostSite, D.upd]
    have hc : Corr (slQ Q) ((List.range x.i).map B) x := by
      have := h.corr
      rwa [hx] at this
    have hst := h.stage hs
    have hcs := corr_step_stage (bs := (List.range x.i).map B) (blk := B x.i) hc rfl hst
    refine ⟨h.ent, ?_, h.wb, h.vb, ?_, ?_, ?_, ?_⟩
    · rw [hd, List.range_succ, List.map_append]
      exact hcs
    · intro hh; cases hh
    · intro hh; cases hh
    · intro hh; simp [StageSite] at hh
    · intro _ k hk
      exact h.pf (Or.inl hs) k hk
  · cases hn

/-- **The premise on the exchange with the partner lane** for the two shuffle events of one
iteration of the thread in state `d` (at the shuffle of the row maximum). -/
def ExchEv (Q : Params) (r s kvh T : Nat) (d : D) (e5 e6 : Event) : Prop :=
  ∀ (m5 : ShflMode) (a5 : Value) (b5 c5 : Nat) (rv : Value) (o5 : Bool)
    (m6 : ShflMode) (a6 : Value) (b6 c6 : Nat) (recv : Value) (o6 : Bool),
    e5.kind = .shfl m5 a5 b5 c5 rv o5 → e6.kind = .shfl m6 a6 b6 c6 recv o6 →
    ∃ y, recv = .float .f32 y ∧ ∃ dp, PeerExchange d dp rv y ∧
      dp.ownScores = halfScores Q r s (tokOf T) (kvh * 6 + remOf T) d.i (1 - Sm.half T)

/-- **The two shuffles of the stage.** From the state at the shuffle of the row maximum, with the
partner's exchange (`ExchEv`), the blocks' scores (`hB`: the key-order block is the two halves'
visible logits) and the iteration inside the split, the state after the second shuffle has the
stage's numbers `Softmax.step`'s; in the first iteration the update follows. -/
theorem SvInv.pair {d d1 d2 : D} {e5 e6 : Event} (hI : Inv L g d)
    (h : SvInv Q L g r s kvh B d) (hs : d.site = .shfl5)
    (hB : ∀ b, b < Q.numIters r s → (B b).map Prod.fst =
      halfScores Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) b 0 ++
      halfScores Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) b 1)
    (hx : ExchEv Q r s kvh (g % L.block) d e5 e6)
    (hR : ∀ m a b c rv o, e5.kind = .shfl m a b c rv o → d.RealIn rv)
    (hn1 : Sm.next L g d e5 = some (some d1)) (hn2 : Sm.next L g d1 e6 = some (some d2)) :
    SvInv Q L g r s kvh B d2 := by
  have hownk := h.own hs
  have hownS : d.ownScores = halfScores Q r s (tokOf (g % L.block))
      (kvh * 6 + remOf (g % L.block)) d.i (Sm.half (g % L.block)) :=
    own_fin (fun k => d.stg.fsv k) hownk
  have hcd : nDone d = d.i := by simp [nDone, PostSite, hs]
  have hc : Corr (slQ Q) ((List.range d.i).map B) d := by
    have := h.corr
    rwa [hcd] at this
  -- unfold the first shuffle
  simp only [Sm.next, hs] at hn1
  split at hn1
  · rename_i m5 a5 b5 c5 rv o5 he5
    split at hn1
    · simp only [Option.some.injEq] at hn1
      subst hn1
      -- the second shuffle
      have hs6 : (d.afterMax rv).site = .shfl6 := rfl
      simp only [Sm.next, hs6] at hn2
      split at hn2
      · rename_i m6 a6 b6 c6 recv o6 he6
        obtain ⟨y, rfl, dp, hxd, hdp⟩ := hx m5 a5 b5 c5 rv o5 m6 a6 b6 c6 recv o6 he5 he6
        split at hn2
        · rename_i v hv
          have hv' : v = .float .f32 ((d.afterMax rv).sumP + y) := by
            have h1 : D.rsOut (d.afterMax rv) (.float .f32 y) =
                .ok (.float .f32 ((d.afterMax rv).sumP + y)) :=
              floatE_add_fin (Sm.valFloat_float _) (Sm.valFloat_float _)
            exact (Except.ok.inj (hv.symm.trans h1))
          subst hv'
          have hsl : slOf d.e = slQ Q := h.ent.sl
          have hlt : d.i < Q.numIters r s := by
            have := (hI.late (by rw [hs]; trivial)).2.2
            have h26 := hI.ok.r26_of_lt this
            rw [h.ent.r25] at h26
            omega
          have hperm : ((B d.i).map Prod.fst).Perm (d.ownScores ++ dp.ownScores) := by
            rw [hB d.i hlt, hownS, hdp]
            rcases Nat.lt_or_ge (Sm.half (g % L.block)) 1 with hh | hh
            · have : Sm.half (g % L.block) = 0 := by omega
              rw [this]
            · have h2 : Sm.half (g % L.block) < 2 := by unfold Sm.half; omega
              have : Sm.half (g % L.block) = 1 := by omega
              rw [this]
              exact List.perm_append_comm
          have hst := stage_pair (d := d) (dp := dp) (rv := rv) (y := y) (sl := slQ Q)
            (bs := (List.range d.i).map B) (blk := B d.i)
            (m := (Softmax.run (slQ Q) ((List.range d.i).map B)).m)
            (l := (Softmax.run (slQ Q) ((List.range d.i).map B)).l)
            (o := (Softmax.run (slQ Q) ((List.range d.i).map B)).o) hsl hc rfl hxd hperm
          have hmu := mUse_stage (d := d) (dp := dp) (rv := rv) (y := y) (sl := slQ Q)
            (bs := (List.range d.i).map B) (blk := B d.i)
            (m := (Softmax.run (slQ Q) ((List.range d.i).map B)).m)
            (l := (Softmax.run (slQ Q) ((List.range d.i).map B)).l)
            (o := (Softmax.run (slQ Q) ((List.range d.i).map B)).o) hsl hc rfl hxd hperm
          have hx2 : SvInv Q L g r s kvh B ((d.afterMax rv).afterSumR y) := by
            refine ⟨h.ent, ?_, h.wb, h.vb, ?_, ?_, ?_, ?_⟩
            · have : nDone ((d.afterMax rv).afterSumR y) = d.i := by
                simp [nDone, PostSite, D.afterSumR, D.afterSum, D.afterMax]
              rw [this]
              exact hc
            · intro hh; cases hh
            · intro hh; cases hh
            · intro _
              exact hst
            · intro _ k hk
              show pOfV (slOf d.e) (d.mUse (eOf rv)) (d.stg.fsv k).1 = _
              have hi : ((d.afterMax rv).afterSumR y).i = d.i := rfl
              rw [hi, hownk k hk, hmu, hsl]
              by_cases hv : visB Q r s (tokOf (g % L.block)) d.i (Sm.half (g % L.block)) k
              · simp only [hv, ↓reduceIte, pOfV]
                congr 1
                ring
              · simp [hv, pOfV, infB, b32]
          split at hn2
          · exact SvInv.toBar20 hx2 trivial hn2
          · simp only [Option.some.injEq] at hn2
            subst hn2
            exact hx2
        · cases hn2
      · cases hn2
    · exact absurd (hR _ _ _ _ _ _ he5) ‹¬ _›
  · cases hn1

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
