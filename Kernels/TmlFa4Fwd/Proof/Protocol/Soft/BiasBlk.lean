-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Tma
import Kernels.TmlFa4Fwd.Proof.Loader.Export.BiasLag
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Coll
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Kernels.TmlFa4Fwd.Proof.Protocol.Bias.Lanes
import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Winner
import Kernels.TmlFa4Fwd.Proof.Protocol.Ld.TmaBlk
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.BiasPoll
import Lemmas.Protocol.KindRingLane
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Progress at the softmax lanes' Bias-full polls

`bias_lag`: a blocked Bias-full poll of any of the stage's lanes has an open tensor copy, or the
electing lane of warp 14 short of the round's group, before the round's slot. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MbarRing

noncomputable section
set_option maxRecDepth 20000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Bias full**, every lane of the stage. -/
theorem bF_lane (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hB : TmaBytes X) {st : Fin 2}
    {h : Nat} (hh : SoftIn L g st.val h) {f : MBarrier.State} (hst : Final X (bF L g st) f)
    (hpar : f.phase % 2 = okPolls (bF L g st) (X.tr h) % 2) :
    f.phase = okPolls (bF L g st) (X.tr h) ∧
      (Descent.Obl L X .tensor ∨ arrivals (bF L g st) (X.tr (tmaLane L X g)) ≤ f.phase ∨
        (X.tr (tmaLane L X g)).countP (issuesTo (bF L g st)) < 2 * (f.phase + 1)) := by
  have o := tmaFull hp hX hFw hB g (b_tmaOff st)
  have huse : ∀ x ∈ (biasRing hp hX hFw hB g st).SF, x.2 ≤ okPolls (bF L g st) (X.tr h) := by
    intro x hx
    rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
    · omega
    have hpres := Unit.present_of_path (bias_reach hp hX hFw hB hh hx (j := x.2 - 1) (by omega))
    have := Poll.nth_present.mp hpres
    omega
  have hle : f.phase ≤ okPolls (bF L g st) (X.tr h) + 1 :=
    (biasRing hp hX hFw hB g st).F_phase_of hX (κ := {0}) (by simp)
      (by rw [Finset.card_singleton]; exact o.init) o.incr o.one (o.rec_zero (by decide)) huse hst
  have hge : okPolls (bF L g st) (X.tr h) ≤ f.phase + 0 := by
    refine okPolls_le_phase hX (Nat.zero_le 1)
      ((biasRing hp hX hFw hB g st).cF.pclean hX) (biasRing hp hX hFw hB g st).cF.noInval
      (fun k pc q acq sc he => ?_) hst
    obtain ⟨-, hu⟩ := bias_use hp hX hFw st he rfl (fun _ h => by cases h)
    rcases hu with ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, _, _, hk, _⟩
    · simp only [Kind.wait.injEq] at hk
      have h1 : q = okPolls (bF L g st) ((X.tr h).take k) % 2 := hk.2.1
      change q % 2 = (okPolls (bF L g st) ((X.tr h).take k) + 0) % 2
      omega
    · cases hk
    · cases hk
  have hph : f.phase = okPolls (bF L g st) (X.tr h) := by omega
  refine ⟨hph, ?_⟩
  by_cases hob : Descent.Obl L X .tensor
  · exact .inl hob
  · exact .inr (o.short hX (by decide) (hff _) hob hst fun x hx => by
      rw [hph]; exact huse x hx)

/-- **A blocked Bias-full poll has an earlier blocker.** -/
theorem bias_lag (hff : ∀ l, ∀ r ∈ X.objects l, r.fault = none) (hub : ¬ HasUb X)
    (hB : TmaBytes X) (hg : g < L.threads) {d : Softmax.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.softmax, d⟩, n)))
    {r : Bool} (hs : d.scheduler.site = .wb r) {f : MBarrier.State} (hst : Final X (sobj L g 320) f)
    (hpar : f.phase % 2 = okPolls (sobj L g 320) (X.tr g) % 2) :
    Sched.Blk (Progress.timed p L) X g := by
  have hne : X.tr g ≠ [] := by
    intro h0
    rw [show (X.tr g).length = 0 by rw [h0]; rfl, Frame.stateAt_zero] at hσ
    simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
  obtain ⟨hw, -⟩ := soft_end hp hX hFw hub hg hσ
  obtain ⟨B, u, T, hBr, hu, hT, huT, hok, hn80⟩ := soft_bias_at hp hX hFw hub hg hσ hs
  have hst2 : Prologue.warpIndex L g / 4 < 2 := by omega
  have hob : sobj L g 320 = bF L g ⟨_, hst2⟩ := by
    simp only [sobj, bF]; congr 1; omega
  rw [hob] at hst hpar hok
  obtain ⟨hph, hcase⟩ := bF_lane hp hX hFw hff hB (g := g) (h := g)
    (st := ⟨Prologue.warpIndex L g / 4, hst2⟩) ⟨hg, rfl, hw, rfl⟩ hst hpar
  rw [hok] at hph
  rcases hcase with hob' | hshort
  · exact .inl ⟨.tensor, .inr (.inr (.inl rfl)), hob'⟩
  obtain ⟨R, bal, hP, hnB⟩ := id hBr
  obtain ⟨R', hR', hbm⟩ := stage_rounds_bound hp hg hBr
  obtain ⟨z, hzt, hzc, hzw, hwin⟩ := warp_winner hp hX hg (w := 14) (by omega)
  have hPz := Epilogue.Picked.cta hzc.symm hP
  have hrounds := Loader.biasPick_rounds (p := p) (L := L) (y := z) (g := g) hzc R bal
  rw [hnB] at hrounds
  clear hnB
  have hstg : Softmax.stg L g = decide (4 ≤ Prologue.warpIndex L g) := by
    have key : ∀ w < 8, Epilogue.scmpi .gt .s (BitVec.ofNat 64 w) 3 = decide (4 ≤ w) := by decide
    exact key (Prologue.warpIndex L g) hw
  have hoff : obj L z (Loader.fOff (Softmax.stg L g)) = bF L g ⟨_, hst2⟩ := by
    have hF : Loader.fOff (Softmax.stg L g) = 320 + 8 * (Prologue.warpIndex L g / 4) := by
      rw [hstg]
      by_cases h4 : 4 ≤ Prologue.warpIndex L g
      · simp only [Loader.fOff, h4, decide_true, ↓reduceIte]; omega
      · simp only [Loader.fOff, h4, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
    rw [obj_cta hzc, hF]
  have hshort' : arrivals (bF L g ⟨_, hst2⟩) (X.tr z) ≤ u ∨
      (X.tr z).countP (issuesTo (bF L g ⟨_, hst2⟩)) < 2 * (u + 1) := by
    by_cases hz : z = tmaLane L X g
    · rw [hz, ← hph]; exact hshort
    · left
      by_contra hgt
      obtain ⟨e, he, hea⟩ := List.countP_pos_iff.mp
        (show 0 < (X.tr z).countP (arrivesOn (bF L g ⟨_, hst2⟩)) by
          unfold arrivals at hgt; omega)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
      have hget : X.get (z, j) = some ((X.tr z)[j]) := List.getElem?_eq_getElem hj
      generalize (X.tr z)[j] = e at hget hea
      obtain ⟨pc, kd⟩ := e
      cases kd <;> simp [arrivesOn, sourceArrive] at hea
      subst hea
      obtain ⟨-, hu'⟩ := bias_use hp hX hFw (g := g) ⟨_, hst2⟩ hget rfl (fun _ h => by cases h)
      rcases hu' with ⟨_, _, _, hk⟩ | ⟨-, tx, hk⟩ | ⟨_, _, _, hk, _⟩
      · cases hk
      · have hk' : Kind.arrive _ _ _ _ _ = Kind.arrive _ _ _ _ _ := hk
        rw [hk'] at hget
        have hbF : obj L g (320 + 8 * (Prologue.warpIndex L g / 4)) =
            obj L z (320 + 8 * (Prologue.warpIndex L g / 4)) := (obj_cta hzc _).symm
        simp only at hget
        rw [hbF] at hget
        obtain ⟨-, -, -, j', pc', mask, inst, -, hwon⟩ := ld_tma_arr hp hX hFw (.inl hzw)
          (by unfold LdTmaOff; omega) hget
        have := elect_full hX (show X.Elect (z, j') pc' mask inst (laneOf L z) from hwon)
        subst this
        exact hz (tmaLane_eq hX hzc hzw hwon)
      · cases hk
  have hdone := Progress.drain_order p (s := u) (o := 0) (by omega) (by decide)
  obtain ⟨h1, h2⟩ := Loader.bias_lane hp hX hub hzt hzw
    (fun k pc mk inst ld he => hwin k pc mk inst ld he) hPz (u := u)
    (st := Softmax.stg L g) (by omega) hdone.le (by rw [hoff]; exact hshort')
  refine Sched.blk_of_lags hX hub hg hne hσ hzt (by rw [hzc]) fun _ => ⟨h1, h2.trans_le ?_⟩
  change _ ≤ Progress.Sm.time p L g d n
  simp only [Progress.Sm.time, hs, Progress.Sm.place, hn80, ite_true, Nat.add_sub_cancel]
  rw [Progress.slotOf_eq (by omega)]
  unfold Progress.clk
  omega

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
