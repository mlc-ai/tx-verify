-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mbar
public import Kernels.TmlFa4Fwd.Proof.Lib.LdKvWait
public import Kernels.TmlFa4Fwd.Proof.Loader.Export.BiasLag
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.ElectNum
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A loader lane at a wait of a TMA group or the drain's Q wait

`ld_tma_wait`: the wait's barrier is the empty one of a Q or Bias stage, after as many elections at
the group's arrival site as successful polls; the poll is the lane's first, or the Bias group of a
warm round or the last (in the slot of the softmax round whose releases it waits for), or the
drain's wait. `tma_copy_ord`: at a tensor copy the lane's elections are its polls. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem tmaOff_mem {o : Nat} (ho : LdTmaOff o) : o ∈ [0, 8, 320, 328] := by
  rcases ho with rfl | rfl | rfl | rfl <;> simp

/-- **At a tensor copy a lane's elections are its polls.** -/
theorem tma_copy_ord (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14) {o : Nat} (ho : LdTmaOff o)
    {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩) (hm : sp.mbar = obj L g o) :
    ElectOrd.siteOrdinal (Loader.arrPcs o) X g k =
      okPolls (obj L g (o + 16)) ((X.tr g).take k) := by
  have hg := Frame.lt_of_get hX he
  rcases LdWarp.open_ev hp hX hFw (.inl hw) he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := obj L g o) hm
    cases hc
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, -⟩ := hJl.refE
  have hs : Loader.budArr d.site o = 0 := by
    cases ld_use (l := obj L g o) hp hRing hev hm with
    | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | arrive _ _ _ _ hk
    | ta _ _ _ _ hk | da _ _ _ hk => cases hk
    | tc t c a' s hs hl hk hb' => rw [hs]; rfl
  have h1 := Loader.elect_num hp hX hg hw hσ h0 (tmaOff_mem ho)
  have h2 : okPolls (obj L g (o + 16)) ((X.tr g).take k) =
      n (.load (.acquire (obj L g (o + 16)))) := count hσ (.load (.acquire (obj L g (o + 16))))
  rw [hs] at h1
  rw [h2]
  exact h1

/-- **A tensor copy on a Bias barrier is of one of the tile's groups**: the lane's polls of the
empty barrier are at most them. -/
theorem bias_copy_le (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14) {st : Bool}
    {pc a : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue a sp⟩)
    (hm : sp.mbar = obj L g (Loader.fOff st)) :
    ∃ R bal, Epilogue.Picked p L g R bal ∧
      okPolls (obj L g (Loader.fOff st + 16)) ((X.tr g).take k) ≤
        Loader.biasPick p L g R bal st := by
  have hg := Frame.lt_of_get hX he
  rcases LdWarp.open_ev hp hX hFw (.inl hw) he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := obj L g (Loader.fOff st)) hm
    cases hc
  obtain ⟨hJl, hF⟩ := hR.2 h0
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, -⟩ := hJl.refE
  have hs : d.site.blk = true := by
    cases ld_use (l := obj L g (Loader.fOff st)) hp hRing hev hm with
    | slot _ _ _ _ _ hk | tw _ _ _ _ hk | dw _ _ _ _ hk | dq _ _ _ hk | arrive _ _ _ _ hk
    | ta _ _ _ _ hk | da _ _ _ hk => cases hk
    | tc t c a' s hs hl hk hb' => rw [hs]; rfl
  obtain ⟨R, bal, hP, hle⟩ := Loader.bias_le hp hX hg hw hσ h0 hF hs st
  refine ⟨R, bal, hP, ?_⟩
  have h2 : okPolls (obj L g (Loader.fOff st + 16)) ((X.tr g).take k) =
      n (.load (.acquire (obj L g (Loader.fOff st + 16)))) :=
    count hσ (.load (.acquire (obj L g (Loader.fOff st + 16))))
  have hn : Loader.nE L g st = .acquire (obj L g (Loader.fOff st + 16)) := by cases st <;> rfl
  rw [h2, ← hn]
  exact hle

/-- What a wait of a TMA group or the drain's Q wait polls. -/
structure TmaWait (p : Params) (L : Launch) (X : Execution) (g t o K : Nat) : Prop where
  off : LdTmaOff o
  ok : okPolls (obj L g (o + 16)) (X.tr g) = K
  ord : ElectOrd.siteOrdinal (Loader.arrPcs o) X g (X.tr g).length = K
  late : K = 0 ∨ ∃ R bal, Epilogue.Picked p L g R bal ∧
    ((∃ st v, o = Loader.fOff st ∧ K = v + 1 ∧ v + 1 < Loader.biasPick p L g R bal st ∧
        Progress.clk p (Progress.slotOf p v) Progress.bandL ≤ t) ∨
      (o = 8 ∧ K = 1 ∧ Progress.doneBase p ≤ t))

/-- A loader state at a wait of a TMA group or the drain's Q wait. -/
def tmaWaitSite : Loader.Site → Bool
  | .tw _ | .dq => true
  | _ => false

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {b : Bool} {d : Loader.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
include hp hX hFw hub hg hσ

/-- **A loader lane at a wait of a TMA group or the drain's Q wait.** -/
theorem ld_tma_wait (hs : tmaWaitSite d.site = true) :
    Prologue.warpIndex L g = 14 ∧
    ∃ o K, TmaWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) o K ∧
      ∀ {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope},
        TEv p L g (.inr ⟨.loader b, d⟩, n) ⟨pc, .wait l q ok acq sc⟩ → l = obj L g (o + 16) := by
  have hJ := (goodR hp hX hFw hg _).2 _ hσ
  obtain ⟨hw, hwb, hR⟩ := JR.loader hJ
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨hJl, hF⟩ := hR hub0
  obtain ⟨kk, A, hRing, hCnt⟩ := hJl.refE
  have htma : d.site.isTma = true := by
    revert hs
    cases d.site <;> simp [tmaWaitSite, Loader.Site.isTma]
  have h14 : Prologue.warpIndex L g = 14 := hRing.tma htma
  rw [← hwb] at hRing
  refine ⟨h14, ?_⟩
  have hok : ∀ o, okPolls (obj L g (o + 16)) (X.tr g) =
      n (.load (.acquire (obj L g (o + 16)))) := fun o => by
    have := count hσ (.load (.acquire (obj L g (o + 16))))
    rw [List.take_length] at this
    exact this
  have hel := fun o (ho : o ∈ [0, 8, 320, 328]) =>
    Loader.elect_num hp hX hg h14 hσ hub0 (o := o) ho
  have hbn := Loader.bias_num hp hX hg h14 hσ hub0
  have hsp := Loader.su_pick hp hX hg hw hσ hub0
  have hqa := Loader.q_acq hp hX hg hw hσ hub0
  have hloc : ∀ (o : Nat), Loader.twOff 0 = 16 → ((∃ t, d.site = .tw t ∧ Loader.twOff t = o + 16) ∨
      d.site = .dq ∧ o = 8) →
      ∀ {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope},
        TEv p L g (.inr ⟨.loader b, d⟩, n) ⟨pc, .wait l q ok acq sc⟩ → l = obj L g (o + 16) := by
    intro o _ hso pc q l ok acq sc hev
    cases ld_use (l := l) hp hRing hev rfl with
    | slot _ _ _ hs' _ _ => rw [hs'] at hs; cases hs
    | dw _ _ hs' _ _ => rw [hs'] at hs; cases hs
    | tw t _ hs' hl _ =>
      rcases hso with ⟨t', hs'', ht⟩ | ⟨hs'', -⟩
      · rw [hs'] at hs''; cases hs''; rw [hl, ht]
      · rw [hs'] at hs''; cases hs''
    | dq _ hs' hl _ =>
      rcases hso with ⟨t', hs'', ht⟩ | ⟨hs'', rfl⟩
      · rw [hs'] at hs''; cases hs''
      · exact hl
    | arrive _ _ hs' | ta _ _ hs' | da _ hs' | tc _ _ _ _ hs' => rw [hs'] at hs; cases hs
  have hbudT : ∀ t o, Loader.budArr (.tw t) o = 0 := fun _ _ => rfl
  cases hsite : d.site <;> rw [hsite] at hs htma <;>
    simp only [tmaWaitSite, Bool.false_eq_true] at hs
  case dq =>
    refine ⟨8, _, ⟨by unfold LdTmaOff; omega, rfl, ?_, ?_⟩, hloc 8 rfl (.inr ⟨hsite, rfl⟩)⟩
    · have := hel 8 (by simp)
      rw [hsite] at this
      rw [hok 8]
      exact this
    · rw [hok 8]
      have h1 := hqa 24 (by simp)
      simp only [hsite, Loader.qAcq, hwb, h14, ↓reduceIte, LdWarp.lcn] at h1
      by_cases h0 : n (.load .commit) = 0
      · rw [ite_eq_left h0] at h1
        exact .inl h1
      · rw [ite_eq_right h0] at h1
        right
        simp only [Loader.LFits, hsite, Loader.lc] at hF
        obtain ⟨l, -, -, hl, hl'⟩ := hF
        cases l with
        | false => exact absurd (hl' rfl) h0
        | true =>
          obtain ⟨⟨R, bal, hP, -⟩, -⟩ := hl rfl
          refine ⟨R, bal, hP, .inr ⟨rfl, h1, ?_⟩⟩
          simp only [Progress.time, Progress.roleTime, Progress.Ld.time, hsite]
          omega
  case tw t =>
    have hblk : d.site.blk = true := by rw [hsite]; rfl
    obtain ⟨-, -, ⟨R, bal, hP, h28⟩, ⟨-, hRd⟩, -⟩ := Loader.lfits_blk_of hblk hF
    have hS : Loader.SuS p L g d.v := hsp.1 (.inl (Loader.lc_blk.mpr hblk))
    have hel0 : ∀ o ∈ [0, 8, 320, 328], ElectOrd.siteOrdinal (Loader.arrPcs o) X g
        (X.tr g).length = n (.load (.acquire (obj L g (o + 16)))) := fun o ho => by
      have := hel o ho
      rw [hsite, hbudT] at this
      exact this
    -- a Bias group
    have hB : ∀ st : Bool, Loader.twOff t = Loader.fOff st + 16 →
        (∃ c, Loader.biasForm st (.tw t) = some (false, c) ∧ c = 0) ∨
        (Loader.biasForm st (.tw t) = some (true, -1) ∧ 4 ≤ t.val ∧ t.val < 6) ∨
        (Loader.biasForm st (.tw t) = some (true, 0) ∧ t.val = 6 ∧ st = false) →
        ∃ o K, TmaWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) o K ∧
          ∀ {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope},
            TEv p L g (.inr ⟨.loader b, d⟩, n) ⟨pc, .wait l q ok acq sc⟩ →
              l = obj L g (o + 16) := by
      intro st ht hf
      have hmem : Loader.fOff st ∈ [0, 8, 320, 328] := by cases st <;> simp
      refine ⟨Loader.fOff st, _, ⟨by cases st <;> simp [LdTmaOff], rfl, ?_, ?_⟩,
        hloc _ rfl (.inl ⟨t, hsite, ht⟩)⟩
      · rw [hok, hel0 _ hmem]
      · rw [hok]
        obtain ⟨q1, q2, q3, -⟩ := hbn st
        have hn : Loader.nE L g st = .acquire (obj L g (Loader.fOff st + 16)) := by
          cases st <;> rfl
        simp only [hsite, LdWarp.lcn, hn] at q1 q2 q3
        have hpk := hS.pick hP st
        rcases hf with ⟨c, hf, rfl⟩ | ⟨hf, h4, h6⟩ | ⟨hf, h6, rfl⟩
        · left
          have := q1 _ hf
          omega
        · right
          have hk' := q2 _ hf
          rw [hsite] at hRd
          simp only [Loader.bc, Loader.inBlk, show ¬ t.val < 4 by omega, h6, ↓reduceIte,
            Loader.RoundsB] at hRd
          obtain ⟨r, -, h2, hr, hnc⟩ := hRd
          refine ⟨R, bal, hP, .inl ⟨st, r, rfl, by omega, ?_, ?_⟩⟩
          · rw [← hpk, Loader.biasTot, Loader.w0_of h2]
            omega
          · simp only [Progress.time, Progress.roleTime, Progress.Ld.time, hsite,
              show ¬ t.val < 4 by omega, h6, ↓reduceIte, Progress.Ld.slot, Progress.Ld.idx,
              Nat.sub_zero]
            rw [hnc, show (2 + 2 * r + 1 - 2) / 2 = r by omega]
            unfold Progress.clk; omega
        · right
          have hk' := q2 _ hf
          rw [hsite] at hRd
          simp only [Loader.bc, Loader.inBlk, show ¬ t.val < 4 by omega, show ¬ t.val < 6 by omega,
            ↓reduceIte, Loader.RoundsB] at hRd
          obtain ⟨-, h2, hnc⟩ := hRd
          have hL := q3 (by simp [Loader.Site.lastGrp, h6])
          refine ⟨R, bal, hP, .inl ⟨false, Loader.wRn d.v.su.r28, rfl, by omega, ?_, ?_⟩⟩
          · rw [← hpk, Loader.biasTot, Loader.w0_of h2]
            simp [hL]
          · simp only [Progress.time, Progress.roleTime, Progress.Ld.time, hsite,
              show ¬ t.val < 4 by omega, show ¬ t.val < 6 by omega, ↓reduceIte, Progress.Ld.slot,
              Progress.Ld.idx, Nat.sub_zero]
            rw [hnc, show (2 + 2 * Loader.wRn d.v.su.r28 + 0 - 2) / 2 =
              Loader.wRn d.v.su.r28 by omega]
            unfold Progress.clk; omega
    -- a Q group
    have hQ : ∀ o, LdTmaOff o → Loader.twOff t = o + 16 → o + 16 ∈ [16, 24] →
        Loader.qAcq 14 (.tw t) 0 (o + 16) = 0 → t.val < 4 →
        ∃ o K, TmaWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) o K ∧
          ∀ {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope},
            TEv p L g (.inr ⟨.loader b, d⟩, n) ⟨pc, .wait l q ok acq sc⟩ →
              l = obj L g (o + 16) := by
      intro o ho ht hm hq h4
      refine ⟨o, _, ⟨ho, rfl, ?_, .inl ?_⟩, hloc _ rfl (.inl ⟨t, hsite, ht⟩)⟩
      · rw [hok, hel0 _ (tmaOff_mem ho)]
      · rw [hok]
        have h1 := hqa _ hm
        simp only [hsite, hwb, h14, LdWarp.lcn] at h1
        exact h1.trans hq
    fin_cases t
    · exact hQ 0 (by simp [LdTmaOff]) rfl (by simp) rfl (by decide)
    · exact hB false rfl (.inl ⟨0, rfl, rfl⟩)
    · exact hQ 8 (by simp [LdTmaOff]) rfl (by simp) rfl (by decide)
    · exact hB true rfl (.inl ⟨0, rfl, rfl⟩)
    · exact hB false rfl (.inr (.inl ⟨rfl, by decide, by decide⟩))
    · exact hB true rfl (.inr (.inl ⟨rfl, by decide, by decide⟩))
    · exact hB false rfl (.inr (.inr ⟨rfl, rfl, rfl⟩))

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
