-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Lag
public import Kernels.TmlFa4Fwd.Proof.Correction.Ref
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Lib.CorrGood
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The counts and the time of a correction lane at a poll

`corr_fw_at`: at the O and free polls of the final stage; `corr_wend_at`: at the last free poll. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {d : Correction.Control.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length =
    some (some (.inr ⟨.correction, d⟩, n)))
include hp hX hFw hub hg hσ

/-- The reference at the end of the trace. -/
theorem corr_end : (8 ≤ Prologue.warpIndex L g ∧ Prologue.warpIndex L g ≤ 11) ∧
    ∃ r ℓ, RefQ p L g d (CorrWarp.rc n) r ℓ ∧ CorrWarp.CFits p L g d (n .shfl) (n .vote) ∧
      (∀ o, okPolls (obj L g o) (X.tr g) = CorrWarp.rc n (.acquire o)) ∧
      ∀ o, arrivals (obj L g o) (X.tr g) = CorrWarp.rc n (.arrive o) := by
  have hJ := (goodR hp hX hFw hg _).2 _ hσ
  obtain ⟨h1, h2, -⟩ := JR.correction hJ (Prologue.warpIndex_lt hp g)
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := (corr_good hp hX hFw ⟨h1, h2⟩ hg _).2 _ hσ hub0
  refine ⟨⟨h1, h2⟩, r, ℓ, hQ, hF, fun o => ?_, fun o => ?_⟩
  · have := corr_okPolls (L := L) (X := X) (g := g) (k := (X.tr g).length) (o := o)
    rw [List.take_length] at this
    rw [this]
    have := count hσ (.corr (.acquire o))
    rwa [List.take_length] at this
  · have := corr_arrivals (L := L) (X := X) (g := g) (k := (X.tr g).length) (o := o)
    rw [List.take_length] at this
    rw [this]
    have := count hσ (.corr (.arrive o))
    rwa [List.take_length] at this

/-- **A correction lane at an O or a free poll of the final stage.** -/
theorem corr_fw_at {st k : Fin 2} (hs : d.scheduler.site = .fw st k) :
    ∃ R, CorrRounds p L g R ∧ n (.corr (.nb st)) = R + 2 ∧
      okPolls (obj L g (Correction.pollOff d.scheduler.site)) (X.tr g) = 0 ∧
      arrivals (obj L g (208 + 8 * st.val)) (X.tr g) = 0 := by
  obtain ⟨-, r, ℓ, hQ, hF, hok, harr⟩ := corr_end hp hX hFw hub hg hσ
  have ht := hQ.tail (by
    have h : ∀ st k : Fin 2, Correction.tailR (.fw st k) = true := by decide
    rw [hs]; exact h st k)
  have hep : CorrWarp.epi d.scheduler.site = .ready 0 := by rw [hs]; rfl
  obtain ⟨rv, -, -, hFE, hu⟩ := hF
  simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  have hb := CorrWarp.bs_ref hC h0 h1 (hu (by
    have h : ∀ st k : Fin 2, (Correction.Site.fw st k).hasUk = true := by decide
    rw [hs]; exact h st k))
  have hR : CorrRounds p L g ((Correction.Bs p L g d.scheduler.v).toNat - 1) :=
    ⟨R, bal, hC.1, by rw [hb]; rfl⟩
  have hr : (Correction.Bs p L g d.scheduler.v).toNat - 1 = r := by omega
  have tab : ∀ st k : Fin 2, ((ptsOf (.nb st)).countP (before (.fw st k)) = 2 ∧
      (ptsOf (.nb st)).countP inRound = 1) ∧
      ((ptsOf (.acquire (Correction.pollOff (.fw st k)))).countP (before (.fw st k)) = 0 ∧
        (ptsOf (.acquire (Correction.pollOff (.fw st k)))).countP inRound = 0) ∧
      (ptsOf (.arrive (208 + 8 * st.val))).countP (before (.fw st k)) = 0 ∧
        (ptsOf (.arrive (208 + 8 * st.val))).countP inRound = 0 := by decide
  obtain ⟨⟨t1, t2⟩, ⟨t3, t4⟩, t5, t6⟩ := tab st k
  have c1 := hQ.cnt (.nb st) (by simp)
  have c2 := hQ.cnt (.acquire (Correction.pollOff d.scheduler.site)) (by simp)
  have c3 := hQ.cnt (.arrive (208 + 8 * st.val)) (by simp)
  rw [hs] at c1 c2 c3
  simp only [passed, t1, t2, t3, t4, t5, t6] at c1 c2 c3
  refine ⟨_, hR, ?_, ?_, ?_⟩
  · change n (.corr (.nb st)) = _ at c1
    rw [c1, hr]; omega
  · rw [hok, hs, c2]; omega
  · rw [harr, c3]; omega

/-- **A correction lane at the last free poll.** -/
theorem corr_wend_at {l : Bool} (hs : d.scheduler.site = .wend l) :
    okPolls (obj L g 232) (X.tr g) = (if l then 1 else 0) ∧
      (l = false → arrivals (obj L g 216) (X.tr g) = 0) ∧
      (l = true → ∃ R, CorrRounds p L g R) := by
  obtain ⟨hw, r, ℓ, hQ, hF, hok, harr⟩ := corr_end hp hX hFw hub hg hσ
  have tab : ∀ l : Bool, ((ptsOf (.acquire 232)).countP (before (.wend l)) =
      (if l then 1 else 0) ∧ (ptsOf (.acquire 232)).countP inRound = 0) ∧
      (ptsOf (.arrive 216)).countP (before (.wend l)) = (if l then 1 else 0) ∧
        (ptsOf (.arrive 216)).countP inRound = 0 := by decide
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := tab l
  have c2 := hQ.cnt (.acquire 232) (by simp)
  have c3 := hQ.cnt (.arrive 216) (by simp)
  rw [hs] at c2 c3
  rw [passed, t3, t4, Nat.mul_zero, Nat.add_zero] at c3
  refine ⟨?_, fun hl => ?_, fun hl => ?_⟩
  · rw [hok, c2, passed, t1, t2]; omega
  · rw [harr, c3, hl]; rfl
  · obtain ⟨R, hR, -⟩ := corr_late_rounds hp hX hFw hw.1 hw.2 0 (k := (X.tr g).length) (by
      rw [List.take_length, harr, c3, hl]; rfl)
    exact ⟨R, hR⟩

end

/-- **The barrier a correction lane's poll event is on**, and the offsets. -/
theorem corr_wait_loc {d : Correction.Control.D} {n : Cls → Nat} {pc q : Nat} {l : Loc}
    {ok acq : Bool}
    {sc : MbarScope}
    (hev : TEv p L g (.inr ⟨.correction, d⟩, n) ⟨pc, .wait l q ok acq sc⟩) :
    l = obj L g (Correction.pollOff d.scheduler.site) ∧
      ((∃ st : Fin 2, ∃ k : Fin 2, d.scheduler.site = .fw st k ∧
        Correction.pollOff d.scheduler.site = 144 + 8 * st.val + 80 * k.val) ∨
        (∃ b, d.scheduler.site = .wend b) ∧ Correction.pollOff d.scheduler.site = 232) := by
  have hevC := hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,hh⟩; cases hh)
  rcases corr_mbar2 hevC (l := l) rfl with ⟨hk, -⟩ | ⟨_, _, hk, hl, hmem⟩
  · cases hk
  · refine ⟨hl, ?_⟩
    obtain ⟨-, hs⟩ := corr_poll_par hevC rfl
    rcases hs with ⟨st, j, hs⟩ | ⟨b, hs⟩
    · left
      refine ⟨st, j, hs, ?_⟩
      have h : ∀ st j : Fin 2, Correction.pollOff (.fw st j) = 144 + 8 * st.val + 80 * j.val := by
        decide
      rw [hs]; exact h st j
    · right
      exact ⟨⟨b, hs⟩, by rw [hs]; rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof
