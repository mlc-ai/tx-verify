-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.DataReads
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.LseAddr
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Stores
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemRoute
public import Kernels.TmlFa4Fwd.Proof.Correction.FstIs0
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.Correction.FstIs1
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.StoreVals0
import Kernels.TmlFa4Fwd.Proof.Correction.StoreVals1
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The words a correction lane's final and log-sum-exp stores write, from its reads

With the lane's statistics reads and loads what its data machine follows: a final store writes a
loaded element over the row sum the lane read (`corr_fst_data`), and a log-sum-exp store the row's,
from the row sum and the row maximum it read (`corr_lse_data`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem fst_tab (st j hh) : rsPos st (.fst st j hh) = true ∧
    inChunk st j (.fst st j hh) = true := by
  revert st j hh
  decide +kernel

private theorem lse_tab (st) : rsPos st (.lse st) = true ∧ rmPos st (.lse st) = true := by
  revert st
  decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
  (hS : StatTo X g k) (hL : LoadTo X g k)
include hp hX hFw hw hw1 hS hL

/-- The data state of a write. -/
private theorem wr_state {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    ∃ d n, Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction, d⟩, n)) ∧
      Frame.stateAt (thread p L) X g k =
        some (some (CorrWarp.cinj p L g (Control.erase d) n)) ∧ n .ub = 0 ∧
      CorrWarp.CFits p L g (Control.erase d) (n .shfl) (n .vote) ∧
      Ref p L g (d, CorrWarp.rc n) ∧ Control.Ev p L g (Control.erase d) ⟨pc, .wr a bs⟩ ∧
      Recs p L X g k d := by
  have hub : ∀ f, (⟨pc, .wr a bs⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨dc, n, hσ, h0, hR, -, hev, -⟩
  · exact (start_mem hev hi.2 trivial).elim
  obtain ⟨d, hs, rfl, hRd⟩ := corr_alive hp hX hFw hw hw1 hS hL he hσ
  exact ⟨d, n, hs, hσ, h0, (hR h0).2, hRd, hev, data_reads hp hX
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1.le hs⟩

/-- **The word of a final store.** -/
theorem corr_fst_data {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hsh : a.loc.space = .shared) :
    ∃ (st : Fin 2) (j : Fin 16) (hh : Fin 2), ∃ s < 4, ∃ (ys : Nat → ℝ) (rs : ℝ),
      FstIs L g st ⟨2 * (j.val % 4) + hh.val, by omega⟩ (j.val / 4) s a ∧
      bs = (fv (ys (4 * hh.val + s) * fRecip rs)).toBytes ∧
      (∃ i a bs, X.get (g, i) = some ⟨(Site.fsum st).pc, .rd a bs⟩ ∧ rebuild 3 bs = .ok (fv rs)) ∧
      ∃ i ad vals, X.TLd (g, i) ad vals .s32x32b ∧ vals.length = 8 ∧
        (∀ x < 8, vals[x]? = some (fv (ys x))) ∧
        ad % 65536 = 256 + 128 * st.val + 8 * j.val ∧
        ∃ R, CorrRounds p L g R ∧ Tm.pArr L X g st i = R + 1 := by
  obtain ⟨d, n, hs, hσ, h0, hF, -, hev, hRec⟩ := wr_state hp hX hFw hw hw1 hS hL he
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (fun _ => nofun)
  obtain ⟨st, j, hh, hsite⟩ : ∃ st j hh, d.site = .fst st j hh := by
    rcases lse_or_final hev with ⟨hh, hs'⟩ | h
    · exfalso
      obtain ⟨_, _, _, _, _, hal, _⟩ := corr_lse_at hp hX hFw hw hw1 he hσ h0 hF hs'
      rw [hal] at hsh
      cases hsh
    · exact h
  have hfe := fst_exact hp (d := Control.erase d) hat hc hf hsite rfl
  obtain ⟨t', ins', o', hat', -, hc', hf'⟩ :=
    Frame.fired_site (fun g hg => threadD_sound hp hg) hX he hs
  obtain ⟨i1, hi1, a1, bs1, hg1, hv1⟩ := hRec.sum st (by rw [hsite]; exact (fst_tab st j hh).1)
  obtain ⟨i2, hi2, pc2, a2, vals, sh, n2, d2, hg2, hs2, hd2, hy⟩ :=
    hRec.load st j (by rw [hsite]; exact (fst_tab st j hh).2)
  obtain ⟨dc, nc, r, ℓ, hσc, hQ, rfl, st', hst'⟩ :=
    corr_ld_state hp hX hFw hw hw1 (k := i2) ⟨pc2, hg2⟩
  have hdc : dc.site = .fld st j := by
    obtain ⟨d', hd', rfl⟩ := data_of_control hp hs2 hσc
    cases hd'
    exact hd2
  obtain ⟨hcol, hlen⟩ : a2 % 65536 = 256 + 128 * st.val + 8 * j.val ∧ vals.length = 8 := by
    rcases hst' with ⟨c, h, -⟩ | ⟨c, h, h1, h2⟩
    · rw [hdc] at h; cases h
    · rw [hdc] at h; cases h
      exact ⟨h1, h2⟩
  have hne : ∀ f, (⟨pc2, .tc (.ld a2 vals .s32x32b)⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  have hr := corr_rounds hp hX hFw hw hw1 hg2 hne hσc (by rw [hdc]; exact (tail_sites st j).2.1)
    (by rw [hdc]; exact (tail_sites st j).2.2)
  have hrr := hQ.tail (by change tailR dc.site = true; rw [hdc]; exact (tail_sites st j).1)
  refine ⟨st, j, hh, d.k.val, d.k.isLt, d.v.ys, rsOf d.v st, hfe, ?_,
    ⟨i1, a1, bs1, hg1, hv1⟩, i2, a2, vals, ⟨pc2, hg2⟩, hlen, fun x hx => ?_, hcol, _, hr, ?_⟩
  · obtain ⟨site, v, kk⟩ := d
    simp only at hsite
    subst hsite
    fin_cases st
    · exact fst_val0 hat' hc' hf' rfl
    · exact fst_val1 hat' hc' hf' rfl
  · have h0 := flN_get hy hx (.pred false)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at h0
    rw [List.getElem?_eq_getElem (by omega), h0]
  · rw [site_arr hσc hQ (.inr (.inr ⟨j, hdc⟩))]
    omega

/-- **The word of a log-sum-exp store.** -/
theorem corr_lse_data {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hgl : a.loc.space = .global) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧ ∃ (st : Fin 2) (rs : ℝ) (rm : Mx),
        a.loc = p.lseLoc (p.qOffset b + (256 * (Epilogue.assignedCoordinates p b
          (g / L.block)).1 + 128 * st.val + g % L.block % 128))
            (Epilogue.assignedCoordinates p b (g / L.block)).2 ∧
        bs = (lseSel p rs rm).toBytes ∧
        (∃ i a bs, X.get (g, i) = some ⟨(Site.fsum st).pc, .rd a bs⟩ ∧
          rebuild 3 bs = .ok (fv rs)) ∧
        ∃ i a bs, X.get (g, i) = some ⟨(Site.fmax st).pc, .rd a bs⟩ ∧
          rebuild 3 bs = .ok (Assumption.erealValue .f32 rm.1) := by
  obtain ⟨d, n, hs, hσ, h0, hF, hR, hev, hRec⟩ := wr_state hp hX hFw hw hw1 hS hL he
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (fun _ => nofun)
  obtain ⟨st, hsite⟩ : ∃ st, d.site = .lse st := by
    rcases lse_or_final hev with h | ⟨st, j, hh, h⟩
    · exact h
    · obtain ⟨-, q, -, w, -, hloc⟩ := fst_at hp hat hc hf h rfl
      rw [hloc] at hgl
      cases hgl
  obtain ⟨b, hb, hlo, hhi, -, hal, -⟩ := corr_lse_at hp hX hFw hw hw1 he hσ h0 hF hsite
  obtain ⟨t', ins', o', hat', -, hc', hf'⟩ :=
    Frame.fired_site (fun g hg => threadD_sound hp hg) hX he hs
  obtain ⟨i1, -, a1, bs1, hg1, hv1⟩ := hRec.sum st (by rw [hsite]; exact (lse_tab st).1)
  obtain ⟨i2, -, a2, bs2, hg2, hv2⟩ := hRec.max st (by rw [hsite]; exact (lse_tab st).2)
  obtain ⟨⟨r, ℓ, hQ⟩, -⟩ := hR
  have hk0 : d.k = 0 := by
    have := hQ.sub
    simp only [hsite] at this
    exact this rfl
  exact ⟨b, hb, hlo, hhi, st, _, _, hal, lse_val hat' hk0 hc' hf' hsite rfl,
    ⟨i1, a1, bs1, hg1, hv1⟩, i2, a2, bs2, hg2, hv2⟩

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
