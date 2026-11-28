-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsMid
public import Kernels.InklingRelDecode.Proof.Softmax.Data.StartRegion
import Kernels.InklingRelDecode.Proof.Lib.Havoc

@[expose] public section

/-! # The bias words kept by the round

The sites between the loop's loads and the barrier after the round keep the facts of the words
that the next sites list: one region check for the words with their packs and one for the words
alone (`DataStep.constAny`), and the successors' facts are among the site's. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.EventFrame Control

set_option maxRecDepth 100000
noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem region_W1 : regionH kernel Lib.hooks ivsW (packK ++ nwK) = true := by decide +kernel
theorem region_W2 : regionH kernel Lib.hooks ivsW nwK = true := by decide +kernel

theorem mid_ok (s : Site) (h : midB s = true) : siteW s = true ∧ subB s = true := by
  cases s with
  | pre j => simp [midB] at h
  | nxt j => simp [midB] at h
  | _ => revert h; decide +kernel

theorem mid_wN (s : Site) (h : midB s = true) : wN s = 64 := by
  cases s with
  | nxt j => simp [midB] at h
  | pre j => simp [midB] at h
  | _ => first | rfl | simp [midB] at h

/-- **The bias words are kept** by a site of the round. -/
theorem w_mid {d : D} (hm : midB d.c.site = true) : DataStep (codeS e L g) wF d := by
  obtain ⟨hw, hb⟩ := mid_ok d.c.site hm
  simp only [siteW, Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hw
  have hs : ∀ j, d.c.site ≠ .pre j := by
    intro j h
    rw [h] at hm
    simp [midB] at hm
  have hk : (wF d).map Prod.fst = (if wP d.c.site then packK else []) ++ nwK := by
    rw [wF, wFS_keyEq _ _ hs, mid_wN _ hm]
    rfl
  have key : DataStep (codeS e L g) wF d :=
    DataStep.constAny (C := codeS e L g) (sF := wF) (d := d)
      (A := Assumptions.all) (tab := Lib.hooks) (ivs := ivsW)
      Lib.rulesFrame hooks_any (Kernels.InklingRelDecode.Proof.segFree h3) ⟨h1, h2⟩
      (fun R h => atS_wF h) (fun ins hc => ?_)
      (by
        rw [hk]
        split_ifs
        · exact region_W1
        · exact region_W2) ?_
  · exact @key
  · change kernel.code[d.c.site.pc]? = some ins at hc
    rw [hc] at h4
    simp only [List.all_eq_true] at h4 ⊢
    intro r hr
    exact h4 r (wFS_keys d.c.site d.v hs r hr)
  · intro ev d' hn x hx
    obtain ⟨c', hnc, rfl⟩ := succ_inv (show (code e L g).next d ev = some (some d') from hn)
    have hz := next_mem (e := e) (L := L) (g := g) (ev := ev) hnc
    obtain ⟨hv1, hv2⟩ := record_wd (L := L) ev c'.site hm
    have := wFS_sub hm hb hz d.v
    simp only [wF] at hx ⊢
    rw [wFS_congr c'.site hv1 hv2] at hx
    exact this x hx

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
