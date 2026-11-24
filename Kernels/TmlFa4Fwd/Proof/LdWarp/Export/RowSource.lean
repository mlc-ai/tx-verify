-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.RowNum
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrRecv
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.RowAddr
import Kernels.TmlFa4Fwd.Proof.LdWarp.Pos
import Kernels.TmlFa4Fwd.Proof.LdWarp.RowStep
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.TileInv
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizePrime
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizeSteady
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpSizeWarm
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The exact source of a row copy

The row copy with `32 t + 2 i + j` earlier ones of its lane is of packet `t`, row `i` of the lane's
sixteen and half `j`. When the row's key of the tile is used, it reads the sixteen bytes of the
lane's column in the key's row of the K (`t` even) or V cache (`ld_row_src`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.LdWarp

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem src_lane : ∀ ℓ < 32, ∀ i < 8,
    (shflSource .idx ℓ i 6175).1 = ℓ / 8 * 8 + i := by decide +kernel

private theorem pair_val {x0 x1 : BitVec 64} {y : Nat} (h0 : x0.toNat = y % 2 ^ 32)
    (h1 : x1.toNat = y / 2 ^ 32) (hy : y < 2 ^ 64) : (x0 ||| x1 <<< 32).toNat = y := by
  have h : (x1 <<< 32).toNat = y / 2 ^ 32 * 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h1]
    omega
  rw [BitVec.toNat_or, h, h0, Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  omega

private theorem off_words : ∀ i < 512,
    (wideU2 (andi (shl (BitVec.ofNat 64 i) 3) 56)).toNat = 16 * (i % 8) ∧
      (and64 (zext (shl (BitVec.ofNat 64 i) 4)) 112).toNat = 16 * (i % 8) := by
  decide +kernel

/-- The source word of a row copy: the row's address and the lane's column. -/
private theorem cp_ad (hp : Pre p L m) (w : Nat) (per : Per) (b : Bool) (i : Fin 16) (c : Fin 2)
    (v : V) (kk : Fin 2) : ∃ off : BitVec 64, off.toNat = 16 * (g % L.block % 8) ∧
      rv p L g w ⟨.cp per b i c, v, kk⟩ ((pkRegs (pk per b)).ad.getD i.val 0) =
        add64 (v.x0 ||| v.x1 <<< 32) off := by
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨h1, h2⟩ := off_words _ hi
  cases per <;> cases b
  case warm.true => exact ⟨_, h2, by fin_cases i <;> rfl⟩
  all_goals exact ⟨_, h1, by fin_cases i <;> rfl⟩

set_option maxHeartbeats 4000000 in
/-- **The exact source of a row copy.** -/
theorem ld_row_src (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {pc : Nat}
    {sp : AsyncCopy.Spec} (he : X.get (g, k) = some ⟨pc, .copy sp⟩) {b t i j : Nat}
    (hlo : tilePrefix p b * p.heads ≤ g / L.block)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) (hi : i < 16) (hj : j < 2)
    (hcnt : ((X.tr g).take k).countP cpCopy = 32 * t + (2 * i + j)) {key : Nat}
    (hkey : key = 128 * (nBlk p L g b - 1 - t / 2) + grpOf L g + 8 * i)
    (hlt : key < p.kLength b) :
    sp.src.size = 16 ∧ sp.src.loc = ⟨.global, 0, (layOf p (t % 2 == 1)).base +
      2 * (p.page b (key / 16) * (layOf p (t % 2 == 1)).pageStride +
        (Epilogue.assignedCoordinates p b (g / L.block)).2 / 6 * (layOf p (t % 2 == 1)).headStride +
        key % 16 * (layOf p (t % 2 == 1)).rowStride) + 16 * (g % L.block % 8) + 128 * j⟩ := by
  have hg := Frame.lt_of_get hX he
  have hkl := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi', hev'⟩ |
    ⟨bb, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi'.2 trivial).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, c, i', j', hs⟩ : ∃ per c i' j', d.site = .cp per c i' j' := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  obtain ⟨t', ins, o, hat, -, hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ hub
  have hbk : d.site.blk = true := by rw [hs]; cases per <;> rfl
  have hF := (hR.2 h0).2
  have hT := tile_inv hp hX hg hw k hkl.le bb d n hσ h0 hbk
  obtain ⟨b', hN⟩ := blk_num hp hg hbk hF hT
  obtain rfl := work_unique hN.lo hN.hi hlo hhi
  have hper : perOf d.site = some per := by rw [hs]; rfl
  have hibv : inBlk d.site = if c then 1 else 0 := by rw [hs]; rfl
  have hib : inBlk d.site ≤ 1 := by rw [hibv]; split <;> omega
  obtain ⟨n1, n2, n3⟩ := nBlk_bound hp hN.batch hN.lo hN.hi
  obtain ⟨hc2, hcu, -, -⟩ := blk_round hbk hF hN n1 n2 hper hib
  -- the packet
  have hcp : ((X.tr g).take k).countP cpCopy =
      32 * n (.load .commit) + (2 * i'.val + j'.val) := by
    have h := Loader.cp_count hp hX hg hw hσ h0
    simp only [Loader.CpCount, hs, Loader.inPkt, LdWarp.lcn] at h
    exact (Nat.add_zero _).symm.trans h
  have hi2 := i'.isLt
  have hj2 := j'.isLt
  obtain ⟨htn, hii, hjj⟩ : n (.load .commit) = t ∧ i'.val = i ∧ j'.val = j := by omega
  have hcb : (t % 2 == 1) = c := by
    rw [hibv, htn] at hc2
    cases c <;> simp at hc2 ⊢ <;> omega
  -- the source lane
  have hrc := LdWarp.recv_ok hp hX hg hw k hkl.le bb d n hσ h0
  obtain ⟨site, v', k2⟩ := d
  simp only at hs
  subst hs
  obtain ⟨-, j0, b1, d1, n1', hsg, hσ1, hub1, hjl1, ⟨per1, c1, hs1⟩, hsh, hx0, hx1⟩ := hrc
  have hlane : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  have hsrc : srcOf L g i' = g - laneOf L g + (laneOf L g / 8 * 8 + i'.val % 8) := by
    unfold srcOf
    rw [src_lane _ hlane _ (Nat.mod_lt _ (by decide))]
  have hb512 := hp.block
  obtain ⟨-, hsw, hsc, -, -⟩ := lane_facts hp hg rfl
    (show laneOf L g / 8 * 8 + i'.val % 8 < 32 by omega)
  rw [← hsrc] at hsw hsc
  have hgrp : grpOf L (srcOf L g i') = grpOf L g ∧ srcOf L g i' % L.block % 8 = i'.val % 8 := by
    rw [hsrc]
    unfold grpOf
    simp only [laneOf, hb512]
    omega
  generalize srcOf L g i' = src at *
  have hww : Prologue.warpIndex L src = 14 ∨ Prologue.warpIndex L src = 15 := by rw [hsw]; exact hw
  have hG1 := (good hp hX hww hsg rfl j0).2 _ hσ1
  have hF1 := (hG1.2 hub1).2
  have hb1 : d1.site.blk = true := by rw [hs1]; cases per1 <;> rfl
  have hT1 := tile_inv hp hX hsg hww j0 hjl1.le b1 d1 n1' hσ1 hub1 hb1
  obtain ⟨b2, hN1⟩ := blk_num hp hsg hb1 hF1 hT1
  have hb2 : b2 = b' := work_unique hN1.lo hN1.hi (by rw [hsc]; exact hlo)
    (by rw [hsc]; exact hhi)
  subst hb2
  have hper1 : perOf d1.site = some per1 := by rw [hs1]; rfl
  have hibv1 : inBlk d1.site = if c1 then 1 else 0 := by rw [hs1]; rfl
  have hib1 : inBlk d1.site ≤ 1 := by rw [hibv1]; split <;> omega
  -- the source has the same commits
  have hnc : n1' (.load .commit) = t := by
    obtain ⟨R, bal, hP, hns, -⟩ := bband hF hbk
    obtain ⟨R1, bal1, hP1, hns1, -⟩ := bband hF1 hb1
    obtain ⟨rfl, rfl⟩ := (hP.cta hsc.symm).unique hP1
    rw [hs1] at hns1
    simp only [pktSh] at hns hns1
    rw [(counts hσ).1, (counts hσ1).1] at hsh
    omega
  have hcc : c1 = c := by
    obtain ⟨m1, -, -⟩ := nBlk_bound hp hN1.batch hN1.lo hN1.hi
    obtain ⟨-, m2, -⟩ := nBlk_bound hp hN1.batch hN1.lo hN1.hi
    obtain ⟨hc3, -⟩ := blk_round hb1 hF1 hN1 m1 m2 hper1 hib1
    rw [hibv1, hnc, ← htn, hc2, hibv] at hc3
    cases c <;> cases c1 <;> simp_all
  subst hcc
  -- the address
  have hI1 := row_inv hp hX hsg hww hN1.lo hN1.hi j0 hjl1.le b1 d1 n1' hσ1 hub1 hb1
  have hrow1 := hI1.row per1 c1 ⟨i'.val / 8, by omega⟩ (by rw [hs1]; rfl)
  have had := adW_num hp hb1 hF1 hT1 hN1 hper1 hib1 c1 ⟨i'.val / 8, by omega⟩
  have hkk : keyAt p L b2 src (n1' (.load .commit)) ⟨i'.val / 8, by omega⟩ = key := by
    rw [hkey, hnc]
    unfold keyAt rowIn nBlk
    rw [hgrp.1, hgrp.2, hsc]
    simp only
    omega
  rw [hkk, hsc, show pageAt p b2 key = p.page b2 (key / 16) by unfold pageAt; rw [ite_eq_left hlt]]
    at had
  have hpair : (v'.x0 ||| v'.x1 <<< 32).toNat = (adW p b2 L src d1.v per1 c1 ⟨i'.val / 8,
      by omega⟩).toNat := by
    rw [show v'.x0 = d1.v.l0 from hx0, show v'.x1 = d1.v.l1 from hx1]
    exact pair_val hrow1.1 hrow1.2 (BitVec.isLt _)
  rw [had] at hpair
  obtain ⟨off, hoff, hadd⟩ := cp_ad (g := g) hp (Loader.wOf bb) per c1 i' j' v' k2
  -- the size
  have hI := row_inv hp hX hg hw hlo hhi k hkl.le bb _ n hσ h0 hbk
  have hlen := len_num hp hbk hF hN hper hib
  have hlo' : sv (lenOf L g v' per) = (p.kLength b2 : Int) -
      (128 * (nBlk p L g b2 - 1 - t / 2) + grpOf L g : Nat) := by
    rw [← htn, ← hlen]
    congr 1
    by_cases hpr : per = .prime
    · subst hpr; rfl
    · rw [ite_eq_right hpr]
      refine Eq.trans ?_ (hI.len per hpr (by cases per <;> cases c1 <;> rfl))
      cases per
      · exact absurd rfl hpr
      · rfl
      · rfl
  have hsz : sp.src.size = 16 := by
    have h : sp.src.size = cpSize L g v' per i' := by
      cases per
      · exact Loader.cp_size_prime hat hc hf rfl
      · exact Loader.cp_size_warm hat hc hf rfl
      · exact Loader.cp_size_steady hat hc hf rfl
    rw [h]
    unfold cpSize
    rw [scmpi_gt_s _ (by omega) (by omega), hlo', ite_eq_left]
    simp only [decide_eq_true_eq]
    omega
  refine ⟨hsz, ?_⟩
  simp only [Loader.Ev] at hev
  rcases hev with ⟨n', hk⟩ | ⟨f, hk⟩
  swap
  · cases hk
  simp only [Kind.copy.injEq] at hk
  subst hk
  simp only [Loc.mk.injEq, true_and]
  rw [hadd, hcb]
  have hl : layOf p c1 = p.kLayout ∨ layOf p c1 = p.vLayout := by
    cases c1
    · exact .inl rfl
    · exact .inr rfl
  obtain ⟨-, hh⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  have hroom := row_room hp hl ((hp.pageTable b2 hN.batch).2 (key / 16) (by omega)).1
    (show (Epilogue.assignedCoordinates p b2 (g / L.block)).2 / 6 < p.kvHeads by
      unfold Params.heads at hh; omega) (show key % 16 < 16 by omega)
  have h3 : (add64 (v'.x0 ||| v'.x1 <<< 32) off).toNat = (v'.x0 ||| v'.x1 <<< 32).toNat +
      16 * (g % L.block % 8) := by
    simp only [add64, r64, toNat_tb64, BitVec.toNat_add, hoff]
    omega
  have hcpo : (BitVec.ofInt 64 (cpOff j')).toNat = 128 * j'.val := by
    fin_cases j' <;> decide
  rw [BitVec.toNat_add, h3, hpair, hcpo, hjj]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
