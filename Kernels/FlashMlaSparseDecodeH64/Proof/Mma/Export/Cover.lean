-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.CommitSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Count
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Desc
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.EvKind
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.MmaCover
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # The QK MMAs of a block read the block's whole dequantized tile

A block `r` of the MMA lane has 24 MMAs, the sixteen QK MMAs `qk k` (the `24 r + k`-th MMA of the
lane) and the eight PV MMAs; the QK MMA `k` has B descriptor `keyDesc (base + 65536 (r % 2)) k`
(`Mma.qkBW_decode`) and the sixteen read every byte of the tile (`MmaFoot.key_cover`). A PV commit
to `svDone` of block `r_b` follows all 24 MMAs of every block `r ≤ r_b`. So (`mma_qkCover`) a byte
of the dequantized tile `r % 2` of the lane's CTA is read, before the commit, by a QK MMA of use
`ringUses 2 (r % 2) r` of the tile: `use + 1` successful polls of `dequantReady` and `use` commits
to `svDone` before it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow MmaFoot

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- The issuing CTA's group of one is the CTA alone. -/
private theorem group_self' (hp : Pre P L m) {g : Nat} (hg : g < L.threads) :
    L.ctaGroup (g / L.block) .one = some [g / L.block] := by
  have hb : 0 < L.block := by rw [hp.block]; decide
  exact ctaGroup_self hp ((Nat.div_lt_iff_lt_mul hb).2 hg)

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- A PV commit to `svDone` follows all MMAs of its block and of the blocks before: it is the
commit of block `rb = 2 · (earlier commits to its slot) + slot`, and `24 (rb + 1)` MMAs of the
lane precede it. -/
private theorem svCommit_mmas {i pc c : Nat} {s : Fin 2} {sp : TcCommit.Spec}
    (hi : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s)) :
    ((X.tr y).take i).countP (Mma.cls .mma) =
      24 * (2 * ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone s))) +
        s.val) + 24 := by
  have h := commit_pcs hX hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  have hpc : 1850 ≤ pc ∧ pc < 2162 := by omega
  have hub : ∀ f, (⟨pc, .tc (.commit sp)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨d, hR, hev, hl, hw⟩ := mma_at hp hX hFw hi hub hpc
  have hc := hR (take_noUb hX hi)
  rcases Mma.ev_commit hl hev with ⟨hs, hm'⟩ | ⟨hs, hm'⟩ | ⟨hs, hm'⟩
  · cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qUt_loc hp)))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, -⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    cases (Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.qk_loc hp (slot2 d.cnt.toNat))))).2
  · obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn⟩ := (Mma.core_loop (by rw [hs]; rfl)).mp hc
    rw [hpha] at hm'
    obtain ⟨hcy, hf⟩ :=
      Mma.mloc_fam (hm.symm.trans (hm'.trans (Mma.sv_loc hp (slot2 d.cnt.toNat))))
    have hC := lane4_commits hp hX hFw hw i (loc L y (.svDone (slot2 d.cnt.toNat)))
    rw [hn _ (by simp), Mma.cnt_sv hp] at hC
    simp only [loc] at hC
    obtain rfl := MbarFam.svDone.inj hf
    subst hcy
    rw [flow_commitsTo, hC, hn _ (by simp)]
    simp only [Mma.cntAt, Mma.proCnt, Mma.loopCnt, hs, Mma.Site.idx, Mma.mmaIn, slot2, ringUses]
    simp
    omega

/-- **The `24 r + k`-th MMA of the lane** (`k < 16`) is the QK MMA `k` of block `r`: B descriptor
`keyDesc (base + 65536 (r % 2)) k`, with `ringUses 2 (r % 2) r + 1` polls of `dequantReady` and
`ringUses 2 (r % 2) r` commits to `svDone` of the tile before it. -/
private theorem qk_event {j pc bb r k : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {b : Fin 2} (hb : b.val = r % 2)
    (he : X.get (y, j) = some ⟨pc, .tc (.mma bb sp acc mask)⟩) (hat : MbarRow.MmaAt L y pc)
    (hn : ((X.tr y).take j).countP (Mma.cls .mma) = 24 * r + k) (hk : k < 16) :
    1853 < pc ∧ sp.descriptor = qkD ∧ sp.b = keyDesc (L.sharedBase + 65536 * (r % 2)) k ∧
      sp.lowCta = y / L.block ∧
      okPolls (mbarLoc L (y / L.block) (.dequantReady b)) ((X.tr y).take j) =
        ringUses 2 b.val r + 1 ∧
      ((X.tr y).take j).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone b))) =
        ringUses 2 b.val r := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hg : y < L.threads := Frame.lt_of_get hX he
  have hgs := group_self' hp hg
  have hub : ∀ f, (⟨pc, .tc (.mma bb sp acc mask)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨d, hR, ⟨hpc, hE⟩, hlv, -⟩ := mma_at hp hX hFw he hub ⟨hlo, hhi⟩
  have hc := hR (take_noUb hX he)
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site
  case qk i =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn'⟩ := (Mma.core_loop (by rfl)).mp hc
    have hh : cnt.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    dsimp only at hpha
    subst hpha
    have hm := hn' _ (by simp : Mma.Cnt.mma ≠ .ub)
    rw [hn] at hm
    simp only [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, Mma.mmaIn] at hm
    have hi := i.isLt
    have hr : cnt.toNat = r ∧ i.val = k := by
      simp at hm
      split_ifs at hm <;> omega
    obtain ⟨hr, hik⟩ := hr
    rcases hE with ⟨s'', hk', haT, hdi, ⟨ctas, hct, hcl, -⟩, -, hBd⟩ | ⟨f, hf⟩
    · cases hk'
      have hD := qkD_eq hdi
      rw [hD, show qkD.group = .one from rfl, hgs] at hct
      cases hct
      simp only [List.head?_cons, Option.some.injEq] at hcl
      rw [Mma.qkBW_decode hp hh i.isLt, hr, hik] at hBd
      refine ⟨by simp only [Mma.Site.pc] at hpc; split_ifs at hpc <;> omega, hD,
        (Option.some.inj hBd).symm, hcl.symm, ?_, ?_⟩
      · have hP := lane4_okPolls hp hX hFw hw j (loc L y (.dequantReady b))
        rw [hn' _ (by simp), Mma.cnt_ready hp] at hP
        simp only [loc] at hP
        rw [hP, hr]
        unfold Mma.useAt Mma.ind
        simp [hb, Mma.Site.idx]
      · have hC := lane4_commits hp hX hFw hw j (loc L y (.svDone b))
        rw [hn' _ (by simp), Mma.cnt_sv hp] at hC
        simp only [loc] at hC
        rw [flow_commitsTo, hC, hr]
    · cases hf
  case leave i => exact absurd rfl (hlv i)
  case pv i =>
    obtain ⟨⟨-, -, -, -, -, hpha, -⟩, hn'⟩ := (Mma.core_loop (by rfl)).mp hc
    have hm := hn' _ (by simp : Mma.Cnt.mma ≠ .ub)
    rw [hn] at hm
    have hi := i.isLt
    have e1 : Mma.mmaIn (21 + i.val) = i.val + 16 := by unfold Mma.mmaIn; split_ifs <;> omega
    simp only [Mma.cntAt, Mma.proCnt, Mma.loopCnt, Mma.Site.idx, e1] at hm
    exfalso
    simp at hm
    omega
  all_goals simp [Mma.EvK, Mma.PollEv, Mma.CommitEv] at hE

/-- **A byte of the dequantized tile of a block is read by a QK MMA of the block before the PV
commit**: for a commit to `svDone s0` with `n` earlier commits to it (block `2 n + s0`), a block
`r ≤ 2 n + s0` and a byte of tile `r % 2` of the lane's CTA, a QK MMA of the lane before the commit
reads the byte as a B operand, after `ringUses 2 (r % 2) r + 1` successful polls of
`dequantReady` and `ringUses 2 (r % 2) r` commits to `svDone` of the tile. -/
theorem mma_qkCover {i pc c r : Nat} {s0 b : Fin 2} {sp : TcCommit.Spec} {l : Loc}
    (hi : X.get (y, i) = some ⟨pc, .tc (.commit sp)⟩) (hm : sp.mbar = mbarLoc L c (.svDone s0))
    (hr : r ≤ 2 * ((X.tr y).take i).countP (PTX.Flow.commitsTo (mbarLoc L c (.svDone s0))) +
      s0.val) (hb : b.val = r % 2) (hl : MemRow.LocIn L (y / L.block) (.dequant b) l) :
    ∃ j < i, ∃ pc' bb idx sp' acc mask, X.get (y, j) = some ⟨pc', .tc (.mma bb sp' acc mask)⟩ ∧
      MbarRow.MmaAt L y pc' ∧ 1853 < pc' ∧ X.MmaFootprint (y, j) true idx l ∧
      okPolls (mbarLoc L (y / L.block) (.dequantReady b)) ((X.tr y).take j) =
        ringUses 2 b.val r + 1 ∧
      ((X.tr y).take j).countP (PTX.Flow.commitsTo (mbarLoc L (y / L.block) (.svDone b))) =
        ringUses 2 b.val r := by
  obtain ⟨hsp, hcta, hlo, hhi⟩ := hl
  simp only [Region.lo, Region.size, hb] at hlo hhi
  have hB := Mma.base_128 hp (65536 * (r % 2)) (by omega)
  obtain ⟨k, hk, hall⟩ := key_cover hB (a := l.addr) hlo (by omega)
  have hmm := svCommit_mmas hp hX hFw hi hm
  obtain ⟨j, x, hj, hx, hcnt⟩ := MbarRing.Slot.exists_nth_countP (Mma.cls .mma) (c := 24 * r + k)
    (xs := (X.tr y).take i) (by omega)
  have hji : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hji.le] at hcnt
  have hget : X.get (y, j) = some x := by
    change (X.tr y)[j]? = some x
    rw [← hj, List.getElem?_take, ite_eq_left hji]
  obtain ⟨pc', kd⟩ := x
  have hin : 1850 ≤ pc' ∧ pc' < 2162 := by
    simp only [Mma.cls, Bool.and_eq_true, Mma.inRole, decide_eq_true_eq] at hx
    omega
  cases kd <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
  case wait q p ok a sc => cases ok <;> simp [Mma.cls, Mma.kindOf] at hx
  case tc t =>
    cases t <;> try (simp [Mma.cls, Mma.kindOf] at hx; done)
    case mma bb sp' acc mask =>
      obtain ⟨-, -, -, -, hw4⟩ := mma_at hp hX hFw hget (fun _ h => by cases h) hin
      have hat : MbarRow.MmaAt L y pc' := ⟨hw4, hin⟩
      obtain ⟨h1853, hD, hsb, hlow, hpol, hcm⟩ := qk_event hp hX hFw hb hget hat hcnt hk
      obtain ⟨idx, hidx⟩ := hall hD (by rw [hsb])
      refine ⟨j, hji, pc', bb, idx, sp', acc, mask, hget, hat, h1853, ?_, hpol, hcm⟩
      refine Or.inl ⟨bb, sp', acc, mask, ⟨pc', hget⟩, ?_⟩
      simp only [ite_true]
      rw [hidx, hlow, ← hcta, ← hsp]

end
end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
