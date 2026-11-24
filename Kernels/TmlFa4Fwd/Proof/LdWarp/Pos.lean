-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Kernels.TmlFa4Fwd.Proof.Common.Roles
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Where a loader lane stands among the warp collectives

The loader's collectives are the scheduler's shuffles and ballots (the output warp's, at the
thread's count shifted by `32` per committed packet) and the packets' row shuffles (32 per
packet, between the first pass's choice and the second pass). For two lanes of one CTA:

* `lband`: a scheduler, request or drain state of the first pass stands before the CTA's choice
  and has committed no packet; one of the second pass stands after the choice and all the tile's
  packets (`pkts` of the picked tile's block word, the same on every lane of the CTA);
* `bband`: a block state stands at the choice plus its packets' shuffles, and a row shuffle
  before the tile's last packet ends;
* from them, the position facts of `Common/Coll.lean` (a shuffle before every ballot with at least
  its ballot count and before every return, no return before a ballot, one site per shuffle and
  per ballot count), from the output warp's (`Epilogue/Position.lean`) on the shifted counts. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (nC ePass eColl eEnd eband)

noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g h : Nat}

/-- The packets' row shuffles. -/
def Site.pkt : Site → Bool
  | .xl _ _ _ | .xh _ _ _ => true
  | _ => false

/-- The loader's shuffle sites: the scan's and the packets'. -/
def Site.lsh (s : Site) : Bool := s.pkt || s.epi.shfl

/-- The block word of the picked tile is the same on every lane of the CTA. -/
theorem r28Ref_cta {R : Nat} {bal : BitVec 64} (hc : g / L.block = h / L.block) :
    r28Ref p L g R bal = r28Ref p L h R bal := by
  simp only [r28Ref, refVL, setup, coords, Epilogue.chosenD, Epilogue.ctaW, hc]

theorem pkt_blk {s : Site} (h : s.pkt = true) : s.blk = true := by
  cases s <;> simp_all [Site.pkt, Site.blk, bc]

theorem pkt_pktSh {s : Site} (h : s.pkt = true) : pktSh s < 32 := by
  cases s <;> simp_all [Site.pkt, pktSh] <;> omega

theorem lsh_cases {s : Site} (h : s.lsh = true) : s.pkt = true ∨ s.epi.shfl = true := by
  simpa [Site.lsh] using h

theorem shfl_lc {s : Site} (h : s.epi.shfl = true) : lc s = .p1 ∨ lc s = .p2 := by
  cases s <;> simp [Site.epi, Epilogue.Site.shfl] at h <;> simp only [lc] <;> split <;> simp

theorem shfl_not_pkt {s : Site} (h : s.epi.shfl = true) : s.pkt = false := by
  cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, Site.pkt]

theorem epi_shfl_inj {s s' : Site} (hs : s.epi.shfl = true) (h : s'.epi = s.epi) : s' = s := by
  cases s <;> simp [Site.epi, Epilogue.Site.shfl] at hs <;> cases s' <;> simp_all [Site.epi]

theorem lc_p1 {s : Site} (h : lc s = .p1 ∨ lc s = .req) : ePass s.epi = false ∧ s.epi ≠ .start := by
  cases s <;> simp only [lc] at h <;> (try split at h) <;> simp_all [ePass, Site.epi]

theorem lc_p2 {s : Site} (h : lc s = .p2) : ePass s.epi = true ∧ s.epi ≠ .start := by
  cases s <;> simp only [lc] at h <;> (try split at h) <;> simp_all [ePass, Site.epi]

/-- `omega` with the choice's position unfolded. -/
local macro "omg" : tactic => `(tactic| ((try unfold nC at *); omega))

/-- Where a state of the scheduler or the drain stands, with output-warp site `s`, shuffles
`ns`, ballots `nv` and commits `nc`. -/
def Band (p : Params) (L : Launch) (g : Nat) (s : Epilogue.Site) (ns nv nc : Nat) : Prop :=
  (ePass s = false ∧ nc = 0 ∧ (s.ballot = true → nv = 0) ∧
    ∀ R bal, Picked p L g R bal → ns ≤ nC R bal ∧ (eColl s = true → ns < nC R bal) ∧
      ∀ l, s ≠ .exit l) ∨
  (ePass s = true ∧ 1 ≤ nv ∧ ∃ R bal, Picked p L g R bal ∧
    nc = pkts (r28Ref p L g R bal) ∧ nC R bal + 32 * nc ≤ ns ∧
    (eEnd s = true → nC R bal + 7 + 32 * nc ≤ ns))

set_option maxHeartbeats 1000000 in
/-- **Where a scheduler, request or drain state stands**, at its count shifted by its committed
packets: the first pass before the CTA's choice with no packet committed, or the second pass after
the choice and all the tile's packets. -/
theorem lband {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc)
    (hl : lc d.site = .p1 ∨ lc d.site = .req ∨ lc d.site = .p2 ∨ lc d.site = .drain) :
    ∃ dE : Epilogue.D, Epilogue.Fits p L g dE (ns - 32 * nc) nv ∧ 32 * nc ≤ ns ∧
      (lc d.site ≠ .drain → dE = toE d) ∧
      (lc d.site = .drain → ∃ l, dE.site = .exit l) ∧
      Band p L g dE.site ns nv nc := by
  have hsu : ∀ R bal, Picked p L g R bal → SuRef p L g d.v → nc = pkts d.v.su.r28 →
      nc = pkts (r28Ref p L g R bal) := by
    rintro R bal hPk ⟨R', bal', hPk', h28⟩ hn
    obtain ⟨rfl, rfl⟩ := hPk.unique hPk'
    rw [hn, h28]
  unfold Band
  rcases hl with hl | hl | hl | hl
  · have hF' := hF
    unfold LFits at hF'
    rw [hl] at hF'
    obtain ⟨rfl, hFE⟩ := hF'
    obtain ⟨hp1, hne⟩ := lc_p1 (.inl hl)
    refine ⟨toE d, by simpa using hFE, by omega, fun _ => rfl, ?_, ?_⟩
    · intro h; rw [hl] at h; cases h
    rcases eband hFE hne with ⟨-, hb, hk⟩ | ⟨hp2, -⟩
    · exact .inl ⟨hp1, rfl, hb, hk⟩
    · exact absurd (hp2.symm.trans hp1) (by simp)
  · have hF' := hF
    unfold LFits at hF'
    rw [hl] at hF'
    obtain ⟨rfl, hFE, -⟩ := hF'
    obtain ⟨hp1, hne⟩ := lc_p1 (.inr hl)
    refine ⟨toE d, by simpa using hFE, by omega, fun _ => rfl, ?_, ?_⟩
    · intro h; rw [hl] at h; cases h
    rcases eband hFE hne with ⟨-, hb, hk⟩ | ⟨hp2, -⟩
    · exact .inl ⟨hp1, rfl, hb, hk⟩
    · exact absurd (hp2.symm.trans hp1) (by simp)
  · have hF' := hF
    unfold LFits at hF'
    rw [hl] at hF'
    obtain ⟨hle, hFE, hS, hn⟩ := hF'
    obtain ⟨hp2, hne⟩ := lc_p2 hl
    refine ⟨toE d, hFE, hle, fun _ => rfl, ?_, ?_⟩
    · intro h; rw [hl] at h; cases h
    rcases eband hFE hne with ⟨hp1, -⟩ | ⟨-, hnv, R, bal, hPk, h1, h2⟩
    · exact absurd (hp2.symm.trans hp1) (by simp)
    · exact .inr ⟨hp2, hnv, R, bal, hPk, hsu R bal hPk hS hn, by omg, fun h => by
        have := h2 h; omg⟩
  · have hF' := hF
    unfold LFits at hF'
    rw [hl] at hF'
    obtain ⟨l, hle, hFE, hT, hF0⟩ := hF'
    refine ⟨_, hFE, hle, fun h => absurd hl h, fun _ => ⟨l, rfl⟩, ?_⟩
    cases l
    · obtain rfl := hF0 rfl
      rcases eband hFE (by simp) with ⟨hp1, hb, hk⟩ | ⟨hp2, -⟩
      · refine .inl ⟨hp1, rfl, hb, fun R bal hPk => ?_⟩
        have := hk R bal hPk
        simp at this
      · simp [ePass] at hp2
    · obtain ⟨hS, hn⟩ := hT rfl
      rcases eband hFE (by simp) with ⟨hp1, -⟩ | ⟨hp2, hnv, R, bal, hPk, h1, h2⟩
      · simp [ePass] at hp1
      · exact .inr ⟨hp2, hnv, R, bal, hPk, hsu R bal hPk hS hn, by omg, fun h => by
          have := h2 h; omg⟩

theorem nc_lt_pkts {s : Site} {v : V} {nc : Nat} (hp : s.pkt = true) (hR : Rounds s v nc) :
    nc < pkts v.su.r28 := by
  obtain ⟨-, hB⟩ := hR
  have hib : inBlk s ≤ 1 := by cases s <;> simp_all [Site.pkt, inBlk] <;> split <;> omega
  unfold pkts
  cases s <;> simp only [Site.pkt, Bool.false_eq_true] at hp <;>
  · rename_i per vv i
    cases per <;> simp only [bc, RoundsB] at hB
    · omega
    · obtain ⟨r, -, h2, hr, rfl⟩ := hB
      rw [w0_of h2]
      have := Int.toNat_of_nonneg (show (0 : Int) ≤ 0 by omega)
      omega
    · obtain ⟨r, -, hr0, hr, rfl⟩ := hB
      have h1 : ((r : Int) - wRn v.su.r28).toNat = r - wRn v.su.r28 := by omega
      have h2 : r - wRn v.su.r28 + 1 ≤ (sv (addi v.su.r28 (-1)) - wRn v.su.r28).toNat := by
        omega
      omega

set_option maxHeartbeats 1000000 in
/-- **Where a block state stands**: at the CTA's choice plus the shuffles of its committed
packets and of the current packet; a row shuffle before the end of the tile's last packet. -/
theorem bband {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc) (hb : d.site.blk = true) :
    ∃ R bal, Picked p L g R bal ∧ ns = nC R bal + 32 * nc + pktSh d.site ∧ nv = 1 ∧
      (d.site.pkt = true → 32 * nc + pktSh d.site < 32 * pkts (r28Ref p L g R bal)) := by
  have hF' := hF
  unfold LFits at hF'
  rw [lc_blk.mpr hb] at hF'
  obtain ⟨hle, hFE, ⟨R', bal', hPk', h28⟩, hR, -⟩ := hF'
  have hsite : d.site.epi = .ready 0 := epi_blk hb
  simp only [Epilogue.Fits, toE, hsite] at hFE
  obtain ⟨R, bal, ⟨hPk, -, -, -, -, -, -, hns, hnv⟩, -⟩ := hFE
  obtain ⟨rfl, rfl⟩ := hPk.unique hPk'
  refine ⟨R, bal, hPk, by unfold nC; omega, hnv, fun hp => ?_⟩
  have h1 := nc_lt_pkts hp hR
  have h2 := pkt_pktSh hp
  rw [← h28]
  omega

/-- **The first pass comes before the packets and the second pass**: shifting the output warp's
counts of two lanes of one CTA keeps their order. -/
theorem shift {s s' : Epilogue.Site} {ns nv nc ns' nv' nc' : Nat}
    (hc : g / L.block = h / L.block) (hB : Band p L g s ns nv nc) (hB' : Band p L h s' ns' nv' nc')
    (hco : eColl s = true) (hco' : eColl s' = true) (hle : 32 * nc ≤ ns) (hle' : 32 * nc' ≤ ns') :
    (ns - 32 * nc < ns' - 32 * nc' → ns < ns') ∧
      (ns = ns' → ns - 32 * nc = ns' - 32 * nc' ∧ ePass s' = ePass s) := by
  rcases hB with ⟨l1, p1, -, k1⟩ | ⟨l2, -, R, bal, hPk, p2, q1, -⟩ <;>
    rcases hB' with ⟨l1', p1', -, k1'⟩ | ⟨l2', -, R', bal', hPk', p2', q1', -⟩
  · exact ⟨fun h => by omega, fun h => ⟨by omega, by rw [l1, l1']⟩⟩
  · have := (k1 R' bal' (Epilogue.Picked.cta hc.symm hPk')).2.1 hco
    exact ⟨fun _ => by omega, fun h => by omega⟩
  · have := (k1' R bal (Epilogue.Picked.cta hc hPk)).2.1 hco'
    exact ⟨fun h => by omega, fun h => by omega⟩
  · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
    rw [← r28Ref_cta hc] at p2'
    exact ⟨fun h => by omega, fun h => ⟨by omega, by rw [l2, l2']⟩⟩

theorem vote_lc {s : Site} {l : Bool} (hs : s = .vote l) :
    (lc s = .p1 ∨ lc s = .req ∨ lc s = .p2 ∨ lc s = .drain) ∧ lc s ≠ .drain := by
  subst hs; cases l <;> simp [lc]

theorem shfl_lc' {s : Site} (hs : s.epi.shfl = true) :
    (lc s = .p1 ∨ lc s = .req ∨ lc s = .p2 ∨ lc s = .drain) ∧ lc s ≠ .drain := by
  rcases shfl_lc hs with h | h <;> simp [h]

theorem exit_lc : (lc Site.exit = .p1 ∨ lc Site.exit = .req ∨ lc Site.exit = .p2 ∨
    lc Site.exit = .drain) ∧ lc Site.exit = .drain := by simp [lc]

theorem shfl_coll {s : Site} (hs : s.epi.shfl = true) : eColl s.epi = true := by
  cases s <;> simp_all [Site.epi, Epilogue.Site.shfl, eColl]

theorem exit_fits {dE : Epilogue.D} {l : Bool} {ns nv : Nat} (hs : dE.site = .exit l)
    (hF : Epilogue.Fits p L g dE ns nv) : Epilogue.Fits.ExitAt p L g l ns nv := by
  simpa [Epilogue.Fits, hs] using hF

variable {d d' : D} {ns nv nc ns' nv' nc' : Nat}

/-- **A shuffle state comes before every ballot state with at least its ballot count.** -/
theorem lshfl_lt_vote {l : Bool} (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hs : d.site.lsh = true)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site = .vote l) (hv : nv ≤ nv') : ns < ns' := by
  obtain ⟨hl', hnd'⟩ := vote_lc hs'
  obtain ⟨dE', hFE', hle', h1', -, hB'⟩ := lband hF' hl'
  have hsE' : dE'.site = .vote l := by rw [h1' hnd']; simp [hs', Site.epi]
  rw [hsE'] at hB'
  rcases lsh_cases hs with hp | hse
  · obtain ⟨R, bal, hPk, hns, hnv, hlt⟩ := bband hF (pkt_blk hp)
    rcases hB' with ⟨-, -, hb0, -⟩ | ⟨-, -, R', bal', hPk', p2', q1', h8⟩
    · have := hb0 rfl; omega
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
      rw [← r28Ref_cta hc] at p2'
      have := h8 rfl
      have := hlt hp
      omg
  · obtain ⟨hl, hnd⟩ := shfl_lc' hse
    obtain ⟨dE, hFE, hle, h1, -, hB⟩ := lband hF hl
    have hsE : dE.site = d.site.epi := by rw [h1 hnd]
    rw [hsE] at hB
    have := Epilogue.shfl_lt_vote hFE hFE' hc (by rw [hsE]; exact hse) hsE' hv
    exact (shift hc hB hB' (shfl_coll hse) rfl hle hle').1 this

/-- **A shuffle state comes before every return.** -/
theorem lshfl_lt_exit (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hs : d.site.lsh = true)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site = .exit) : ns < ns' := by
  have hl' : lc d'.site = .drain := by rw [hs']; rfl
  obtain ⟨dE', hFE', hle', -, h2', hB'⟩ := lband hF' (.inr (.inr (.inr hl')))
  obtain ⟨l', hsE'⟩ := h2' hl'
  rw [hsE'] at hB'
  rcases lsh_cases hs with hp | hse
  · obtain ⟨R, bal, hPk, hns, hnv, hlt⟩ := bband hF (pkt_blk hp)
    rcases hB' with ⟨-, -, -, k1⟩ | ⟨-, -, R', bal', hPk', p2', q1', h8⟩
    · exact absurd rfl ((k1 R bal (Epilogue.Picked.cta hc hPk)).2.2 l')
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hPk).unique hPk'
      rw [← r28Ref_cta hc] at p2'
      have := h8 rfl
      have := hlt hp
      omg
  · obtain ⟨hl, hnd⟩ := shfl_lc' hse
    obtain ⟨dE, hFE, hle, h1, -, hB⟩ := lband hF hl
    have hsE : dE.site = d.site.epi := by rw [h1 hnd]
    rw [hsE] at hB
    have := Epilogue.shfl_lt_exit hFE hc (by rw [hsE]; exact hse) (exit_fits hsE' hFE')
    exact (shift hc hB hB' (shfl_coll hse) rfl hle hle').1 this

/-- **No lane returns before a ballot that another lane of its warp makes.** -/
theorem lvote_exit {l : Bool} (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hs : d.site = .vote l)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site = .exit) (hv : nv' ≤ nv) : False := by
  obtain ⟨hl, hnd⟩ := vote_lc hs
  obtain ⟨dE, hFE, -, h1, -, -⟩ := lband hF hl
  have hl' : lc d'.site = .drain := by rw [hs']; rfl
  obtain ⟨dE', hFE', -, -, h2', -⟩ := lband hF' (.inr (.inr (.inr hl')))
  obtain ⟨l', hsE'⟩ := h2' hl'
  exact Epilogue.vote_exit (late := l) hFE hc (by rw [h1 hnd]; simp [hs, Site.epi])
    (exit_fits hsE' hFE') hv

/-- **Two lanes at shuffle states with one shuffle count**: a scan shuffle of one is the same
site of the other, at the same shifted count. -/
theorem lshfl_same (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hse : d.site.epi.shfl = true)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site.lsh = true) (hn : ns = ns') :
    d'.site = d.site ∧ ns' - 32 * nc' = ns - 32 * nc := by
  obtain ⟨hl, hnd⟩ := shfl_lc' hse
  obtain ⟨dE, hFE, hle, h1, -, hB⟩ := lband hF hl
  have hsE : dE.site = d.site.epi := by rw [h1 hnd]
  rw [hsE] at hB
  rcases lsh_cases hs' with hp | hse'
  · obtain ⟨R, bal, hPk, hns, hnv, hlt⟩ := bband hF' (pkt_blk hp)
    exfalso
    rcases hB with ⟨-, -, -, k1⟩ | ⟨-, -, R', bal', hPk', p2, q1, -⟩
    · have := (k1 R bal (Epilogue.Picked.cta hc.symm hPk)).2.1 (shfl_coll hse)
      omg
    · obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc.symm hPk).unique hPk'
      have := hlt hp
      rw [← r28Ref_cta hc] at this
      omg
  · obtain ⟨hl', hnd'⟩ := shfl_lc' hse'
    obtain ⟨dE', hFE', hle', h1', -, hB'⟩ := lband hF' hl'
    have hsE' : dE'.site = d'.site.epi := by rw [h1' hnd']
    rw [hsE'] at hB'
    obtain ⟨hE, -⟩ := (shift hc hB hB' (shfl_coll hse) (shfl_coll hse') hle hle').2 hn
    have := Epilogue.shfl_same hFE hFE' hc (by rw [hsE]; exact hse) (by rw [hsE']; exact hse') hE
    rw [hsE, hsE'] at this
    exact ⟨epi_shfl_inj hse this, hE.symm⟩

/-- **Two ballot states of lanes of one CTA with one ballot count are at one site**, at the same
shifted count. -/
theorem lvote_same {l l' : Bool} (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hs : d.site = .vote l)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site = .vote l') (hv : nv = nv') :
    d'.site = d.site ∧ ns' - 32 * nc' = ns - 32 * nc := by
  obtain ⟨hl, hnd⟩ := vote_lc hs
  obtain ⟨dE, hFE, -, h1, -, -⟩ := lband hF hl
  obtain ⟨hl', hnd'⟩ := vote_lc hs'
  obtain ⟨dE', hFE', -, h1', -, -⟩ := lband hF' hl'
  have hsE : dE.site = .vote l := by rw [h1 hnd]; simp [hs, Site.epi]
  have hsE' : dE'.site = .vote l' := by rw [h1' hnd']; simp [hs', Site.epi]
  obtain ⟨h1, h2⟩ := Epilogue.vote_same hFE hFE' hc hsE hsE' hv
  refine ⟨?_, h2⟩
  rw [hsE, hsE'] at h1
  simp only [Epilogue.Site.vote.injEq] at h1
  rw [hs, hs', h1]

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
