-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Positions in the warp's common sequence of shuffles and ballots

The states of the lanes of one warp that hold the reference values stand at positions of one
sequence: a state's shuffle count `ns` and ballot count `nv` fix its site. Two lanes at shuffle
sites with one shuffle count are at one site (`shfl_same`); a lane at a shuffle site comes before
every ballot state with at least its ballot count (`shfl_lt_vote`) and before every return
(`shfl_lt_exit`); no lane returns before a ballot it has not made while another lane makes it
(`vote_exit`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section


/-- The scan of pass `late` that round `r` runs. -/
def scanOf (late : Bool) (r : Nat) : Scan :=
  if r = 0 then (if late then .second else .first) else (if late then .loop2 else .loop)

/-- The shuffle site of a scan at offset `o` of its round. -/
def scanSite (k : Scan) (o : Nat) : Site :=
  if o = 0 then .down k else if h : o ≤ 5 then .up k ⟨o - 1, by omega⟩ else .total k

variable {p : Params} {L : Launch} {g h : Nat} {ns nv ns' nv' : Nat}

theorem scanRound_scanOf {c r : Nat} {k : Scan} (hR : ScanRound p c k r) : k = scanOf k.late r := by
  obtain ⟨-, hr⟩ := hR
  cases k <;> simp_all [scanOf, Scan.late]

/-- Where a state at a shuffle site stands: at offset `o` of round `r` of the scan of pass
`late`, or at the choice after the scan ended at round `R`. -/
theorem shfl_pos {d : D} (hF : Fits p L g d ns nv) (hs : d.site.shfl = true) :
    ∃ late n0 v0, PassStart p L g late n0 v0 ∧
      ((∃ r o, Reached p (g / L.block) late r ∧ o ≤ 6 ∧ d.site = scanSite (scanOf late r) o ∧
          ns = n0 + 7 * r + o ∧ nv = v0) ∨
        (∃ R, End p (g / L.block) late R ∧ BalOf p (g / L.block) late R d.bal ∧
          scmp .ge .s (gxv p (g / L.block) late R) (batchOf p late) = false ∧ nv = v0 + 1 ∧
          ((d.site = .pre late ∧ selN d.bal = 2 ∧ ns = n0 + 7 * (R + 1)) ∨
            (d.site = .tiles late ∧ ns = n0 + 7 * (R + 1) + (selN d.bal - 1))))) := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases s with
  | down k =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    refine ⟨k.late, n0, v0, hP, .inl ⟨r, 0, hR.1, by omega, ?_, hns, hnv⟩⟩
    simp only [scanSite, ↓reduceIte]
    rw [← scanRound_scanOf hR]
  | up k j =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    refine ⟨k.late, n0, v0, hP, .inl ⟨r, 1 + j.val, hR.1, by omega, ?_, by omega,
      hnv⟩⟩
    have hj := j.isLt
    simp only [scanSite, show 1 + j.val ≠ 0 by omega, ↓reduceIte, show 1 + j.val ≤ 5 by omega,
      dite_true]
    rw [← scanRound_scanOf hR]
    congr 1
    ext
    simp
  | total k =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    refine ⟨k.late, n0, v0, hP, .inl ⟨r, 6, hR.1, by omega, ?_, hns, hnv⟩⟩
    simp only [scanSite, show (6 : Nat) ≠ 0 by omega, ↓reduceIte, show ¬ (6 : Nat) ≤ 5 by omega,
      dite_false]
    rw [← scanRound_scanOf hR]
  | pre l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -, hB, h0⟩ := hF
    obtain ⟨hEV1, -, -, -, hEVb⟩ := hEV
    exact ⟨l, n0, v0, hP, .inr ⟨R, hEV1, hB, hEVb, hnv,
      .inl ⟨rfl, by simp [selN, h0], hns⟩⟩⟩
  | tiles l =>
    obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -, hB, -⟩ := hF
    obtain ⟨hEV1, -, -, -, hEVb⟩ := hEV
    exact ⟨l, n0, v0, hP, .inr ⟨R, hEV1, hB, hEVb, hnv, .inr ⟨rfl, hns⟩⟩⟩
  | _ => simp [Site.shfl] at hs

/-- The positions of the first pass come before the second pass's start. -/
theorem pass1_lt {n0 v0 R : Nat} (hP : PassStart p L g true n0 v0)
    (hE : End p (g / L.block) false R) {bal : BitVec 64}
    (hB : BalOf p (g / L.block) false R bal) : 7 * (R + 1) + (selN bal - 1) < n0 := by
  simp only [PassStart, ↓reduceIte] at hP
  obtain ⟨R', b', hPk, rfl, -⟩ := hP
  obtain rfl := hE.unique hPk.1
  obtain rfl := hB.unique hPk.2.1
  have := selN_pos bal
  omega

theorem passStart_v0 {late : Bool} {n0 v0 : Nat} (hP : PassStart p L g late n0 v0) :
    v0 = if late then 1 else 0 := by
  cases late
  · simp only [PassStart, Bool.false_eq_true, ↓reduceIte] at hP ⊢; exact hP.2
  · simp only [PassStart, ↓reduceIte] at hP ⊢
    obtain ⟨_, _, _, _, h⟩ := hP
    exact h

theorem passStart_n0 {n0 v0 : Nat} (hP : PassStart p L g false n0 v0) : n0 = 3 := by
  simp [PassStart] at hP; exact hP.1

theorem passStart_ge {late : Bool} {n0 v0 : Nat} (hP : PassStart p L g late n0 v0) : 3 ≤ n0 := by
  cases late
  · simp only [PassStart, Bool.false_eq_true, ↓reduceIte] at hP; omega
  · simp only [PassStart, ↓reduceIte] at hP
    obtain ⟨_, _, _, h, -⟩ := hP
    omega

/-- Every state comes after the startup's three shuffles. -/
theorem fits_three {d : D} (hF : Fits p L g d ns nv) : 3 ≤ ns := by
  cases hs : d.site <;> simp only [Fits, hs] at hF
  case start => omega
  case exit =>
    obtain ⟨_, _, hP, _, _, h⟩ := hF
    have := passStart_ge hP
    rcases h with ⟨-, h, -⟩ | ⟨_, -, -, h, -⟩ <;> omega
  case q0 => obtain ⟨_, _, ⟨-, -, -, -, -, -, -, h, -⟩⟩ := hF; omega
  all_goals first
    | (obtain ⟨_, _, _, hP, _, h, -⟩ := hF; have := passStart_ge hP; omega)
    | (obtain ⟨_, _, ⟨-, -, -, -, -, -, -, h, -⟩, -⟩ := hF; omega)

/-- A position of the first pass comes before the start of the second pass of a lane of the same
CTA. -/
theorem pos1_lt {n0 v0 n1 v1 : Nat} {ns : Nat} (hc : g / L.block = h / L.block)
    (hP : PassStart p L h true n1 v1)
    (hpos : (∃ r o, Reached p (g / L.block) false r ∧ o ≤ 6 ∧ ns = n0 + 7 * r + o) ∨
      (∃ R bal, End p (g / L.block) false R ∧ BalOf p (g / L.block) false R bal ∧
        ns ≤ n0 + 7 * (R + 1) + (selN bal - 1)))
    (hP0 : PassStart p L g false n0 v0) : ns < n1 := by
  obtain rfl := passStart_n0 hP0
  simp only [PassStart, ↓reduceIte] at hP
  obtain ⟨R1, b1, hPk, rfl, -⟩ := hP
  simp only [Picked] at hPk
  rw [← hc] at hPk
  have := selN_pos b1
  rcases hpos with ⟨r, o, hR, ho, rfl⟩ | ⟨R, bal, hE, hB, hle⟩
  · have := hR.le_end hPk.1
    omega
  · obtain rfl := hE.unique hPk.1
    obtain rfl := hB.unique hPk.2.1
    omega

/-- The passes of two lanes of one CTA start at one position. -/
theorem PassStart.same {late : Bool} {n0 v0 n0' v0' : Nat} (hc : g / L.block = h / L.block)
    (hP : PassStart p L g late n0 v0) (hP' : PassStart p L h late n0' v0') :
    n0 = n0' ∧ v0 = v0' := by
  cases late
  · simp only [PassStart, Bool.false_eq_true, ↓reduceIte] at hP hP'; omega
  · simp only [PassStart, ↓reduceIte] at hP hP'
    obtain ⟨R, b, hPk, rfl, rfl⟩ := hP
    obtain ⟨R', b', hPk', rfl, rfl⟩ := hP'
    simp only [Picked] at hPk hPk'
    rw [hc] at hPk
    obtain rfl := hPk.1.unique hPk'.1
    obtain rfl := hPk.2.1.unique hPk'.2.1
    exact ⟨rfl, rfl⟩

/-- **Two lanes of a warp at shuffle sites with one shuffle count are at one site.** -/
theorem shfl_same {d d' : D} (hF : Fits p L g d ns nv) (hF' : Fits p L h d' ns' nv')
    (hc : g / L.block = h / L.block) (hs : d.site.shfl = true) (hs' : d'.site.shfl = true)
    (hn : ns = ns') : d'.site = d.site := by
  obtain ⟨l, n0, v0, hP, hpos⟩ := shfl_pos hF hs
  obtain ⟨l', n0', v0', hP', hpos'⟩ := shfl_pos hF' hs'
  rw [hc] at hpos
  -- the two states are in one pass
  have hl : l = l' := by
    by_contra hne
    have low : ∀ {g h : Nat} {d d' : D} {ns nv ns' nv' n0 v0 n1 v1 : Nat},
        g / L.block = h / L.block →
        PassStart p L g false n0 v0 → PassStart p L h true n1 v1 →
        ((∃ r o, Reached p (g / L.block) false r ∧ o ≤ 6 ∧
            d.site = scanSite (scanOf false r) o ∧ ns = n0 + 7 * r + o ∧ nv = v0) ∨
          (∃ R, End p (g / L.block) false R ∧ BalOf p (g / L.block) false R d.bal ∧
            scmp .ge .s (gxv p (g / L.block) false R) (batchOf p false) = false ∧
            nv = v0 + 1 ∧ ((d.site = .pre false ∧ selN d.bal = 2 ∧ ns = n0 + 7 * (R + 1)) ∨
              (d.site = .tiles false ∧ ns = n0 + 7 * (R + 1) + (selN d.bal - 1))))) →
        ((∃ r o, Reached p (h / L.block) true r ∧ o ≤ 6 ∧
            d'.site = scanSite (scanOf true r) o ∧ ns' = n1 + 7 * r + o ∧ nv' = v1) ∨
          (∃ R, End p (h / L.block) true R ∧ BalOf p (h / L.block) true R d'.bal ∧
            scmp .ge .s (gxv p (h / L.block) true R) (batchOf p true) = false ∧
            nv' = v1 + 1 ∧ ((d'.site = .pre true ∧ selN d'.bal = 2 ∧ ns' = n1 + 7 * (R + 1)) ∨
              (d'.site = .tiles true ∧ ns' = n1 + 7 * (R + 1) + (selN d'.bal - 1))))) →
        ns < ns' := by
      intro g h d d' ns nv ns' nv' n0 v0 n1 v1 hc hP0 hP1 hp hp'
      have hlt : ns < n1 := by
        refine pos1_lt hc hP1 ?_ hP0
        rcases hp with ⟨r, o, hR, ho, -, hns, -⟩ | ⟨R, hE, hB, -, -, hsel⟩
        · exact .inl ⟨r, o, hR, ho, hns⟩
        · refine .inr ⟨R, d.bal, hE, hB, ?_⟩
          rcases hsel with ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> omega
      rcases hp' with ⟨r, o, -, -, -, hns, -⟩ | ⟨R, -, -, -, -, hsel⟩
      · omega
      · rcases hsel with ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> omega
    cases l <;> cases l'
    · exact hne rfl
    · have := low hc hP hP' (by rw [← hc] at hpos; exact hpos) hpos'
      omega
    · have := low hc.symm hP' hP hpos' (by rw [← hc] at hpos; exact hpos)
      omega
    · exact hne rfl
  subst hl
  obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP'
  rcases hpos with ⟨r, o, hR, ho, hsite, hns, hnv⟩ | ⟨R, hE, hB, -, hnv, hsel⟩ <;>
    rcases hpos' with ⟨r', o', hR', ho', hsite', hns', hnv'⟩ | ⟨R', hE', hB', -, hnv', hsel'⟩
  · obtain ⟨rfl, rfl⟩ : r = r' ∧ o = o' := by omega
    rw [hsite, hsite']
  · have := hR.le_end hE'
    have := selN_pos d'.bal
    rcases hsel' with ⟨-, -, h'⟩ | ⟨-, h'⟩ <;> omega
  · have := hR'.le_end hE
    have := selN_pos d.bal
    rcases hsel with ⟨-, -, h'⟩ | ⟨-, h'⟩ <;> omega
  · obtain rfl := hE.unique hE'
    obtain hb := hB.unique hB'
    rw [hb] at hsel
    rcases hsel with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩ <;> rcases hsel' with ⟨h1', h2', h3'⟩ | ⟨h1', h3'⟩
    · rw [h1, h1']
    · omega
    · omega
    · rw [h1, h1']

/-- Where a ballot state stands: after the scan of pass `late` ended at round `R`. -/
theorem vote_pos {d : D} {late : Bool} (hF : Fits p L g d ns nv) (hs : d.site = .vote late) :
    ∃ n0, PassStart p L g late n0 nv ∧ ∃ R, End p (g / L.block) late R ∧
      scmp .ge .s (gxv p (g / L.block) late R) (batchOf p late) = false ∧
      ns = n0 + 7 * (R + 1) := by
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  subst hs
  obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -⟩ := hF
  obtain ⟨hEV1, -, -, -, hEVb⟩ := hEV
  subst hnv
  exact ⟨n0, hP, R, hEV1, hEVb, hns⟩

theorem Picked.cta {R : Nat} {b : BitVec 64} (hc : g / L.block = h / L.block)
    (hP : Picked p L g R b) : Picked p L h R b := by
  simp only [Picked, hc] at hP ⊢
  exact hP

/-- **A shuffle state comes before every ballot state with at least its ballot count.** -/
theorem shfl_lt_vote {d d' : D} {late : Bool} (hF : Fits p L g d ns nv)
    (hF' : Fits p L h d' ns' nv')
    (hc : g / L.block = h / L.block) (hs : d.site.shfl = true) (hs' : d'.site = .vote late)
    (hv : nv ≤ nv') : ns < ns' := by
  obtain ⟨l, n0, v0, hP, hpos⟩ := shfl_pos hF hs
  obtain ⟨n1, hP1, R1, hE1, -, hns1⟩ := vote_pos hF' hs'
  rw [hc] at hpos
  cases l <;> cases late
  · obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP1
    rcases hpos with ⟨r, o, hR, ho, -, hns, hnv⟩ | ⟨R, -, -, -, hnv, -⟩
    · have := hR.le_end hE1
      omega
    · omega
  · have := pos1_lt hc hP1 (n0 := n0) (ns := ns) (by
      rw [← hc] at hpos
      rcases hpos with ⟨r, o, hR, ho, -, hns, -⟩ | ⟨R, hE, hB, -, -, hsel⟩
      · exact .inl ⟨r, o, hR, ho, hns⟩
      · refine .inr ⟨R, d.bal, hE, hB, ?_⟩
        rcases hsel with ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> omega) hP
    omega
  · have h1 := passStart_v0 hP
    have h2 := passStart_v0 hP1
    simp at h1 h2
    rcases hpos with ⟨r, o, -, -, -, -, hnv⟩ | ⟨R, -, -, -, hnv, -⟩ <;> omega
  · obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP1
    rcases hpos with ⟨r, o, hR, ho, -, hns, hnv⟩ | ⟨R, -, -, -, hnv, -⟩
    · have := hR.le_end hE1
      omega
    · omega

/-- **A shuffle state comes before every return.** -/
theorem shfl_lt_exit {d : D} {late : Bool} {nsx nvx : Nat} (hF : Fits p L g d ns nv)
    (hc : g / L.block = h / L.block) (hs : d.site.shfl = true)
    (hx : Fits.ExitAt p L h late nsx nvx) : ns < nsx := by
  obtain ⟨l, n0, v0, hP, hpos⟩ := shfl_pos hF hs
  obtain ⟨n1, v1, hP1, R1, hE1, hx⟩ := hx
  rw [hc] at hpos
  have hsame : l = late → ns < nsx := by
    intro hl
    subst hl
    obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP1
    rcases hpos with ⟨r, o, hR, ho, -, hns, -⟩ | ⟨R, hE, hB, hgx, -, hsel⟩
    · have := hR.le_end hE1
      rcases hx with ⟨-, h3, -⟩ | ⟨b, -, -, h3, -⟩ <;> omega
    · obtain rfl := hE.unique hE1
      rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, h3, -⟩
      · rw [hg] at hgx; cases hgx
      · obtain rfl := hB.unique hb
        have := selN_pos d.bal
        rcases hsel with ⟨-, -, h4⟩ | ⟨-, h4⟩ <;> omega
  cases l <;> cases late
  · exact hsame rfl
  · have := pos1_lt hc hP1 (n0 := n0) (ns := ns) (by
      rw [← hc] at hpos
      rcases hpos with ⟨r, o, hR, ho, -, hns, -⟩ | ⟨R, hE, hB, -, -, hsel⟩
      · exact .inl ⟨r, o, hR, ho, hns⟩
      · refine .inr ⟨R, d.bal, hE, hB, ?_⟩
        rcases hsel with ⟨-, -, h3⟩ | ⟨-, h3⟩ <;> omega) hP
    rcases hx with ⟨-, h3, -⟩ | ⟨b, -, -, h3, -⟩ <;> omega
  · -- the lane is in the second pass, the other returned from the first
    exfalso
    simp only [PassStart, ↓reduceIte] at hP
    obtain ⟨Rp, bp, hPk, -, -⟩ := hP
    have hPk' := hPk.cta hc
    obtain rfl := hPk'.1.unique hE1
    rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, -, -, hnp⟩
    · exact absurd (hg.symm.trans hPk'.2.2.1) (by simp)
    · obtain rfl := hPk'.2.1.unique hb
      exact hnp rfl hPk'
  · exact hsame rfl

/-- **No lane returns before a ballot that another lane of its warp makes**: a return with at
most the ballot's count of ballots is impossible. -/
theorem vote_exit {d : D} {late late' : Bool} {nsx nvx : Nat} (hF : Fits p L g d ns nv)
    (hc : g / L.block = h / L.block) (hs : d.site = .vote late)
    (hx : Fits.ExitAt p L h late' nsx nvx) (hv : nvx ≤ nv) : False := by
  obtain ⟨n0, hP, R, hE, hgx, -⟩ := vote_pos hF hs
  obtain ⟨n1, v1, hP1, R1, hE1, hx⟩ := hx
  have h0 := passStart_v0 hP
  have h1 := passStart_v0 hP1
  rw [hc] at hE hgx
  cases late <;> cases late'
  · obtain rfl := hE.unique hE1
    rcases hx with ⟨hg, -, -⟩ | ⟨b, -, -, -, h3, -⟩
    · rw [hg] at hgx; cases hgx
    · simp at h0 h1; omega
  · simp at h0 h1; rcases hx with ⟨-, -, h3⟩ | ⟨b, -, -, -, h3, -⟩ <;> omega
  · simp only [PassStart, ↓reduceIte] at hP
    obtain ⟨Rp, bp, hPk, -, -⟩ := hP
    have hPk' := hPk.cta hc
    obtain rfl := hPk'.1.unique hE1
    rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, -, -, hnp⟩
    · exact absurd (hg.symm.trans hPk'.2.2.1) (by simp)
    · obtain rfl := hPk'.2.1.unique hb
      exact hnp rfl hPk'
  · obtain rfl := hE.unique hE1
    rcases hx with ⟨hg, -, -⟩ | ⟨b, -, -, -, h3, -⟩
    · rw [hg] at hgx; cases hgx
    · simp at h0 h1; omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
