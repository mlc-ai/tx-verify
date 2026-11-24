-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
public import Kernels.TmlFa4Fwd.Proof.Progress.OutputColl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's collectives, by their number

Two lanes of the output warp at collective sites with as many collectives before them are at one
site (`out_site_same`), and a lane returns after more collectives than a lane at one has made
(`out_lt_exit`). The pass is a function of the CTA and the number (`Progress.Late`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (Late)

noncomputable section

variable {p : Params} {L : Launch} {g h ns nv ns' nv' : Nat}

/-- Where a collective site stands in pass `l`: `q` collectives after the pass's start. -/
def Pos (p : Params) (c : Nat) (l : Bool) (q : Nat) (s : Site) : Prop :=
  (∃ r o, Reached p c l r ∧ o ≤ 6 ∧ q = 7 * r + o ∧ s = scanSite (scanOf l r) o) ∨
    (∃ R, End p c l R ∧ q = 7 * (R + 1) ∧ s = .vote l ∧
      scmp .ge .s (gxv p c l R) (batchOf p l) = false) ∨
    ∃ R b, End p c l R ∧ BalOf p c l R b ∧ scmp .ge .s (gxv p c l R) (batchOf p l) = false ∧
      ((selN b = 2 ∧ q = 7 * (R + 1) + 1 ∧ s = .pre l) ∨
        (q = 7 * (R + 1) + selN b ∧ s = .tiles l))

/-- A number of collectives of a pass is at one site. -/
theorem Pos.unique {c : Nat} {l : Bool} {q : Nat} {s s' : Site} (h : Pos p c l q s)
    (h' : Pos p c l q s') : s = s' := by
  rcases h with ⟨r, o, hR, ho, hq, rfl⟩ | ⟨R, hE, hq, rfl, -⟩ | ⟨R, b, hE, hB, -, h⟩ <;>
    rcases h' with ⟨r', o', hR', ho', hq', rfl⟩ | ⟨R', hE', hq', rfl, -⟩ | ⟨R', b', hE', hB', -, h'⟩
  · obtain ⟨rfl, rfl⟩ : r = r' ∧ o = o' := by omega
    rfl
  · have := hR.le_end hE'
    omega
  · have := hR.le_end hE'
    have := selN_pos b'
    rcases h' with ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> omega
  · have := hR'.le_end hE
    omega
  · rfl
  · obtain rfl := hE.unique hE'
    have := selN_pos b'
    rcases h' with ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> omega
  · have := hR'.le_end hE
    have := selN_pos b
    rcases h with ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> omega
  · obtain rfl := hE.unique hE'
    have := selN_pos b
    rcases h with ⟨-, h1, -⟩ | ⟨h1, -⟩ <;> omega
  · obtain rfl := hE.unique hE'
    obtain rfl := hB.unique hB'
    rcases h with ⟨h0, h1, rfl⟩ | ⟨h1, rfl⟩ <;> rcases h' with ⟨h0', h1', rfl⟩ | ⟨h1', rfl⟩ <;>
      first | rfl | omega

/-- **The position of a collective site.** -/
theorem coll_pos {d : D} (hF : Fits p L g d ns nv) (hs : Progress.Out.coll d.site = true) :
    ∃ l n0 v0 q, PassStart p L g l n0 v0 ∧ ns + nv = n0 + v0 + q ∧
      Pos p (g / L.block) l q d.site := by
  cases hsh : d.site.shfl with
  | true =>
    obtain ⟨l, n0, v0, hP, h⟩ := shfl_pos hF hsh
    rcases h with ⟨r, o, hR, ho, hsite, hns, hnv⟩ | ⟨R, hE, hB, hgx, hnv, h⟩
    · exact ⟨l, n0, v0, 7 * r + o, hP, by omega, .inl ⟨r, o, hR, ho, rfl, hsite⟩⟩
    · have := selN_pos d.bal
      rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
      · exact ⟨l, n0, v0, 7 * (R + 1) + 1, hP, by omega,
          .inr (.inr ⟨R, d.bal, hE, hB, hgx, .inl ⟨h2, rfl, h1⟩⟩)⟩
      · exact ⟨l, n0, v0, 7 * (R + 1) + selN d.bal, hP, by omega,
          .inr (.inr ⟨R, d.bal, hE, hB, hgx, .inr ⟨rfl, h1⟩⟩)⟩
  | false =>
    obtain ⟨l, hl⟩ : ∃ l, d.site = .vote l := by
      simp only [Progress.Out.coll, hsh, Bool.false_or] at hs
      revert hs
      cases d.site <;> simp [Site.ballot]
    obtain ⟨n0, hP, R, hE, hgx, hns⟩ := vote_pos hF hl
    exact ⟨l, n0, nv, 7 * (R + 1), hP, by omega, .inr (.inl ⟨R, hE, rfl, hl, hgx⟩)⟩

/-- The pass of a position is a function of the CTA and the number. -/
theorem pos_late {l : Bool} {n0 v0 q : Nat} {s : Site} (hP : PassStart p L g l n0 v0)
    (hq : Pos p (g / L.block) l q s) : Late p (g / L.block) (n0 + v0 + q) ↔ l = true := by
  cases l with
  | true => exact ⟨fun _ => rfl, fun _ => Progress.late_of_passStart hP (by omega)⟩
  | false =>
    refine ⟨fun h => ?_, fun h => by cases h⟩
    exfalso
    simp only [PassStart, Bool.false_eq_true, ↓reduceIte] at hP
    obtain ⟨rfl, rfl⟩ := hP
    rcases hq with ⟨r, o, hR, ho, rfl, -⟩ | ⟨R, hE, rfl, -, -⟩ | ⟨R, b, hE, hB, -, hq⟩
    · exact Progress.not_late_reached hR (n := 3 + 0 + (7 * r + o)) (by omega) h
    · refine Progress.not_late_of_end (L := L) (g := g) hE
        (n := 3 + 0 + 7 * (R + 1)) (fun bal _ => ?_) h
      have := selN_pos bal
      omega
    · refine Progress.not_late_of_end (L := L) (g := g) hE (n := 3 + 0 + q)
        (fun bal hb => ?_) h
      obtain rfl := hB.unique hb
      have := selN_pos b
      rcases hq with ⟨h0, rfl, -⟩ | ⟨rfl, -⟩ <;> omega

/-- **Two lanes of the output warp at collective sites with one number are at one site.** -/
theorem out_site_same {d d' : D} (hF : Fits p L g d ns nv) (hF' : Fits p L h d' ns' nv')
    (hc : g / L.block = h / L.block) (hs : Progress.Out.coll d.site = true)
    (hs' : Progress.Out.coll d'.site = true) (hn : ns + nv = ns' + nv') : d.site = d'.site := by
  obtain ⟨l, n0, v0, q, hP, h1, hq⟩ := coll_pos hF hs
  obtain ⟨l', n0', v0', q', hP', h1', hq'⟩ := coll_pos hF' hs'
  have e1 := pos_late hP hq
  have e2 := pos_late hP' hq'
  rw [← h1] at e1
  rw [← h1', ← hn, ← hc] at e2
  have hl : l = l' := by
    have := e1.symm.trans e2
    cases l <;> cases l' <;> simp_all
  subst hl
  obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP'
  obtain rfl : q = q' := by omega
  rw [hc] at hq
  exact hq.unique hq'

/-- **A collective position is before every return.** -/
theorem pos_lt_exit {late l : Bool} {n0 v0 q : Nat} {s : Site} (hP : PassStart p L g l n0 v0)
    (hq : Pos p (g / L.block) l q s) (hc : g / L.block = h / L.block)
    (hx : Fits.ExitAt p L h late ns' nv') : n0 + v0 + q < ns' + nv' := by
  have e1 := pos_late hP hq
  obtain ⟨n1, v1, hP1, R1, hE1, hx⟩ := hx
  have hge : n1 + v1 ≤ ns' + nv' := by
    rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega
  have hsame : l = late → n0 + v0 + q < ns' + nv' := by
    rintro rfl
    obtain ⟨rfl, rfl⟩ := PassStart.same hc hP hP1
    rw [hc] at hq
    rcases hq with ⟨r, o, hR, ho, rfl, -⟩ | ⟨R, hE, rfl, -, hgx⟩ | ⟨R, b, hE, hB, hgx, hq⟩
    · have := hR.le_end hE1
      rcases hx with ⟨-, h3, h4⟩ | ⟨b, -, -, h3, h4, -⟩ <;> omega
    · obtain rfl := hE.unique hE1
      rcases hx with ⟨hg, -, -⟩ | ⟨b, -, -, h3, h4, -⟩
      · rw [hg] at hgx; cases hgx
      · omega
    · obtain rfl := hE.unique hE1
      have := selN_pos b
      rcases hx with ⟨hg, -, -⟩ | ⟨b', hb', -, h3, h4, -⟩
      · rw [hg] at hgx; cases hgx
      · obtain rfl := hB.unique hb'
        rcases hq with ⟨-, h5, -⟩ | ⟨h5, -⟩ <;> omega
  cases l <;> cases late
  · exact hsame rfl
  · by_contra hcon
    have hl : Late p (g / L.block) (n0 + v0 + q) := by
      rw [hc]; exact Progress.late_of_passStart hP1 (by omega)
    exact absurd (e1.mp hl) (by simp)
  · exfalso
    simp only [PassStart, ↓reduceIte] at hP
    obtain ⟨Rp, bp, hPk, -, -⟩ := hP
    have hPk' := hPk.cta hc
    obtain rfl := hPk'.1.unique hE1
    rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, -, -, hnp⟩
    · exact absurd (hg.symm.trans hPk'.2.2.1) (by simp)
    · obtain rfl := hPk'.2.1.unique hb
      exact hnp rfl hPk'
  · exact hsame rfl

/-- **A lane at a collective has made fewer than a lane that returned.** -/
theorem out_lt_exit {d : D} {late : Bool} (hF : Fits p L g d ns nv)
    (hc : g / L.block = h / L.block) (hs : Progress.Out.coll d.site = true)
    (hx : Fits.ExitAt p L h late ns' nv') : ns + nv < ns' + nv' := by
  obtain ⟨l, n0, v0, q, hP, h1, hq⟩ := coll_pos hF hs
  rw [h1]
  exact pos_lt_exit hP hq hc hx

/-- A return of the first pass is of a CTA that picked no tile. -/
theorem exit_not_picked {R : Nat} {bal : BitVec 64} (hx : Fits.ExitAt p L h false ns nv)
    (hP : Picked p L h R bal) : False := by
  obtain ⟨n1, v1, -, R1, hE1, hx⟩ := hx
  obtain rfl := hP.1.unique hE1
  rcases hx with ⟨hg, -, -⟩ | ⟨b, hb, -, -, -, hnp⟩
  · exact absurd (hg.symm.trans hP.2.2.1) (by simp)
  · obtain rfl := hP.2.1.unique hb
    exact hnp rfl hP

/-- A return is after eleven collectives. -/
theorem exit_ge {late : Bool} (hx : Fits.ExitAt p L h late ns nv) : 10 ≤ ns + nv := by
  obtain ⟨n1, v1, hP, R1, -, hx⟩ := hx
  have := passStart_ge hP
  rcases hx with ⟨-, h3, -⟩ | ⟨b, -, -, h3, -⟩ <;> omega

/-- A position of a pass is at a site of the pass. -/
theorem Pos.late {c : Nat} {l : Bool} {q : Nat} {s : Site} (h : Pos p c l q s) : s.late = l := by
  rcases h with ⟨r, o, -, -, -, rfl⟩ | ⟨R, -, -, rfl, -⟩ | ⟨R, b, -, -, -, h⟩
  · have hk : (scanOf l r).late = l := by
      unfold scanOf; cases l <;> by_cases h0 : r = 0 <;> simp [h0, Scan.late]
    unfold scanSite
    split_ifs <;> exact hk
  · rfl
  · rcases h with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- Two lanes at the choice's shuffles hold one ballot. -/
theorem bal_same {d d' : D} {l : Bool} {ns nv ns' nv' : Nat}
    (hc : g / L.block = h / L.block) (hF : Fits p L g d ns nv)
    (hF' : Fits p L h d' ns' nv') (hd : d.site = .pre l ∨ d.site = .tiles l)
    (he : d'.site = d.site) : d.bal = d'.bal := by
  have key : ∀ {g : Nat} {d : D} {ns nv : Nat}, Fits p L g d ns nv →
      (d.site = .pre l ∨ d.site = .tiles l) → ∃ R, End p (g / L.block) l R ∧
        BalOf p (g / L.block) l R d.bal := by
    intro g d ns nv hF hd
    rcases hd with hd | hd <;> simp only [Fits, hd] at hF
    · obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -, hB, h0⟩ := hF
      exact ⟨R, hEV.1, hB⟩
    · obtain ⟨R, n0, v0, hP, hEV, hns, hnv, -, hB, -⟩ := hF
      exact ⟨R, hEV.1, hB⟩
  obtain ⟨R, hE, hB⟩ := key hF hd
  obtain ⟨R', hE', hB'⟩ := key hF' (by rw [he]; exact hd)
  rw [hc] at hE hB
  obtain rfl := hE.unique hE'
  exact hB.unique hB'

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
