-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Tmem
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # What a correction lane's Tensor Memory access follows

A rescale access of credit `q` follows `q + 1` events of the lane's named barrier with the softmax
warp of the stage, and `q` is at most the tile's rescale rounds; a final access follows a
successful poll of the stage's O-full barrier (`corr_route`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem o_sites : allSites.all (fun s =>
    (pollOff s != 144 || s == .fw 0 0) && (pollOff s != 152 || s == .fw 1 0)) = true := by
  decide +kernel

private theorem o_tab : ∀ st : Fin 2,
    (pollPts (144 + 8 * st.val)).countP (before (.fw st 0)) = 0 ∧
      (pollPts (144 + 8 * st.val)).countP inRound = 0 := by
  decide

/-- The named-barrier points before a rescale access, and the O-full polls before a final one. -/
def routeOk (st : Fin 2) : Bool :=
  decide ((nbPts st).countP inRound = 1) &&
    decide ((pollPts (144 + 8 * st.val)).countP inRound = 0) &&
    ((List.finRange 8).all fun c => decide ((nbPts st).countP (before (.rld st c)) = 2) &&
      decide ((nbPts st).countP (before (.rst st c)) = 2)) &&
    (List.finRange 16).all fun c =>
      decide ((pollPts (144 + 8 * st.val)).countP (before (.fld st c)) = 1)

theorem route_tab : ∀ st, routeOk st = true := by decide +kernel

theorem loop_sites : ∀ st c, (inRound (Site.rld st c).pc = true ∧
    CorrWarp.epi (.rld st c) = .ready 0 ∧ (Site.rld st c).hasUk = true) ∧
    inRound (Site.rst st c).pc = true ∧
    CorrWarp.epi (.rst st c) = .ready 0 ∧ (Site.rst st c).hasUk = true := by
  intro st c
  refine ⟨⟨?_, rfl, ?_⟩, ?_, rfl, ?_⟩ <;> revert st c <;> decide

theorem tail_sites : ∀ st c, tailR (Site.fld st c) = true ∧
    CorrWarp.epi (.fld st c) = .ready 0 ∧ (Site.fld st c).hasUk = true := by
  intro st c
  refine ⟨?_, rfl, ?_⟩ <;> revert st c <;> decide

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- The tile's rescale rounds at a rescale state. -/
theorem corr_rounds {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) {d : Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hep : CorrWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true) :
    CorrRounds p L g ((Bs p L g d.scheduler.v).toNat - 1) := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n', hσ', -⟩ |
    ⟨d', n', hσ', h0, hR, -⟩
  · rw [hσ] at hσ'
    simp [CorrWarp.cinj] at hσ'
  · rw [hσ] at hσ'
    simp only [CorrWarp.cinj, Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq,
      heq_eq_eq, true_and] at hσ'
    obtain ⟨rfl, -⟩ := hσ'
    obtain ⟨-, rv, -, -, hFE, hu⟩ := hR h0
    simp only [Epilogue.Fits, CorrWarp.toE, show d.scheduler.site = d.site from rfl, hep] at hFE
    obtain ⟨R, bal, hC, h0', h1⟩ := hFE
    have hb := CorrWarp.bs_ref hC h0' h1 (hu huk)
    exact ⟨R, bal, hC.1, by rw [hb]; rfl⟩

/-- A rescale state's route. -/
theorem round_route {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) {d : Control.D} {n : Cls → Nat} {r ℓ : Nat} {st : Fin 2}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hQ : RefQ p L g d (CorrWarp.rc n) r ℓ)
    (hs : (∃ c, d.site = .rld st c) ∨ ∃ c, d.site = .rst st c) :
    ((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st.val)) =
        Tm.pArr L X g st k + 1 ∧
      ∃ R, CorrRounds p L g R ∧ Tm.pArr L X g st k ≤ R := by
  have ht := route_tab st
  simp only [routeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨h1, -⟩, h2⟩, -⟩ := ht
  have hnb : n (.corr (.nb st)) = (nbPts st).countP (before d.site) + r * 1 := by
    rw [← h1]
    exact hQ.cnt (.nb st) (by simp)
  rw [corr_isBarId hw hw1, count hσ, hnb]
  rcases hs with ⟨c, hs⟩ | ⟨c, hs⟩
  · obtain ⟨⟨a1, a2, a3⟩, -⟩ := loop_sites st c
    have harr := site_arr hσ hQ (st := st) (.inl ⟨c, hs⟩)
    have hl := hQ.loop (by change inRound d.site.pc = true; rw [hs]; exact a1)
    have hr := corr_rounds hp hX hFw hw hw1 he hub hσ (by rw [hs]; exact a2) (by rw [hs]; exact a3)
    have hb := (h2 c (List.mem_finRange c)).1
    rw [hs, hb, harr]
    exact ⟨by omega, _, hr, by omega⟩
  · obtain ⟨-, a1, a2, a3⟩ := loop_sites st c
    have harr := site_arr hσ hQ (st := st) (.inr (.inl ⟨c, hs⟩))
    have hl := hQ.loop (by change inRound d.site.pc = true; rw [hs]; exact a1)
    have hr := corr_rounds hp hX hFw hw hw1 he hub hσ (by rw [hs]; exact a2) (by rw [hs]; exact a3)
    have hb := (h2 c (List.mem_finRange c)).2
    rw [hs, hb, harr]
    exact ⟨by omega, _, hr, by omega⟩

/-- **What a Tensor Memory access of a correction lane follows**, and the tile's rescale rounds. -/
theorem corr_route {k a st : Nat} {vals : List Value} {sh : TcShape}
    (hl : X.TLd (g, k) a vals sh ∨ X.TSt (g, k) a vals sh)
    (hcol : 256 + 128 * st ≤ a % 65536) (hcol' : a % 65536 < 384 + 128 * st) (hst : st < 2) :
    (((X.tr g).take k).countP (Execution.isBarId (Prologue.warpIndex L g - 5 + 4 * st)) =
        Tm.pArr L X g st k + 1 ∧ ∃ R, CorrRounds p L g R ∧ Tm.pArr L X g st k ≤ R) ∨
      1 ≤ okPolls (Tm.oFull L (g / L.block) st) ((X.tr g).take k) ∧
        ∃ R, CorrRounds p L g R ∧ Tm.pArr L X g st k = R + 1 := by
  rcases hl with hl | hl
  · obtain ⟨d, n, r, ℓ, hσ, hQ, -, st', hs⟩ := corr_ld_state hp hX hFw hw hw1 hl
    obtain ⟨pc, he⟩ := hl
    have hst' := st'.isLt
    rcases hs with ⟨c, hs, h1, -⟩ | ⟨c, hs, h1, -⟩ <;> have hc := c.isLt <;>
      obtain rfl : st = st'.val := by omega
    · exact .inl (round_route hp hX hFw hw hw1 he (by intro f h; cases h) hσ hQ (.inl ⟨c, hs⟩))
    · right
      have ht := route_tab st'
      simp only [routeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
      obtain ⟨⟨⟨-, h1'⟩, -⟩, h2⟩ := ht
      have hp' : n (.corr (.acquire (144 + 8 * st'.val))) =
          (pollPts (144 + 8 * st'.val)).countP (before d.site) + r * 0 := by
        rw [← h1']
        exact hQ.cnt (.acquire (144 + 8 * st'.val)) (by simp)
      have hk := corr_okPolls (L := L) (g := g) (X := X) (k := k) (144 + 8 * st'.val)
      rw [count hσ, hp', hs, h2 c (List.mem_finRange c)] at hk
      obtain ⟨t1, t3, t4⟩ := tail_sites st' c
      have harr := site_arr hσ hQ (st := st') (.inr (.inr ⟨c, hs⟩))
      have ht := hQ.tail (by change tailR d.site = true; rw [hs]; exact t1)
      exact ⟨hk.ge, _, corr_rounds hp hX hFw hw hw1 he (by intro f h; cases h) hσ
        (by rw [hs]; exact t3) (by rw [hs]; exact t4), by rw [harr]; omega⟩
  · obtain ⟨d, n, r, ℓ, hσ, hQ, -, st', c, hs, h1, -⟩ := corr_st_state hp hX hFw hw hw1 hl
    obtain ⟨pc, he⟩ := hl
    have hst' := st'.isLt
    have hc := c.isLt
    obtain rfl : st = st'.val := by omega
    exact .inl (round_route hp hX hFw hw hw1 he (by intro f h; cases h) hσ hQ (.inr ⟨c, hs⟩))

/-- **A poll of an O-full barrier** has parity 0 and is the lane's first successful one. -/
theorem corr_o_poll {k pc par st : Nat} {ok acq : Bool} {sc : MbarScope} (hst : st < 2)
    (he : X.get (g, k) = some ⟨pc, .wait (Tm.oFull L (g / L.block) st) par ok acq sc⟩) :
    par = 0 ∧ acq = true ∧ sc = .cta ∧
      okPolls (Tm.oFull L (g / L.block) st) ((X.tr g).take k) = 0 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := Tm.oFull L (g / L.block) st) rfl
    cases hc
  have hl : 144 + 8 * st = pollOff d.site := by
    rcases corr_mbar2 hev (l := Tm.oFull L (g / L.block) st) rfl with ⟨hk, -⟩ | ⟨_, _, -, hl, -⟩
    · cases hk
    · simp only [Tm.oFull, Tm.bar, bl, Loc.mk.injEq, true_and] at hl
      omega
  have hs : d.site = .fw ⟨st, hst⟩ 0 := by
    have h1 := List.all_eq_true.mp o_sites d.site (mem_allSites d.site)
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h1
    obtain ⟨h0, h1⟩ := h1
    interval_cases st
    · exact h0.resolve_left (fun h => h hl.symm)
    · exact h1.resolve_left (fun h => h hl.symm)
  have hcnt := hQ.cnt (.acquire (144 + 8 * st)) (by simp)
  have ht := o_tab ⟨st, hst⟩
  obtain ⟨t1, t2⟩ := ht
  have h0 : okPolls (Tm.oFull L (g / L.block) st) ((X.tr g).take k) = 0 := by
    have hk := corr_okPolls (L := L) (g := g) (X := X) (k := k) (144 + 8 * st)
    rw [hc, hcnt, hs] at hk
    refine hk.trans ?_
    show (pollPts (144 + 8 * st)).countP _ + r * (pollPts (144 + 8 * st)).countP _ = 0
    rw [t1, t2, Nat.mul_zero]
  obtain ⟨site, v, kk⟩ := d
  simp only at hs
  subst hs
  simp only [Ev, pollPar, Kind.wait.injEq] at hev
  obtain ⟨_, -, h1, -, h2, h3⟩ := hev
  exact ⟨h1, h2, h3, h0⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
