-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Lib.CollKind
public import Kernels.TmlFa4Fwd.Proof.Lib.CollSched
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The warp collectives of the correction warps

Besides the scheduler's shuffles and ballots, a correction lane makes a ballot in every rescale
stage. `corrMid` places them in the pipeline's slots. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandC primeBase endBase bmax)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (selN Picked)
open PTX.Kernels.TmlFa4Fwd.Proof.CorrWarp (rvN refV)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The correction warps' sites whose event is a warp collective. -/
def Correction.Site.wcoll : Correction.Site → Bool
  | .down _ | .up _ _ | .total _ | .vote _ | .pre _ | .tiles _ | .rvote _ => true
  | _ => false

/-- **The kind of a correction event.** -/
theorem corr_ev_kind {d : Correction.Control.D} {e : Event}
    (hev : Correction.Control.Ev p L g d e) (hub : ∀ f, e.kind ≠ .ub f) :
    CollKind e.kind d.site.wcoll ∧ isElectEv e = false := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s <;> simp only [Correction.Control.Ev, Correction.Ev, Correction.Control.D.scheduler,
    Correction.rdOrUb, Epilogue.Ev, Correction.Site.toE] at hev
  all_goals shape_destruct hev
  all_goals first
    | exact absurd rfl (hub _)
    | (refine ⟨?_, rfl⟩
       first
         | exact .shfl _ _ _ _ _ _
         | exact .vote _ _ _ (by norm_num)
         | exact .bar _ _ _
         | exact .rd _ _
         | exact .wait _ _ _ _ _
         | exact .tc _
         | exact .exit
         | exact .setMax _ _ _
         | exact .wr _ _
         | exact .arrive _ _ _ _ _
         | exact .fenceProxy _ _)

/-- Whether a thread state of a correction warp is at a collective site. -/
def corrAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Bool :=
  match σ with
  | (.inl s, _) => match s.site with | .sh _ => true | _ => false
  | (.inr ⟨.correction, d⟩, _) => d.site.wcoll
  | _ => false

private theorem CollKind.coll {pc : Nat} {k : Kind} {b : Bool} (h : CollKind k b)
    (he : isElectEv ⟨pc, k⟩ = false) : Sched.isWarpColl ⟨pc, k⟩ = b ∧
      Sched.isWarpColl ⟨pc, k⟩ = isColl ⟨pc, k⟩ := by
  obtain ⟨h1, h2⟩ := h.counts (pc := pc)
  refine ⟨h1, ?_⟩
  rw [he] at h2
  cases hw : Sched.isWarpColl ⟨pc, k⟩ <;> cases hc : isColl ⟨pc, k⟩ <;> rw [hw, hc] at h2 <;>
    simp at h2 ⊢

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
  (hg : g < L.threads) {w : Nat} (hw8 : 8 ≤ w ∧ w ≤ 11) (hw : Prologue.warpIndex L g = w)
include hp hX hub hg hw8 hw

/-- **An event of a correction warp** is a warp collective exactly at a collective site, and is a
shuffle or a full ballot. -/
theorem corr_event_coll {k : Nat} {σ : (thread p L g).D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Sched.isWarpColl e = corrAt p L g σ ∧ Sched.isWarpColl e = isColl e := by
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => hub ⟨(g, k), e.pc, f, by
    rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hR := (CorrWarp.good hp hX hw8 hg hw k).2 _ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · have hS := hR.1
    obtain ⟨hev, -⟩ := start_fired hp hX he hσ
    obtain ⟨pc, kind⟩ := e
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, h⟩ := hev <;> subst h <;>
        exact ⟨rfl, rfl⟩
    case fence => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩
    case bar => simp only [Startup.Ev] at hev; subst hev; exact ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := corr_ev_kind (CorrWarp.fired_both hp hX he hσ hne).1 hne
    exact h1.coll h2

/-- **The collectives before a state of a correction warp.** -/
theorem corr_cnt_eq {k : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP Sched.isWarpColl = σ.2 .shfl + σ.2 .vote := by
  have h1 : ((X.tr g).take k).countP Sched.isWarpColl = ((X.tr g).take k).countP isColl := by
    clear hσ
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.take_add_one]
      cases he : (X.tr g)[k]? with
      | none => simpa using ih
      | some e =>
        have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := fun pc f hf =>
          hub ⟨(g, k), pc, f, show (X.tr g)[k]? = _ by rw [he, hf]⟩
        obtain ⟨σ', hσ', -⟩ := good_state hp hX (show X.get (g, k) = some e from he) hne
          (CorrWarp.good hp hX hw8 hg hw k)
        have := (corr_event_coll hp hX hub hg hw8 hw (show X.get (g, k) = some e from he) hσ').2
        simp only [Option.toList_some, List.countP_append, List.countP_singleton, this, ih]
  obtain ⟨hs, hv⟩ := counts hσ
  rw [h1, countColl, hs, hv]

end

/-! ### The rounds -/

/-- What a correction lane's tile fixes: the first pass's collectives, the rescale ballots. -/
@[ext]
structure CorrTile where
  ch : Nat
  V : Nat

/-- **The correction lane's tile.** -/
def IsCorrTile (p : Params) (L : Launch) (w c g : Nat) (a : CorrTile) : Prop :=
  g < L.threads ∧ Prologue.warpIndex L g = w ∧ g / L.block = c ∧ a.V / 2 + 1 ≤ bmax p ∧
    ∃ R bal, Picked p L g R bal ∧ a.ch = 4 + 7 * (R + 1) + selN bal ∧
      a.V = rvN (Correction.Bs p L g (refV p L g R bal))

theorem IsCorrTile.same (hp : Pre p L m) {w c : Nat} {a b : CorrTile}
    (hc : h / L.block = g / L.block) (hT : IsCorrTile p L w c g a)
    (hT' : IsCorrTile p L w c h b) : b = a := by
  obtain ⟨hg, -, -, -, R, bal, hP, h1, h2⟩ := hT
  obtain ⟨hh, -, -, -, R', bal', hP', h1', h2'⟩ := hT'
  obtain ⟨rfl, rfl⟩ := (Epilogue.Picked.cta hc hP').unique hP
  rw [bs_warp hp hh hg hc] at h2'
  exact CorrTile.ext (h1'.trans h1.symm) (h2'.trans h2.symm)

/-- **Where a state of the rounds stands.** -/
def CorrM (p : Params) (a : CorrTile) (N t : Nat) (o : Option Correction.Site) : Prop :=
  (o = none ∧ N = a.ch ∧ t < primeBase p + 8) ∨
  (o = none ∧ ∃ j, j ≤ a.V ∧ N = a.ch + j ∧ t < endBase p ∧
    (j < a.V → t < clk p (1 + j / 2) (bandC (j % 2) + 4))) ∨
  ∃ (r : Nat) (st : Fin 2), 2 * r + st.val < a.V ∧ 1 + r ≤ bmax p ∧
    N = a.ch + (2 * r + st.val) ∧ t = clk p (1 + r) (bandC st.val + 4) ∧ o = some (.rvote st)

/-- **The correction warps' rounds** (warp `w` of CTA `c`). -/
def corrMid (hp : Pre p L m) (w c : Nat) : Mid p L Correction.Site CorrTile where
  tile := IsCorrTile p L w c
  ch a := a.ch
  tot a := a.V
  M := CorrM p
  same := fun hc hT hT' => IsCorrTile.same hp hc hT hT'
  picked := fun hT => by
    obtain ⟨-, -, -, -, R, bal, hP, h1, -⟩ := hT
    exact ⟨R, bal, hP, h1⟩
  ge := by
    rintro a N t o (⟨-, h, -⟩ | ⟨-, j, -, h, -⟩ | ⟨r, st, -, -, h, -⟩) <;> omega
  tge := by
    rintro a N t x (⟨h, -⟩ | ⟨h, -⟩ | ⟨r, st, -, -, -, h, -⟩)
    · cases h
    · cases h
    · have := Progress.primeBase_le_clk p (1 + r) (bandC st.val + 4)
      omega
  lt_tot := by
    rintro a N t x (⟨h, -⟩ | ⟨h, -⟩ | ⟨r, st, h1, -, h2, -⟩)
    · cases h
    · cases h
    · omega
  lt_end := by
    rintro g a N t o - - h
    have hend : Progress.tailBase p + 4096 = endBase p := rfl
    have hpt : primeBase p + 1024 ≤ Progress.tailBase p := Progress.primeBase_le_clk p _ _
    rcases h with ⟨-, -, h⟩ | ⟨-, j, -, -, h, -⟩ | ⟨r, st, -, hb, -, h, -⟩
    · omega
    · exact h
    · have hst := st.isLt
      have := Progress.clk_lt_tail (p := p) (a := 1 + r) (o := bandC st.val + 4)
        (by simp only [bandC, Progress.span]; omega)
      rw [Progress.slotOf_eq hb] at this
      omega
  order := by
    rintro a N N' t t' x o (⟨h, -⟩ | ⟨h, -⟩ | ⟨r, st, h1, hb, h2, h3, h4⟩) hH hle
    · cases h
    · cases h
    have hT8 := Progress.primeBase_le_clk p (1 + r) (bandC st.val + 4)
    have hst := st.isLt
    rcases hH with ⟨-, -, h⟩ | ⟨-, j, hj, hN, -, h⟩ | ⟨r', st', -, hb', hN, h, ho⟩
    · left; omega
    · left
      have hjle : j ≤ 2 * r + st.val := by omega
      refine (h (by omega)).trans_le ?_
      rw [h3]
      rcases Nat.lt_or_ge (j / 2) r with h5 | h5
      · exact (Progress.clk_lt_of_slot (by omega)
          (by simp only [bandC, Progress.span]; omega)).le
      · have e1 : j / 2 = r := by omega
        rw [e1]
        unfold clk
        simp only [bandC]
        omega
    · have hst' := st'.isLt
      rcases Nat.lt_trichotomy r' r with h5 | rfl | h5
      · left
        rw [h, h3]
        exact Progress.clk_lt_of_slot (by omega) (by simp only [bandC, Progress.span]; omega)
      · rcases Nat.lt_or_eq_of_le (show st'.val ≤ st.val by omega) with h6 | h6
        · left; rw [h, h3]; exact Progress.clk_lt_of_off (by simp only [bandC]; omega)
        · obtain rfl := Fin.ext h6
          exact .inr ⟨by omega, ho.trans h4.symm, by rw [h, h3]⟩
      · exfalso; omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
