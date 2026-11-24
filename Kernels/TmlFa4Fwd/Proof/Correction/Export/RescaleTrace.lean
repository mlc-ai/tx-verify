-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Stores
import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Correction.Control.Representative
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TcEv
import Kernels.TmlFa4Fwd.Proof.Correction.Loads
import Kernels.TmlFa4Fwd.Proof.Correction.RefCases
import Kernels.TmlFa4Fwd.Proof.Correction.Shapes
import Kernels.TmlFa4Fwd.Proof.Correction.Steps
import Kernels.TmlFa4Fwd.Proof.Correction.StoreValsR
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Lemmas.Flow.GlueStep
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The data of a correction lane's rescale rounds

A rescale ballot's predicate compares the scale that the stage's statistics read returned
(`corr_vote_data`), and a rescale store writes the elements of the load before it times that scale
(`corr_rescale_store`). Only the scale reads (`ScaleTo`) and the Tensor Memory loads before the
event are taken: no other statistics read precedes a rescale event (`data_to_round`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The loaded bytes are a scale word** of factor `x`: a number, or the pattern of one. -/
def ReadsAs (bs : List (Option Byte)) (x : ℝ) : Prop :=
  ∃ s : Sc, rebuild 3 bs = .ok s.val ∧ s.real = x

theorem ReadsAs.unique {bs : List (Option Byte)} {x y : ℝ} (h : ReadsAs bs x) (h' : ReadsAs bs y) :
    x = y := by
  obtain ⟨s, h1, rfl⟩ := h
  obtain ⟨s', h2, rfl⟩ := h'
  rw [h1, Except.ok.injEq] at h2
  cases s <;> cases s' <;> simp_all [Sc.val, Sc.real]

/-- **The scale reads of a lane before a position** returned scale words. -/
def ScaleTo (X : Execution) (g K : Nat) : Prop :=
  ∀ i < K, ∀ (st : Fin 2) a bs, X.get (g, i) = some ⟨(Site.rscale st).pc, .rd a bs⟩ →
    ∃ x, ReadsAs bs x

/-- The sites from stage `st`'s rescale ballot to its last store. -/
def Site.inResc (st : Fin 2) : Site → Bool
  | .rvote s | .rld s _ | .rldw s _ | .rst s _ => s == st
  | _ => false

/-- The sites from the final stage on. -/
def Site.final : Site → Bool
  | .farr0 | .fbar _ | .fsum _ | .fmax _ | .farr _ | .fw _ _ | .fld _ _ | .fwl _ _ | .fst _ _ _
  | .fence _ | .fdone _ _ | .lse _ => true
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .wend l | .barEnd l | .exit l => l
  | _ => false

private theorem final_tab :
    allSites.all (fun s => !s.final || (nexts s).all Site.final) = true := by decide +kernel

private theorem resc_tab : allSites.all (fun s => (nexts s).all fun s' => [(0 : Fin 2), 1].all
    fun st => !s'.inResc st || s.inResc st || (s == .rscale st && s' == .rvote st)) = true := by
  decide +kernel

private theorem chunk_tab : allSites.all (fun s => (nexts s).all fun s' => match s' with
    | .rldw st c => s == .rld st c
    | .rst st c => s == .rldw st c
    | _ => true) = true := by decide +kernel

/-! ### The control steps -/

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L g) (hw1 : Prologue.warpIndex L g ≤ 11)
include hp hX hFw hw hw1

/-- A step between two events of a correction lane. -/
theorem corr_step {j : Nat} {d : Control.D} {n : Cls → Nat} {e e' : Event}
    (he : X.get (g, j) = some e) (he' : X.get (g, j + 1) = some e')
    (hub : ∀ f, e.kind ≠ .ub f) (hub' : ∀ f, e'.kind ≠ .ub f)
    (hσ : Frame.stateAt (thread p L) X g j = some (some (CorrWarp.cinj p L g d n))) :
    ∃ d', Frame.stateAt (thread p L) X g (j + 1) = some (some (CorrWarp.cinj p L g d'
        (Code.bump (Proof.cls L g) n e))) ∧ Control.succ p L g d e = some (some d') ∧
      Control.Ref p L g (d, CorrWarp.rc n) ∧ Control.Ev p L g d e := by
  obtain ⟨hR, hev⟩ : Control.Ref p L g (d, CorrWarp.rc n) ∧ Control.Ev p L g d e := by
    rcases CorrWarp.open_ev hp hX hFw hw hw1 he hub with ⟨s, n0, h, -⟩ |
      ⟨d0, n0, h, h0, hR, -, hev, -⟩
    · rw [hσ] at h; cases h
    · rw [hσ] at h; cases h; exact ⟨(hR h0).1.counts, hev⟩
  have hst : Frame.stateAt (thread p L) X g (j + 1) = ((Control.succ p L g d e).map
      (Option.map fun d' => CorrWarp.cinj p L g d' (Code.bump (Proof.cls L g) n e))) := by
    rw [Frame.stateAt_succ (show (X.tr g)[j]? = some e from he), hσ]
    exact CorrWarp.next_cinj d n _
  have hsome : ∃ σ, Frame.stateAt (thread p L) X g (j + 1) = some (some σ) := by
    rcases CorrWarp.open_ev hp hX hFw hw hw1 he' hub' with ⟨s, n0, h, -⟩ | ⟨d0, n0, h, -⟩
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  obtain ⟨σ, hσ'⟩ := hsome
  rw [hst] at hσ'
  rcases hs : Control.succ p L g d e with _ | _ | d'
  · rw [hs] at hσ'; cases hσ'
  · rw [hs] at hσ'; cases hσ'
  · exact ⟨d', by rw [hst, hs]; rfl, rfl, hR, hev⟩

/-- No final-stage state precedes a rescale event. -/
private theorem not_final {i k : Nat} {di d : Control.D} {ni n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hik : i ≤ k)
    (hi : Frame.stateAt (thread p L) X g i = some (some (CorrWarp.cinj p L g di ni)))
    (hk : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g d n)))
    (hd : d.site.final = false) : di.site.final = false := by
  by_contra hf
  have key : ∀ t, i + t ≤ k → ∃ d' n', Frame.stateAt (thread p L) X g (i + t) =
      some (some (CorrWarp.cinj p L g d' n')) ∧ d'.site.final = true := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨di, ni, hi, by simpa using hf⟩
    | succ t ih =>
      intro ht
      obtain ⟨d', n', hσ, hfin⟩ := ih (by omega)
      have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = some e from he)).1
      have ev : ∀ j ≤ k, ∃ e', X.get (g, j) = some e' ∧ ∀ f, e'.kind ≠ .ub f := by
        intro j hj
        obtain ⟨e', h⟩ : ∃ e', X.get (g, j) = some e' :=
          ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
        refine ⟨e', h, ?_⟩
        rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · rw [he] at h; cases h; exact hub
        · exact Frame.noUbBefore_of_get hX he _ hj _ h
      obtain ⟨e1, h1, u1⟩ := ev (i + t) (by omega)
      obtain ⟨e2, h2, u2⟩ := ev (i + t + 1) (by omega)
      obtain ⟨d2, hσ2, hs, hR, hev⟩ := corr_step hp hX hFw hw hw1 h1 h2 u1 u2 hσ
      refine ⟨d2, _, hσ2, ?_⟩
      rcases corr_ctl_step hR hev u1 hs with ⟨hsame, -⟩ | ⟨hM, -⟩
      · rw [hsame]; exact hfin
      · have ht := List.all_eq_true.mp final_tab d'.site (mem_allSites _)
        rw [hfin] at ht
        simp only [Bool.not_true, Bool.false_or] at ht
        exact List.all_eq_true.mp ht _ hM
  obtain ⟨d', n', hσ, hfin⟩ := key (k - i) (by omega)
  rw [Nat.add_sub_cancel' hik, hk] at hσ
  cases hσ
  rw [hd] at hfin
  cases hfin

/-- **The data reads before a rescale event**, from the scale reads and the loads. -/
theorem data_to_round {K : Nat} {d : Control.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, K) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hc : Frame.stateAt (thread p L) X g K = some (some (CorrWarp.cinj p L g d n)))
    (hd : d.site.final = false) (hS : ScaleTo X g K) (hL : LoadTo X g K) :
    CorrWarp.DataTo p L X g K := by
  intro i hi di ni ei hei hs hR hdat
  have hci := control_of_data hp hs
  have hfin : di.site.final = false :=
    not_final hp hX hFw hw hw1 he hub hi.le (di := Control.erase di) hci hc hd
  have hpc : ei.pc = di.site.pc := Frame.event_pc (fun g hg => threadD_sound hp hg) hX hei hs
  obtain ⟨pc, kd⟩ := ei
  obtain ⟨s, v, k⟩ := di
  cases s
  case rscale st =>
    intro a bs hk
    simp only at hk hpc
    subst hk hpc
    obtain ⟨_, s, hs, -⟩ := hS i hi st a bs hei
    exact ⟨s, hs⟩
  case rld st c =>
    intro a vals sh hk
    simp only at hk
    subst hk
    have hl : X.TLd (g, i) a vals sh := ⟨pc, hei⟩
    obtain ⟨dc, nc, r, ℓ, hσ, -, rfl, st', hst⟩ := corr_ld_state hp hX hFw hw hw1 hl
    refine flN_some ?_ (hL i hi a vals hl)
    rw [hci] at hσ
    have hσ' : (Control.erase ⟨.rld st c, v, k⟩) = dc := by
      have h := congrArg (fun z : Option (Option (thread p L g).D) => z.bind fun y => y) hσ
      simp only [Option.bind_some, Option.some.injEq] at h
      cases h
      rfl
    rcases hst with ⟨c', h, -, hn⟩ | ⟨c', h, -, hn⟩
    · exact hn
    · rw [← hσ'] at h; cases h
  all_goals first
    | (cases hfin; done)
    | cases hdat

/-! ### The data states -/

/-- The state has a scale read by the stage's last statistics read, and at a store the elements of
the load before it. -/
structure Inv (L : Launch) (X : Execution) (g k : Nat) (d : D) : Prop where
  scale : ∀ st : Fin 2, d.site.inResc st = true → ∃ i a bs, i < k ∧
    X.get (g, i) = some ⟨(Site.rscale st).pc, .rd a bs⟩ ∧ ReadsAs bs (sOf d.v st).real ∧
    Tm.pArr L X g st i = Tm.pArr L X g st k
  load : ∀ (st : Fin 2) c, d.site = .rldw st c ∨ d.site = .rst st c → ∃ i a vals, i < k ∧
    X.TLd (g, i) a vals .s32x32b ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧
    vals.length = 16 ∧ flN 16 vals = some d.v.xs ∧ Tm.pArr L X g st i = Tm.pArr L X g st k

omit hp hX hFw hw hw1 in
/-- An event with no arrival on the stage's P-full object keeps its arrivals. -/
theorem pArr_next {k : Nat} {e : Event} (he : X.get (g, k) = some e) {st : Nat}
    (h : arrivesOn (Tm.pFull L (g / L.block) st) e = false) :
    Tm.pArr L X g st (k + 1) = Tm.pArr L X g st k := by
  unfold Tm.pArr arrivals
  rw [List.take_add_one, show (X.tr g)[k]? = some e from he, Option.toList_some,
    List.countP_append, List.countP_singleton, h]
  simp

omit hp hX hFw hw hw1 in
private theorem no_arr {d : Control.D} {e : Event} {st : Fin 2} (hev : Control.Ev p L g d e)
    (hub : ∀ f, e.kind ≠ .ub f) (hs : d.site = .rscale st ∨ d.site.inResc st = true) (m : Loc) :
    arrivesOn m e = false := by
  obtain ⟨s, v, k⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hub
  cases s <;> simp [Site.inResc] at hs
  all_goals simp only [Control.Ev, Control.D.scheduler, Ev, rdOrUb] at hev
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals first
    | exact absurd rfl (hub _)
    | rfl

omit hp hX hFw hw hw1 in
/-- The scale is kept inside a rescale stage. -/
private theorem scale_keep {st : Fin 2} {d d' : D} {e : Event} (h : d.site.inResc st = true)
    (hs : succ p L g d e = some (some d')) : sOf d'.v st = sOf d.v st := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp [Site.inResc] at h
  all_goals subst h
  case rvote s =>
    simp only [succ] at hs
    split at hs
    · cases hs
      simp only [afterVote, D.ite]
      fin_cases s <;> split <;> rfl
    · cases hs
  case rld s c =>
    simp only [succ] at hs
    split at hs
    · split at hs
      · split at hs <;> cases hs
        fin_cases s <;> rfl
      · cases hs
    · cases hs
  case rldw s c =>
    simp only [succ] at hs
    split at hs <;> cases hs
    rfl
  case rst s c =>
    simp only [succ] at hs
    split_ifs at hs <;> (cases hs; rfl)

omit hp hX hFw hw hw1 in
private theorem inv_step {k : Nat} {d d' : D} {e : Event} (he : X.get (g, k) = some e)
    (hpc : e.pc = d.site.pc) (hub : ∀ f, e.kind ≠ .ub f)
    (hev : Control.Ev p L g (Control.erase d) e) (hs : succ p L g d e = some (some d'))
    (hld : ∀ a vals sh, e.kind = .tc (.ld a vals sh) → ∀ st c, d.site = .rld st c →
      sh = .s32x32b ∧ a % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16)
    (hI : Inv L X g k d) : Inv L X g (k + 1) d' := by
  obtain ⟨p1, p2⟩ : (∀ st, d'.site.inResc st = true → d.site.inResc st = true ∨
      (d.site = .rscale st ∧ d'.site = .rvote st)) ∧
      ∀ st c, (d'.site = .rldw st c → d.site = .rld st c) ∧
        (d'.site = .rst st c → d.site = .rldw st c) := by
    rcases succ_cases hs with ⟨rfl, _, _, _, _, hk⟩ | ⟨hf, -, rfl⟩ | hM
    · refine ⟨fun st h => .inl h, fun st c => ⟨fun h => ?_, fun h => ?_⟩⟩ <;>
      · exfalso
        obtain ⟨s, v, j⟩ := d'
        change s = _ at h
        subst h
        simp only [Control.Ev, Control.erase, Control.D.scheduler, Ev] at hev
        rw [hk] at hev
        shape_destruct hev
        all_goals cases ‹Kind.wait _ _ _ _ _ = _›
    · refine ⟨fun st h => ?_, fun st c => ⟨fun h => ?_, fun h => ?_⟩⟩
      · revert hf h; cases d.site <;> simp [Site.isFst, Site.inResc]
      all_goals simp only at h; rw [h] at hf; cases hf
    · refine ⟨fun st h => ?_, fun st c => ⟨fun h => ?_, fun h => ?_⟩⟩
      · have h1 := List.all_eq_true.mp (List.all_eq_true.mp resc_tab _ (mem_allSites d.site)) _ hM.1
        have h2 := List.all_eq_true.mp h1 st (by fin_cases st <;> simp)
        simpa [h] using h2
      all_goals
        have h1 := List.all_eq_true.mp (List.all_eq_true.mp chunk_tab _ (mem_allSites d.site)) _
          hM.1
        rw [h] at h1
        simpa using h1
  constructor
  · intro st h
    rcases p1 st h with h1 | ⟨h1, h2⟩
    · obtain ⟨i, a, bs, hi, hr, hb, hc⟩ := hI.scale st h1
      exact ⟨i, a, bs, by omega, hr, by rw [scale_keep h1 hs]; exact hb, hc.trans
        (pArr_next he (no_arr hev hub (st := st) (.inr h1) _)).symm⟩
    · have hno := no_arr hev hub (st := st) (.inl h1) (Tm.pFull L (g / L.block) st)
      obtain ⟨s, v, j⟩ := d
      obtain ⟨pc, kd⟩ := e
      change s = _ at h1
      subst h1
      simp only [succ] at hs
      split at hs
      · rename_i _ a bs
        simp only at hpc
        subst hpc
        split at hs
        · rename_i w hw
          obtain ⟨y, hy, rfl⟩ := scale32_some hs
          refine ⟨k, a, bs, by omega, he, ⟨y, by rw [hw, hy], ?_⟩, (pArr_next he hno).symm⟩
          fin_cases st <;> rfl
        · cases hs
      · cases hs
  · rintro st c (h | h)
    · have h1 := (p2 st c).1 h
      have hno := no_arr hev hub (st := st) (.inr (by
        show (Control.erase d).site.inResc st = true
        rw [show (Control.erase d).site = _ from h1]; simp [Site.inResc]))
        (Tm.pFull L (g / L.block) st)
      obtain ⟨s, v, j⟩ := d
      obtain ⟨pc, kd⟩ := e
      change s = _ at h1
      subst h1
      simp only [succ] at hs
      split at hs
      · split at hs
        · rename_i _ a vals sh
          split at hs
          · rename_i xs hx
            cases hs
            obtain ⟨rfl, h3, h4⟩ := hld a vals sh rfl st c rfl
            exact ⟨k, a, vals, by omega, ⟨pc, he⟩, h3, h4, hx, (pArr_next he hno).symm⟩
          · cases hs
        · cases hs
      · cases hs
    · have h1 := (p2 st c).2 h
      have hno := no_arr hev hub (st := st) (.inr (by
        show (Control.erase d).site.inResc st = true
        rw [show (Control.erase d).site = _ from h1]; simp [Site.inResc]))
        (Tm.pFull L (g / L.block) st)
      obtain ⟨i, a, vals, hi, hl, h3, h4, hx, hc⟩ := hI.load st c (.inl h1)
      have hv : d'.v = d.v := by
        obtain ⟨s, v, j⟩ := d
        change s = _ at h1
        subst h1
        simp only [succ] at hs
        split at hs <;> cases hs
        rfl
      exact ⟨i, a, vals, by omega, hl, h3, h4, by rw [hv]; exact hx,
        hc.trans (pArr_next he hno).symm⟩

/-- **The data state of a rescale event** over its control state, with its invariant. -/
theorem corr_resc_alive {k : Nat} {dc : Control.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f)
    (hc : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g dc n)))
    (hf : dc.site.final = false) (hS : ScaleTo X g k) (hL : LoadTo X g k) :
    ∃ d : D, Frame.stateAt (threadD p L) X g k = some (some (.inr ⟨.correction, d⟩, n)) ∧
      Control.erase d = dc ∧ Inv L X g k d := by
  have hD := data_to_round hp hX hFw hw hw1 he hub hc hf hS hL
  have hlen := (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = some e from he)).1
  have hg := Frame.lt_of_get hX he
  have key : ∀ j ≤ k, ∃ σ, Frame.stateAt (threadD p L) X g j = some (some σ) ∧
      ∀ d n, σ = (.inr ⟨.correction, d⟩, n) → Inv L X g j d := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨_, Frame.stateAt_zero, fun d n h => ?_⟩
      cases h
    | succ j ih =>
      intro hj
      obtain ⟨⟨σ0, n0⟩, hs0, hI⟩ := ih (by omega)
      obtain ⟨σ, hs, -⟩ := CorrWarp.alive hp hX ⟨hw, hw1⟩ hg rfl hD (j + 1) hj (by omega)
      refine ⟨σ, hs, ?_⟩
      rintro d' n' rfl
      obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, j) = some e0 :=
        ⟨_, List.getElem?_eq_getElem (show j < (X.tr g).length by omega)⟩
      have hu0 := Frame.noUbBefore_of_get hX he _ hj _ he0
      rw [Frame.stateAt_succ (show (X.tr g)[j]? = some e0 from he0), hs0] at hs
      obtain ⟨hn, -⟩ := Code.counted_next_some (C := gluedD p L g) hs
      cases σ0 with
      | inl s =>
        obtain ⟨s', -, henter⟩ := Code.glue_inl_some hn
        unfold Code.enter at henter
        split at henter <;> cases henter
        exact ⟨fun _ h => (by cases h), fun _ _ h => (by
          rcases h with h | h <;> cases h)⟩
      | inr a =>
        obtain ⟨i, d⟩ := a
        obtain ⟨d2, hst, hd2⟩ := Code.glue_inr_some hn
        cases hd2
        have hci := control_of_data hp hs0
        have hev : Control.Ev p L g (Control.erase d) e0 := by
          rcases CorrWarp.open_ev hp hX hFw hw hw1 he0 hu0 with ⟨s, n1, h, -⟩ |
            ⟨d1, n1, h, -, -, -, hev, -⟩
          · rw [hci] at h; cases h
          · rw [hci] at h
            cases h
            exact hev
        refine inv_step he0 (Frame.event_pc (fun g hg => threadD_sound hp hg) hX he0 hs0) hu0 hev
          hst ?_ (hI d n0 rfl)
        intro a vals sh hk st c hsite
        obtain ⟨pc0, kd0⟩ := e0
        simp only at hk
        subst hk
        obtain ⟨dc, nc, r, ℓ, hσ, -, rfl, st', hst'⟩ := corr_ld_state hp hX hFw hw hw1
          (show X.TLd (g, j) a vals sh from ⟨pc0, he0⟩)
        rw [hci] at hσ
        have hσ' : Control.erase d = dc := by cases hσ; rfl
        have hsite' : dc.site = .rld st c := by rw [← hσ']; exact hsite
        rcases hst' with ⟨c', h, h1, h2⟩ | ⟨c', h, -⟩
        · rw [hsite'] at h
          cases h
          exact ⟨rfl, h1, h2⟩
        · rw [hsite'] at h; cases h
  obtain ⟨σ, hs, hI⟩ := key k le_rfl
  obtain ⟨d, rfl, hd⟩ := data_of_control hp hs hc
  exact ⟨d, hs, hd, hI d n rfl⟩

/-- **A rescale ballot's predicate** compares the scale the stage's last statistics read
returned. -/
theorem corr_vote_data {k pc : Nat} {m' : Nat} {a : Bool} {b : BitVec 32} {st : Fin 2}
    {dc : Control.D} {n : Cls → Nat} (he : X.get (g, k) = some ⟨pc, .vote m' a b⟩)
    (hc : Frame.stateAt (thread p L) X g k = some (some (CorrWarp.cinj p L g dc n)))
    (hs : dc.site = .rvote st) (hS : ScaleTo X g k) (hL : LoadTo X g k) :
    ∃ i ad bs x, i < k ∧ X.get (g, i) = some ⟨(Site.rscale st).pc, .rd ad bs⟩ ∧
      ReadsAs bs x ∧ Tm.pArr L X g st i = Tm.pArr L X g st k ∧
      a = Assumption.erealCompare .lt (x : EReal) (1 : ℝ) := by
  obtain ⟨d, hσ, rfl, hI⟩ := corr_resc_alive hp hX hFw hw hw1 he (by intro f h; cases h) hc
    (by rw [hs]; rfl) hS hL
  obtain ⟨o, hf⟩ := (Frame.trace (fun _ hg => threadD_sound hp hg) hX
    (Frame.lt_of_get hX he)).fired_at he hσ
  have hev := (Code.Shape.fired (shape hp) (stepAt hp (Frame.lt_of_get hX he))
    (show (code p L g).toMachine.Fired (some d) _ o from hf)).1
  have hs' : d.site = .rvote st := hs
  obtain ⟨i, ad, bs, hi, hr, hb, hp'⟩ := hI.scale st (by rw [hs']; simp [Site.inResc])
  refine ⟨i, ad, bs, _, hi, hr, hb, hp', ?_⟩
  simp only [Ev, hs'] at hev
  obtain ⟨b', h⟩ := hev
  cases h
  rfl

/-- **A rescale store** writes the elements of a load of its credit and cells times the scale that
the stage's last statistics read returned. -/
theorem corr_rescale_store {k a : Nat} {vals : List Value} {sh : TcShape}
    (ht : X.TSt (g, k) a vals sh) (hS : ScaleTo X g k) (hL : LoadTo X g k) :
    ∃ (st : Fin 2) (c : Fin 8) (i : Nat) (ad : Acc) (bs : List (Option Byte)) (x : ℝ),
      a % 65536 = 256 + 128 * st.val + 16 * c.val ∧ vals.length = 16 ∧ i < k ∧
      X.get (g, i) = some ⟨(Site.rscale st).pc, .rd ad bs⟩ ∧ ReadsAs bs x ∧
      Tm.pArr L X g st i = Tm.pArr L X g st k ∧
      ∃ k' a' vals', X.TLd (g, k') a' vals' .s32x32b ∧ a' % 65536 = a % 65536 ∧
        vals'.length = 16 ∧ Tm.pArr L X g st k' = Tm.pArr L X g st k ∧
        ∀ j < 16, ∃ y, vals'[j]? = some (fv y) ∧ vals[j]? = some (fv (y * x)) := by
  obtain ⟨dc, n, -, -, hc, -, -, st, c, hsite, h1, h2⟩ := corr_st_state hp hX hFw hw hw1 ht
  obtain ⟨pc, he⟩ := ht
  obtain ⟨d, hσ, rfl, hI⟩ := corr_resc_alive hp hX hFw hw hw1 he (by intro f h; cases h) hc
    (by rw [hsite]; rfl) hS hL
  obtain ⟨t, ins, o, hat, -, hcd, hf⟩ :=
    Frame.fired_site (fun g hg => threadD_sound hp hg) hX he hσ
  have hs' : d.site = .rst st c := hsite
  obtain ⟨i, ad, bs, hi, hr, hb, hp'⟩ := hI.scale st (by rw [hs']; simp [Site.inResc])
  obtain ⟨k', a', vals', -, hl, g1, g2, hx, g3⟩ := hI.load st c (.inr hs')
  obtain ⟨s, v, j⟩ := d
  change s = _ at hs'
  subst hs'
  have hv := rst_val hat hcd hf rfl
  refine ⟨st, c, i, ad, bs, _, h1, h2, hi, hr, hb, hp', k', a', vals', hl, by omega, g2, g3,
    fun j hj => ⟨v.xs j, ?_, ?_⟩⟩
  · have := flN_get hx hj (.pred false)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    rw [List.getElem?_eq_getElem (by omega), this]
  · rw [hv]
    simp [hj]

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
