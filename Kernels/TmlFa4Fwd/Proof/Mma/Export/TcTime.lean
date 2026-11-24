-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollState
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemCount
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Mma.Open
import Kernels.TmlFa4Fwd.Proof.Mma.Export.SafePre
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Progress.Order
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites

@[expose] public section

/-! # The MMA warp's Tensor Memory resource events in the time table

`mma_end_time`: a role state of the MMA warp before its end is before every end, and before the end
of a lane of a CTA with no tile (`endT p false 0`) when the CTA picked none. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase doneBase passTime endT)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The end's sites. -/
def Site.isEnd : Site → Option Bool
  | .relinq l | .bar2 l | .dealloc l | .exit l => some l
  | _ => none

private theorem site_lt (s : Site) (h : s.pipe = true) : s.ord < 86 := by
  cases s <;> simp [Site.pipe] at h
  case wt k => revert k; decide
  case sh k => revert k; decide
  case eq k => revert k; decide
  case ep k => revert k; decide
  case ce k => revert k; decide
  case cm k => revert k; decide
  case qk b j => revert b j; decide
  case pv b j => revert b j; decide
  case mw b l => revert b l; decide

/-- Whether a thread state of the MMA warp is at a resource event. -/
def tcAt (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Bool :=
  match σ with
  | (.inr ⟨.mma, .inl .alloc⟩, _) => true
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => isRD d.site
  | _ => false

/-- **A resource event leads to a later state.** -/
theorem tc_next {σ : (thread p L g).D} (h : tcAt p L g σ = true) (e : Event) :
    ∃ σ', (thread p L g).next σ e = some (some σ') ∧
      Progress.time p L g σ < Progress.time p L g σ' := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try cases h
  rcases d with s | ⟨u, d⟩
  · cases s <;> try cases h
    have hnx : (thread p L g).next (.inr ⟨.mma, .inl .alloc⟩, n) e =
        some (some (.inr ⟨.mma, Code.enter (S p L g (ent p L)) (fun _ => code p L g (ent p L))
          Start.exit (if laneOf L g = 0 then .wr else .enter)⟩,
          Code.bump (Proof.cls L g) n e)) := rfl
    refine ⟨_, hnx, ?_⟩
    by_cases h0 : laneOf L g = 0
    · simp only [h0, ite_true]
      show scanBase + 1 < scanBase + 2
      omega
    · simp only [h0, ite_false]
      show scanBase + 1 < scanBase + 3
      omega
  · have hrd : isRD d.site = true := h
    obtain ⟨site, v⟩ := d
    cases site <;> simp only [isRD, Bool.false_eq_true] at hrd
    case relinq l =>
      refine ⟨minj p L g ⟨.bar2 l, v⟩ (Code.bump (Proof.cls L g) n e),
        (next_minj _ _ _).trans rfl, ?_⟩
      show endT p l 0 < endT p l 4
      unfold endT; split <;> omega
    case dealloc l =>
      refine ⟨minj p L g ⟨.exit l, v⟩ (Code.bump (Proof.cls L g) n e),
        (next_minj _ _ _).trans rfl, ?_⟩
      show endT p l 6 < endT p l 8
      unfold endT; split <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
include hp hX hub hg hw

/-- **A state of the MMA warp before its end** is early. -/
theorem mma_end_time {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ))
    (hne : ∀ d n, σ = minj p L g d n → d.site.isEnd = none) :
    Progress.time p L g σ < doneBase p ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) → Progress.time p L g σ < endT p false 0) := by
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  have hend : primeBase p + 1024 ≤ endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold endBase Progress.tailBase; omega
  have hdone : doneBase p = endBase p + 4 * Progress.cmax p + 8 := rfl
  have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
  have he0 : endT p false 0 = primeBase p + 1000 := by simp [endT]
  -- an early state
  have early : ∀ {t : Nat}, t < primeBase p + 1000 → t < doneBase p ∧
      ((¬ ∃ R bal, Epilogue.Picked p L g R bal) → t < endT p false 0) := fun h =>
    ⟨by omega, fun _ => by omega⟩
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, -⟩ := hR
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      simp only [StartAt, he] at hS
    have := Progress.startTime_lt hx
    refine early ?_
    simp only [Progress.time]
    omega
  · rcases d with s | ⟨u, d⟩
    · refine early ?_
      simp only [Progress.time, Progress.roleTime, Progress.Mm.startT]
      split <;> omega
    · have hub0 : n .ub = 0 := by
        by_contra h
        obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
        cases kind <;> simp [Proof.cls] at hk
        exact hub ⟨(g, j), pc, _, hf⟩
      obtain ⟨⟨r, w, hQ, -⟩, hF⟩ := hR hub0
      have hns := hne d n rfl
      show Progress.Mm.time p d n < _ ∧ (_ → Progress.Mm.time p d n < _)
      cases he : d.site.early with
      | true =>
        refine early ?_
        have hF' := hF
        simp only [MFits, he, ite_true] at hF'
        obtain ⟨h3, hv, hps⟩ := hF'
        cases hs : d.site <;> rw [hs] at he <;> simp only [Site.early, Bool.false_eq_true] at he <;>
          simp only [Progress.Mm.time, hs, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true,
            ite_false, ite_true, reduceCtorEq, Site.late, Progress.Mm.scans, Site.toE,
            Progress.Out.ballots, Progress.Mm.coll, Site.scan, Bool.false_and, passTime] <;> omega
      | false =>
      obtain ⟨h1, h2, -, h4, h5⟩ := mfits_main he hF
      cases hpipe : d.site.pipe with
      | true =>
        obtain ⟨R0, bal, hC, hB⟩ := bs_ref (pmid_of hpipe) hF
        have hR' : MmaRounds p L g _ := ⟨R0, bal, hC.1, rfl⟩
        have hbm := mma_rounds_bmax hp hg hR'
        refine ⟨?_, fun hno => (hno ⟨R0, bal, hC.1⟩).elim⟩
        have hB' : Bs p L g d.v = Bs p L g (mmaRef p L g R0 bal) := hB
        have h86 := (site_lt d.site hpipe)
        have hslot : (if d.site.ord < 20 then 0 else Progress.Mm.round d.site.ord d.v + 1) ≤
            Progress.bmax p + 1 := by
          split
          · omega
          · rename_i h20
            rw [Progress.Mm.round_eq (by omega) h86 hQ.ps]
            by_cases h60 : d.site.ord < 60
            · have := (hQ.loop ⟨Nat.le_of_not_lt h20, h60⟩).1
              rw [hB'] at this
              change (r : Int) + 1 < Bs p L g (mmaRef p L g R0 bal) at this
              generalize Bs p L g (mmaRef p L g R0 bal) = B at this hbm
              omega
            · have := hQ.tail ⟨Nat.le_of_not_lt h60, Nat.lt_trans h86 (by decide)⟩
              rw [hB'] at this
              change (r : Int) + 1 = Bs p L g (mmaRef p L g R0 bal) ∨
                (r = 0 ∧ Bs p L g (mmaRef p L g R0 bal) < 2) at this
              generalize Bs p L g (mmaRef p L g R0 bal) = B at this hbm
              omega
        simp only [Progress.Mm.time, hpipe, ite_true, Progress.Mm.pipeT]
        exact Progress.drain_order p hslot (by unfold Progress.span; omega)
      | false =>
        have hnb : d.site ≠ .bar1 ∧ Progress.Mm.endOff d.site = none := by
          constructor
          · rintro h; rw [h] at he; cases he
          · revert hns
            cases d.site <;> simp [Site.isEnd, Progress.Mm.endOff]
        have ht : Progress.Mm.time p d n = passTime (if d.site.late then endBase p else scanBase)
            (n .shfl - d.v.ps + Progress.Out.ballots d.site.toE) (Progress.Mm.coll d.site) := by
          simp only [Progress.Mm.time, hpipe, Bool.false_eq_true, ite_false, hnb.2, hnb.1,
            Progress.Mm.scans]
        have hb : Progress.Out.ballots d.site.toE ≤ 1 := by
          unfold Progress.Out.ballots; split <;> omega
        have hpt : ∀ b c co, passTime b c co ≤ b + 2 * c := fun b c co => by
          unfold passTime; split <;> omega
        have hle := hpt (if d.site.late then endBase p else scanBase)
          (n .shfl - d.v.ps + Progress.Out.ballots d.site.toE) (Progress.Mm.coll d.site)
        rw [← ht] at hle
        have hall := Epilogue.fits_coll_le_all hp h2
        cases hl : d.site.late with
        | true =>
          rw [hl] at hle
          simp only [ite_true] at hle
          obtain ⟨R, bal, hP, -⟩ := h4 hl
          exact ⟨by omega, fun hno => (hno ⟨R, bal, hP⟩).elim⟩
        | false =>
          rw [hl] at hle
          simp only [Bool.false_eq_true, ite_false] at hle
          have hlE : (toE d).site.late = false := by
            show d.site.epi.late = false
            revert hl hns
            cases d.site <;> simp [Site.late, Site.epi, Epilogue.Site.late, Site.isEnd]
          have := Epilogue.fits_coll_le hp h2 hlE
          exact early (by omega)

/-- **The end of a lane of the MMA warp** is the second pass's exactly when its CTA picked a
tile. -/
theorem mma_end_picked {d : D} {n : Cls → Nat} {l : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hl : d.site.isEnd = some l) : l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [Proof.cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨-, hF⟩ := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ hub0
  have hs : d.site.early = false ∧ d.site.epi = .exit l ∧ d.site.late = l := by
    revert hl
    cases d.site <;> simp only [Site.isEnd, Option.some.injEq, reduceCtorEq, false_implies]
    all_goals rintro rfl; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨-, h2, -, h4, -⟩ := mfits_main hs.1 hF
  cases l with
  | true =>
    obtain ⟨R, bal, hP, -⟩ := h4 hs.2.2
    exact ⟨fun _ => ⟨R, bal, hP⟩, fun _ => rfl⟩
  | false =>
    constructor
    · intro h; cases h
    · exact fun h => (noPicked_of_exit h2 hs.2.1 h).elim

/-- The time of a Tensor Memory resource event: the allocation request, the hand-back, the
deallocation, at the end `l`. -/
def tcT (p : Params) (l : Bool) (c : Nat) : Nat :=
  if c = 0 then scanBase + 1 else if c = 1 then endT p l 0 else endT p l 6

/-- **A state with at most `c` resource events** is no later than resource event `c`, and earlier
unless it is at one. -/
theorem mma_tc_le {σ : (thread p L g).D} {l : Bool} {c : Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) (hc : tcnt p L g σ ≤ c) (hc2 : c ≤ 2)
    (hl : 1 ≤ c → (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal)) :
    Progress.time p L g σ ≤ tcT p l c ∧
      (tcAt p L g σ = false → Progress.time p L g σ + 1 ≤ tcT p l c) := by
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  have hT1 : endT p l 0 ≤ endT p l 6 := by unfold endT; split <;> omega
  have hdone : doneBase p ≤ endT p true 0 := by simp [endT]
  -- a state before the end
  have mid : 1 ≤ c → (∀ d n, σ = minj p L g d n → d.site.isEnd = none) →
      Progress.time p L g σ + 1 ≤ tcT p l c := by
    intro h1 hne
    obtain ⟨t1, t2⟩ := mma_end_time hp hX hub hg hw hσ hne
    have : Progress.time p L g σ < endT p l 0 := by
      cases l with
      | true => omega
      | false => exact t2 fun h => by have := (hl h1).mpr h; cases this
    unfold tcT
    split_ifs <;> omega
  by_cases hend : ∃ d n, σ = minj p L g d n ∧ d.site.isEnd ≠ none
  · obtain ⟨d, n, rfl, hd⟩ := hend
    obtain ⟨l', hl'⟩ := Option.ne_none_iff_exists'.mp hd
    have hts : 1 ≤ tsite d.site := by cases d.site <;> simp [tsite]
    have hc' : tsite d.site ≤ c := hc
    have hll : l' = l := by
      have h1 := mma_end_picked hp hX hub hg hw hσ hl'
      have h2 := hl (by omega)
      have := h1.trans h2.symm
      cases l <;> cases l' <;> simp_all
    subst hll
    have e0 : endT p l' 0 + 4 = endT p l' 4 ∧ endT p l' 4 + 2 = endT p l' 6 := by
      unfold endT; split <;> omega
    have ht : Progress.time p L g (minj p L g d n) = Progress.Mm.time p d n := rfl
    rw [ht]
    cases hs : d.site <;> rw [hs] at hl' hc' <;>
      simp only [Site.isEnd, Option.some.injEq, reduceCtorEq] at hl' <;>
      simp only [tsite] at hc' <;> subst hl' <;>
      simp only [Progress.Mm.time, hs, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true, ite_false,
        tcT, tcAt, isRD]
    all_goals
      refine ⟨?_, ?_⟩ <;> (try intro hx) <;> (try (cases hx; done)) <;> split_ifs <;> omega
  · push Not at hend
    by_cases h1 : 1 ≤ c
    · have := mid h1 hend
      exact ⟨by omega, fun _ => this⟩
    · obtain rfl : c = 0 := by omega
      simp only [tcT, ite_true]
      obtain ⟨σ, n⟩ := σ
      rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
      · obtain ⟨hS, -⟩ := hR
        have hx : ∀ r, s.site ≠ .enter r := by
          intro r he
          simp only [StartAt, he] at hS
        have := Progress.startTime_lt hx
        simp only [Progress.time]
        omega
      · rcases d with s | ⟨u, d⟩
        · cases s with
          | set => simp only [Progress.time, Progress.roleTime, Progress.Mm.startT]; omega
          | alloc =>
            simp only [Progress.time, Progress.roleTime, Progress.Mm.startT, tcAt]
            exact ⟨le_rfl, fun h => by cases h⟩
          | wr => simp [tcnt] at hc
          | enter => simp [tcnt] at hc
        · exfalso
          have h1 : tsite d.site ≤ 0 := hc
          revert h1
          cases d.site <;> simp [tsite]


omit hub hg in
/-- **A warp-collective `tcgen05` event of the MMA warp** is a resource event, at a resource
site. -/
theorem mma_tc_ev (hFw : Follow p L X) {e : Event} (he : X.get (g, k) = some e)
    (hne : ∀ f, e.kind ≠ .ub f) {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    isTcColl e = Tmem.Pair.isTmemOp e ∧ (isTcColl e = true → tcAt p L g σ = true) := by
  rcases Mma.open_ev hp hX hFw hw he hne with ⟨s, n, hσ1, -, -, hi, hev⟩ |
    ⟨s, n, hσ1, -, hinv, hev⟩ | ⟨d, n, hσ1, -, -, -, hev⟩
  · have hq := start_nores hev hi.2
    have : isTcColl e = false := by
      obtain ⟨pc, kind⟩ := e
      obtain ⟨site, x1, x2, x3⟩ := s
      have hx : exit L g _ = none := hi.2
      cases site with
      | sh j =>
        fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
          subst hk <;> rfl
      | elect j =>
        simp only [Startup.Ev] at hev
        rcases hev with ⟨_, _, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> rfl
      | init q =>
        simp only [Startup.Ev] at hev
        rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> rfl
      | fence => simp only [Startup.Ev] at hev; subst hev; rfl
      | bar => simp only [Startup.Ev] at hev; subst hev; rfl
      | enter r => simp [exit] at hx
    rw [this, hq]
    exact ⟨rfl, fun h => by cases h⟩
  · rw [hσ] at hσ1
    cases hσ1
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
      strict_fired_site hp hX he hσ rfl
    have hk3 := Mma.pre_kind hp hat hc hf
    obtain ⟨pc, kind⟩ := e
    cases s with
    | set =>
      obtain ⟨_, hk⟩ := hk3.1 rfl
      simp only at hk
      subst hk
      exact ⟨rfl, fun h => by cases h⟩
    | alloc =>
      have hk := hk3.2.1 rfl
      simp only at hk
      subst hk
      exact ⟨rfl, fun _ => rfl⟩
    | wr =>
      obtain ⟨_, hk⟩ := hk3.2.2 rfl
      simp only at hk
      subst hk
      exact ⟨rfl, fun h => by cases h⟩
    | enter => exact absurd hinv.2 (by simp [Mma.Start.exit])
  · rw [hσ] at hσ1
    cases hσ1
    have hk := mma_ev_kind hev hne
    obtain ⟨pc, kind⟩ := e
    generalize d.site.wcoll = wc at hk
    cases hk with
    | tc kd =>
      show _ ∧ (_ → isRD d.site = true)
      obtain ⟨site, v⟩ := d
      cases site <;> simp only [Mma.Ev] at hev
      case relinq | dealloc =>
        rcases hev with ⟨_, _, h⟩ | ⟨f, h⟩
        · cases h; exact ⟨rfl, fun _ => rfl⟩
        · cases h
      case qk | pv =>
        rcases hev with ⟨_, _, _, _, h⟩ | ⟨f, h⟩
        · cases h; exact ⟨rfl, fun h => by cases h⟩
        · cases h
      case cm =>
        rcases hev with ⟨_, h, -⟩ | ⟨f, h⟩
        · cases h; exact ⟨rfl, fun h => by cases h⟩
        · cases h
      all_goals (exfalso; simp [Epilogue.Ev, Mma.Site.toE] at hev)
    | _ => exact ⟨rfl, fun h => by cases h⟩

/-- **The warp-collective `tcgen05` events before a state** of the MMA warp. -/
theorem mma_tc_count (hFw : Follow p L X) {σ : (thread p L g).D} (hk : k ≤ (X.tr g).length)
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ((X.tr g).take k).countP isTcColl = tcnt p L g σ := by
  have hne : ∀ j e f, X.get (g, j) = some e → e.kind ≠ .ub f := fun j e f he hf =>
    hub ⟨(g, j), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  rw [← mma_count_at hp hX hg hw k hk (fun j _ e f he => hne j e f he) σ hσ]
  refine List.countP_congr fun e hmem => ?_
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hmem
  have hjl : j < (X.tr g).length := by rw [List.length_take] at hj; omega
  have he : X.get (g, j) = some e := by
    show (X.tr g)[j]? = _
    rw [← hje, List.getElem_take]
    exact List.getElem?_eq_getElem hjl
  obtain ⟨σ', hσ', -⟩ := good_state hp hX he
    (fun pc f hf => hub ⟨(g, j), pc, f, by rw [he, hf]⟩)
    (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw j)
  rw [(mma_tc_ev hp hX hw hFw he (fun f => hne j e f he) hσ').1]

/-- **A lane of the MMA warp with fewer resource events is no later than a lane at one.** -/
theorem mma_tcLag (hFw : Follow p L X) {h j c : Nat} (hs : SameWarp L g h)
    {d : (thread p L g).D} (hK : X.TcK (g, j) c)
    (hσ : Frame.stateAt (thread p L) X g j = some (some d))
    (hle : (X.tr h).countP isTcColl ≤ c) :
    Sched.threadTime (Progress.timed p L) X h ≤ Progress.time p L g d := by
  have hh := hs.1.2.1
  have hwh : Prologue.warpIndex L h = 12 := by rw [← hw]; exact hs.2.symm
  have hcta : g / L.block = h / L.block := hs.1.2.2
  obtain ⟨⟨e, he, hcl⟩, hcnt⟩ := hK
  have hne : ∀ f, e.kind ≠ .ub f := fun f hf => by
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    cases hcl
  have hat := (mma_tc_ev hp hX hw hFw he hne hσ).2 hcl
  have hc : tcnt p L g d = c := by
    rw [← mma_tc_count hp hX hub hg hw hFw
      (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = some e from he)).1.le hσ]
    exact hcnt
  -- the event's time and end
  obtain ⟨l, hT, hl, hc2⟩ : ∃ l, Progress.time p L g d = tcT p l c ∧
      (1 ≤ c → (l = true ↔ ∃ R bal, Epilogue.Picked p L g R bal)) ∧ c ≤ 2 := by
    obtain ⟨σ, n⟩ := d
    rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try (cases hat)
    rcases d with s | ⟨u, d⟩
    · cases s <;> try (cases hat; done)
      have hc0 : c = 0 := hc.symm
      exact ⟨true, by subst hc0; rfl, fun h => by omega, by omega⟩
    · have hrd : isRD d.site = true := hat
      have hcs : tsite d.site = c := hc
      cases hsd : d.site <;> rw [hsd] at hrd hcs <;> simp only [isRD, Bool.false_eq_true] at hrd
      case relinq l =>
        have hc1 : c = 1 := hcs.symm
        refine ⟨l, ?_, fun _ => mma_end_picked hp hX hub hg hw hσ (by rw [hsd]; rfl), by omega⟩
        subst hc1
        show Progress.Mm.time p d n = _
        simp only [Progress.Mm.time, hsd, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true,
          ite_false, tcT, one_ne_zero, ite_true]
      case dealloc l =>
        have hc1 : c = 2 := hcs.symm
        refine ⟨l, ?_, fun _ => mma_end_picked hp hX hub hg hw hσ (by rw [hsd]; rfl), by omega⟩
        subst hc1
        show Progress.Mm.time p d n = _
        simp [Progress.Mm.time, hsd, Site.pipe, Progress.Mm.endOff, tcT]
  have hl' : 1 ≤ c → (l = true ↔ ∃ R bal, Epilogue.Picked p L h R bal) := fun h1 => by
    rw [hl h1]
    exact ⟨fun ⟨R, bal, hP⟩ => ⟨R, bal, Epilogue.Picked.cta hcta hP⟩,
      fun ⟨R, bal, hP⟩ => ⟨R, bal, Epilogue.Picked.cta hcta.symm hP⟩⟩
  have hcntle : ∀ k, ((X.tr h).take k).countP isTcColl ≤ c := fun k =>
    le_trans (List.take_sublist _ _).countP_le hle
  have key : ∀ k σ, k ≤ (X.tr h).length → Frame.stateAt (thread p L) X h k = some (some σ) →
      Progress.time p L h σ ≤ tcT p l c ∧
        (tcAt p L h σ = false → Progress.time p L h σ + 1 ≤ tcT p l c) := fun k σ hk hσ' =>
    mma_tc_le hp hX hub hh hwh hσ'
      (by rw [← mma_tc_count hp hX hub hh hwh hFw hk hσ']; exact hcntle k) hc2 hl'
  rw [hT]
  unfold Sched.threadTime
  split
  · rename_i σ hσ'; exact (key _ σ le_rfl hσ').1
  · exact Nat.zero_le _
  · rename_i hnone
    split
    · rename_i σ hσ'
      by_cases hat' : tcAt p L h σ = false
      · exact (key _ σ (Nat.sub_le _ _) hσ').2 hat'
      · -- the last event is a resource event, after which the machine goes on
        exfalso
        have hlen : 0 < (X.tr h).length := by
          by_contra h0
          rw [show (X.tr h).length = 0 by omega, Frame.stateAt_zero] at hnone
          cases hnone
        obtain ⟨e', he'⟩ : ∃ e, (X.tr h)[(X.tr h).length - 1]? = some e :=
          ⟨_, List.getElem?_eq_getElem (show (X.tr h).length - 1 < (X.tr h).length by omega)⟩
        obtain ⟨σ', hσ'', -⟩ := tc_next (by simpa using hat') e'
        have h1 := Frame.stateAt_succ (C := thread p L) he'
        rw [show Frame.stateAt (thread p L) X h ((X.tr h).length - 1) = _ from hσ',
          show (X.tr h).length - 1 + 1 = (X.tr h).length by omega] at h1
        have h2 : (thread p L h).next σ e' = none := h1.symm.trans hnone
        rw [hσ''] at h2
        cases h2
    · exact Nat.zero_le _

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
