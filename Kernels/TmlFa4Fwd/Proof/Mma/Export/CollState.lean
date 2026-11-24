-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollCount
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.CollPos
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every state of the MMA warp stands in its schedule of collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase passTime)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The collective a thread state of the MMA warp is at. -/
def tagOf (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Option CollTag :=
  match σ with
  | (.inl s, _) => match s.site with | .sh j => some (.start j) | _ => none
  | (.inr ⟨.mma, .inr ⟨_, d⟩⟩, _) => if d.site.wcoll then some (.site d.site) else none
  | _ => none

theorem tagOf_isSome (σ : (thread p L g).D) : (tagOf p L g σ).isSome = mmaAt p L g σ := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · simp only [tagOf, mmaAt]; cases s.site <;> rfl
  all_goals first
    | rfl
    | (rcases d with s | ⟨u, d⟩
       · rfl
       · simp only [tagOf, mmaAt]; cases d.site.wcoll <;> rfl)

private theorem site_tab : ∀ s : Site, s.pipe = true →
    (s.ord < 86) ∧ (s.wcoll = true ↔ s.ord ∈ collQ) := by
  intro s h
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

private theorem wcoll_false : ∀ s : Site, s.early = false → s.pipe = false → s.scan = false →
    s.wcoll = false := by
  intro s h1 h2 h3
  cases s <;> first
    | rfl
    | (cases h1; done)
    | (cases h2; done)
    | cases h3

private theorem late_ord : ∀ s : Site, s.late = true → s.ord = 100 := by
  intro s h
  cases s <;> first
    | (cases h; done)
    | (simp only [Site.late] at h; simp only [Site.ord, h, ite_true])

private theorem not_late_ord : ∀ s : Site, s.pipe = false → s.late = false → s.ord = 0 := by
  intro s h1 h
  cases s <;> first
    | rfl
    | (cases h1; done)
    | (simp only [Site.late] at h; simp only [Site.ord, h, Bool.false_eq_true, ite_false])

private theorem scan_late : ∀ s : Site, s.scan = true → s.toE.late = s.late := by
  intro s h
  cases s <;> first
    | rfl
    | cases h

private theorem rest_cases : ∀ s : Site, s.early = false → s.pipe = false → s.scan = false →
    (s = .q0 ∨ s = .q1 ∨ s = .uk) ∨ ∃ l, s.epi = .exit l ∧ s.late = l := by
  intro s h1 h2 h3
  cases s <;> first
    | (cases h1; done)
    | (cases h2; done)
    | (cases h3; done)
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inl (.inr (.inr rfl))
    | exact .inr ⟨_, rfl, rfl⟩

/-- A scan state's ballots of its pass. -/
private theorem scan_band {dE : Epilogue.D} {ns nv : Nat} (hF : Epilogue.Fits p L g dE ns nv)
    {s : Site} (hs : s.scan = true) (he : dE.site = s.toE) :
    ∃ n0 v0, Epilogue.PassStart p L g s.late n0 v0 ∧ n0 ≤ ns ∧
      nv = v0 + Progress.Out.ballots s.toE := by
  cases s <;> simp only [Site.scan, Bool.false_eq_true] at hs <;>
    simp only [Site.toE] at he <;> simp only [Epilogue.Fits, he] at hF <;>
    obtain ⟨r, n0, v0, hP, -, h1, h2, -⟩ := hF <;>
    exact ⟨n0, v0, hP, by omega, by simp only [Site.toE, Progress.Out.ballots]; omega⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
include hp hX hFw hub hg hw

omit hp hX hFw hub hg hw in
/-- The total of the elections. -/
private theorem won_lost {d : D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) :
    n (.mma .won) + n (.mma .lost) = electAll d.site.ord r := by
  have h1 := hQ.won
  have h2 := hQ.lost
  change n (.mma .won) = _ at h1
  change n (.mma .lost) = _ at h2
  rw [h1, h2]
  cases w <;> simp

omit hX hFw hub hg hw in
/-- A role state. -/
private theorem role_cls {d : D} {n : Cls → Nat} {r : Nat} {w : Bool}
    (hQ : RefQ p L g d.site.ord d.v (Mma.rc n) r w) (hF : MFits p L g d (n .shfl) (n .vote))
    {u : Unit} : MCls p L g (mmaCnt p L g (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n))
      (Progress.time p L g (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n))
      (if d.site.wcoll then some (.site d.site) else none) := by
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  have hE := won_lost hQ
  have hN : mmaCnt p L g (.inr ⟨.mma, .inr ⟨u, d⟩⟩, n) =
      n .shfl + n .vote + electAll d.site.ord r := by
    simp only [mmaCnt]; omega
  rw [hN]
  show MCls p L g _ (Progress.Mm.time p d n) _
  clear hN hE
  cases he : d.site.early with
  | true =>
    have hF' := hF
    simp only [MFits, he, ite_true] at hF'
    obtain ⟨h3, hv, hps⟩ := hF'
    have hpipe : d.site.pipe = false := by
      revert he; cases d.site <;> simp [Site.early, Site.pipe]
    have ho : d.site.ord = 0 := by revert he; cases d.site <;> simp [Site.early, Site.ord]
    have hr : r = 0 := hQ.pre (by omega)
    have h0 : electAll 0 0 = 0 := by decide
    rw [ho, hr, h0, h3, hv]
    cases hs : d.site <;> rw [hs] at he <;> simp only [Site.early, Bool.false_eq_true] at he
    · refine .early _ ?_
      simp only [Progress.Mm.time, hs, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true, ite_false,
        ite_true]
      omega
    · refine .early _ ?_
      simp only [Progress.Mm.time, hs, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true, ite_false,
        reduceCtorEq, Site.late, Progress.Mm.scans, Site.toE, Progress.Out.ballots,
        Progress.Mm.coll, Site.scan, Bool.false_and, passTime]
      omega
    · have ht : Progress.Mm.time p d n = scanBase + 6 := by
        simp only [Progress.Mm.time, hs, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true,
          ite_false, reduceCtorEq, Site.late, Progress.Mm.scans, Site.toE, Progress.Out.ballots,
          Progress.Mm.coll, passTime, ite_true]
        omega
      rw [ht]
      exact .bcast
  | false =>
  obtain ⟨h1, h2, -, h4, h5⟩ := mfits_main he hF
  cases hpipe : d.site.pipe with
  | true =>
    obtain ⟨R0, bal, hC, hB⟩ := bs_ref (pmid_of hpipe) hF
    have hB' : Bs p L g d.v = Bs p L g (mmaRef p L g R0 bal) := hB
    have hR : MmaRounds p L g _ := ⟨R0, bal, hC.1, rfl⟩
    obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := id hC
    obtain ⟨t1, t2⟩ := site_tab d.site hpipe
    have hpl : PlaceOk d.site.ord r ((Bs p L g (mmaRef p L g R0 bal)).toNat - 1) := by
      refine ⟨t1, hQ.pre, fun hq => ?_, fun hq => ?_⟩
      · have := (hQ.loop hq).1
        rw [hB'] at this
        change (r : Int) + 1 < Bs p L g (mmaRef p L g R0 bal) at this
        generalize Bs p L g (mmaRef p L g R0 bal) = B at this ⊢
        omega
      · have := hQ.tail ⟨hq, Nat.lt_trans t1 (by decide)⟩
        rw [hB'] at this
        change (r : Int) + 1 = Bs p L g (mmaRef p L g R0 bal) ∨
          (r = 0 ∧ Bs p L g (mmaRef p L g R0 bal) < 2) at this
        generalize Bs p L g (mmaRef p L g R0 bal) = B at this ⊢
        omega
    have hps := hQ.ps
    have hN : n .shfl + n .vote + electAll d.site.ord r =
        1 + chN R0 bal + pipeCnt d.site.ord r := by
      unfold chN pipeCnt; omega
    have ht : Progress.Mm.time p d n = Progress.Mm.pipeT p d.site.ord r := by
      simp only [Progress.Mm.time, hpipe, ite_true]
      unfold Progress.Mm.pipeT
      by_cases h20 : d.site.ord < 20
      · simp only [h20, ite_true]
      · rw [Progress.Mm.round_eq (by omega) t1 hps]
    rw [hN, ht]
    refine .pipe R0 bal _ _ _ _ hP hR hpl ⟨d.site, rfl, hpipe, fun hq => ?_, fun x hx => ?_⟩
    · simp [t2.mpr hq]
    · by_contra hq
      rw [← t2] at hq
      simp [hq] at hx
  | false =>
  have ho : d.site.late = false → d.site.ord = 0 ∧ r = 0 ∧ d.v.ps = 0 := fun hl => by
    have h0 := not_late_ord d.site hpipe hl
    exact ⟨h0, hQ.pre (by omega), h5 hpipe hl⟩
  have ho2 : d.site.late = true → d.site.ord = 100 := late_ord d.site
  have hep : d.site.epi = (toE d).site := rfl
  have hTot : d.site.late = true → ∃ R, MmaRounds p L g R ∧ ∃ R0 bal,
      Epilogue.Picked p L g R0 bal ∧ d.v.ps + electAll d.site.ord r = pipeCnt 100 R := fun hl => by
    obtain ⟨R0, bal, hP, hps⟩ := h4 hl
    refine ⟨_, ⟨R0, bal, hP, rfl⟩, R0, bal, hP, ?_⟩
    have hps' := hQ.ps
    have h100 := ho2 hl
    rw [h100] at hps' ⊢
    have hr : r = (Bs p L g (mmaRef p L g R0 bal)).toNat - 1 := by
      have e : shAt 100 r = shAt 100 (Bs p L g (refV p L g R0 bal) - 1).toNat := hps'.symm.trans hps
      rw [Progress.Mm.shAt_lin,
        Progress.Mm.shAt_lin 100 (Bs p L g (refV p L g R0 bal) - 1).toNat] at e
      change r = (Bs p L g (refV p L g R0 bal)).toNat - 1
      omega
    rw [hps', hr]
    rfl
  have hcoll : d.site.scan = true → d.site.epi = d.site.toE ∧
      d.site.wcoll = Progress.Out.coll d.site.toE ∧
      Progress.Mm.coll d.site = Progress.Out.coll d.site.toE ∧ d.site ≠ .bar1 ∧
      Progress.Mm.endOff d.site = none := fun hs => by
    refine ⟨toE_eq hs, ?_, ?_, ?_, ?_⟩ <;> revert hs <;> cases d.site <;>
      simp [Site.scan, Site.wcoll, Site.toE, Progress.Out.coll, Epilogue.Site.shfl,
        Epilogue.Site.ballot, Progress.Mm.coll, Progress.Mm.endOff]
  cases hscan : d.site.scan with
  | true =>
    obtain ⟨c1, c2, c3, c4, c5⟩ := hcoll hscan
    obtain ⟨n0, v0, hps, hn0, hnv⟩ := scan_band h2 hscan (by rw [← hep, c1])
    have hv0 := Epilogue.passStart_v0 hps
    have ht : Progress.Mm.time p d n = passTime (if d.site.late then endBase p else scanBase)
        (n .shfl - d.v.ps + Progress.Out.ballots d.site.toE) (Progress.Out.coll d.site.toE) := by
      simp only [Progress.Mm.time, hpipe, Bool.false_eq_true, ite_false, c5, c4, c3,
        Progress.Mm.scans]
    cases hl : d.site.late with
    | false =>
      obtain ⟨o1, o2, o3⟩ := ho hl
      have e0 : electAll 0 0 = 0 := by decide
      have hbd := Epilogue.fits_coll_le hp h2 (by
        rw [← hep, c1, scan_late d.site hscan, hl])
      rw [hl] at hps hv0 ht
      simp only [Bool.false_eq_true, ite_false] at hv0 ht
      have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
      have h30 := Epilogue.passStart_ge hps
      cases hco : Progress.Out.coll d.site.toE with
      | true =>
        rw [hco] at ht
        obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ :=
          Epilogue.coll_pos h2 (by rw [← hep, c1]; exact hco)
        have hll : l = false := by
          rw [← hq.late, ← hep, c1, scan_late d.site hscan, hl]
        subst hll
        obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same rfl hps hps'
        simp only [Epilogue.PassStart, Bool.false_eq_true, ite_false] at hps
        rw [c2, hco, o1, o2, e0]
        have hN : n .shfl + n .vote + 0 = 4 + q := by omega
        have ht' : Progress.Mm.time p d n = scanBase + 2 * (4 + q) := by
          rw [ht]; simp only [passTime, ite_true]; omega
        rw [hN, ht']
        exact .scan q d.site c1 hscan (by rw [hep]; exact hq)
      | false =>
        rw [hco] at ht
        rw [c2, hco, o1, o2, e0]
        have hN : n .shfl + n .vote + 0 = (n .shfl - 1 + n .vote) + 1 := by omega
        rw [hN, ht]
        simp only [passTime, Bool.false_eq_true, ite_false]
        exact .scanOff _ _ (by omega) (by omega) (by omega)
    | true =>
      obtain ⟨R, hR, R0, bal, hP, htot⟩ := hTot hl
      rw [hl] at hps hv0 ht
      simp only [ite_true] at hv0 ht
      have hge : chN R0 bal = n0 + v0 := by
        simp only [Epilogue.PassStart, ite_true] at hps
        obtain ⟨R', bal', hP', rfl, rfl⟩ := hps
        obtain ⟨rfl, rfl⟩ := hP'.unique hP
        unfold chN; omega
      cases hco : Progress.Out.coll d.site.toE with
      | true =>
        rw [hco] at ht
        obtain ⟨l, n0', v0', q, hps', hq1, hq⟩ :=
          Epilogue.coll_pos h2 (by rw [← hep, c1]; exact hco)
        have hll : l = true := by
          rw [← hq.late, ← hep, c1, scan_late d.site hscan, hl]
        subst hll
        obtain ⟨rfl, rfl⟩ := Epilogue.PassStart.same rfl hps hps'
        rw [c2, hco]
        have hN : n .shfl + n .vote + electAll d.site.ord r =
            1 + pipeCnt 100 R + (n0 + v0 + q) := by omega
        have ht' : Progress.Mm.time p d n = endBase p + 2 * (n0 + v0 + q) := by
          rw [ht]; simp only [passTime, ite_true]; omega
        rw [hN, ht']
        exact .scan2 R0 bal R n0 v0 q d.site hP hR hps c1 hscan (by rw [hep]; exact hq)
      | false =>
        rw [hco] at ht
        rw [c2, hco]
        have hN : n .shfl + n .vote + electAll d.site.ord r =
            1 + pipeCnt 100 R + (n .shfl - 1 - d.v.ps + n .vote) := by omega
        rw [hN, ht]
        simp only [passTime, Bool.false_eq_true, ite_false]
        exact .scan2Off R0 bal R _ _ hP hR (by omega) (by omega) (by omega)
  | false =>
    have hwc : d.site.wcoll = false :=
      wcoll_false d.site he hpipe hscan
    rw [hwc]
    have hcase : (d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) ∨
        ∃ l, d.site.epi = .exit l ∧ d.site.late = l := by
      exact rest_cases d.site he hpipe hscan
    rcases hcase with hq | ⟨l, hx, hl⟩
    · have hl : d.site.late = false := by rcases hq with h | h | h <;> rw [h] <;> rfl
      obtain ⟨o1, o2, o3⟩ := ho hl
      have e0 : electAll 0 0 = 0 := by decide
      have hC : ∃ R0 bal, Epilogue.ChosenVals p L g R0 bal (toE d) (n .shfl - 1 - d.v.ps)
          (n .vote) := by
        have h2' := h2
        rcases hq with h | h | h <;> simp only [Epilogue.Fits, toE, h, Site.epi] at h2'
        · exact h2'
        · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
        · obtain ⟨R0, bal, hC, -⟩ := h2'; exact ⟨R0, bal, hC⟩
      obtain ⟨R0, bal, hC⟩ := hC
      have hbd := Epilogue.chosen_coll_le hp hC
      obtain ⟨-, -, -, -, -, -, -, hns, hnv⟩ := hC
      have hcm : Progress.cmax p = 7 * (p.batch + 3) + 6 := rfl
      rw [o1, o2, e0]
      have hN : n .shfl + n .vote + 0 = (n .shfl - 1 + n .vote) + 1 := by omega
      have ht : Progress.Mm.time p d n = scanBase + 2 * n .shfl - 1 := by
        rcases hq with h | h | h <;>
          simp only [Progress.Mm.time, h, Site.pipe, Progress.Mm.endOff, Bool.false_eq_true,
            ite_false, reduceCtorEq, Site.late, Progress.Mm.scans, Site.toE, Progress.Out.ballots,
            Progress.Mm.coll, Site.scan, Bool.false_and, passTime, o3, Nat.sub_zero, Nat.add_zero]
      rw [hN, ht]
      exact .scanOff _ _ (by omega) (by omega) (by omega)
    · have h2' : Epilogue.Fits.ExitAt p L g l (n .shfl - 1 - d.v.ps) (n .vote) := by
        simpa only [Epilogue.Fits, toE, hx] using h2
      cases l with
      | false =>
        obtain ⟨o1, o2, o3⟩ := ho hl
        have e0 : electAll 0 0 = 0 := by decide
        rw [o1, o2, e0]
        have hN : n .shfl + n .vote + 0 = 1 + (n .shfl - 1 - d.v.ps) + n .vote := by omega
        rw [hN]
        exact .end1 _ _ _ h2'
      | true =>
        obtain ⟨R, hR, R0, bal, hP, htot⟩ := hTot hl
        have hN : n .shfl + n .vote + electAll d.site.ord r =
            1 + pipeCnt 100 R + (n .shfl - 1 - d.v.ps + n .vote) := by omega
        rw [hN]
        exact .end2 R0 bal R _ _ _ hP hR h2'

omit hFw in
/-- **A lane of the MMA warp at its return.** -/
theorem mma_exit_cls {d : D} {n : Cls → Nat} {l : Bool}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g d n)))
    (hs : d.site = .exit l) : ExitN p L g (mmaCnt p L g (minj p L g d n)) := by
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [Proof.cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨⟨r, w, hQ, -⟩, hF⟩ := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ hub0
  have hE := won_lost hQ
  have hN : mmaCnt p L g (minj p L g d n) = n .shfl + n .vote + electAll d.site.ord r := by
    rw [← hE]; rfl
  rw [hN]
  obtain ⟨h1, h2, -, h4, h5⟩ := mfits_main (by rw [hs]; rfl) hF
  have h2' : Epilogue.Fits.ExitAt p L g l (n .shfl - 1 - d.v.ps) (n .vote) := by
    simpa only [Epilogue.Fits, toE, hs, Site.epi] using h2
  cases l with
  | false =>
    have ho : d.site.ord = 0 := by rw [hs]; rfl
    have hr : r = 0 := hQ.pre (by rw [ho]; decide)
    have hps : d.v.ps = 0 := h5 (by rw [hs]; rfl) (by rw [hs]; rfl)
    have e0 : electAll 0 0 = 0 := by decide
    rw [ho, hr, e0]
    exact .inl ⟨_, _, h2', by omega⟩
  | true =>
    obtain ⟨R0, bal, hP, hps⟩ := h4 (by rw [hs]; rfl)
    have h100 : d.site.ord = 100 := by rw [hs]; rfl
    have hps' := hQ.ps
    rw [h100] at hps' ⊢
    have hr : r = (Bs p L g (mmaRef p L g R0 bal)).toNat - 1 := by
      have e : shAt 100 r = shAt 100 (Bs p L g (refV p L g R0 bal) - 1).toNat := hps'.symm.trans hps
      rw [Progress.Mm.shAt_lin,
        Progress.Mm.shAt_lin 100 (Bs p L g (refV p L g R0 bal) - 1).toNat] at e
      change r = (Bs p L g (refV p L g R0 bal)).toNat - 1
      omega
    refine .inr ⟨R0, bal, r, _, _, hP, ⟨R0, bal, hP, hr.symm⟩, h2', ?_⟩
    have e : pipeCnt 100 r = d.v.ps + electAll 100 r := by rw [pipeCnt, hps']
    rw [e]
    generalize electAll 100 r = E
    clear hN hE hps' e hr hps h2 h2' hQ
    omega

omit hFw in
/-- **Where a state of the MMA warp stands.** -/
theorem mma_cls {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    MCls p L g (mmaCnt p L g σ) (Progress.time p L g σ) (tagOf p L g σ) := by
  have hR := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
  have hprv : primeBase p = scanBase + 2 * Progress.cmax p + 4 := rfl
  have hsb : scanBase = 256 := rfl
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩ <;> try exact hR.elim
  · obtain ⟨hS, hv, hZ⟩ := hR
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site <;> simp only [StartAt] at hS
    case sh j =>
      have hN : mmaCnt p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = j.val := by
        simp only [mmaCnt]; have := hZ.2.1; have := hZ.2.2; omega
      rw [hN]
      have ht : Progress.time p L g (.inl ⟨.sh j, x1, x2, x3⟩, n) = Progress.shPc j.val := by
        fin_cases j <;> rfl
      rw [ht]
      exact .start j
    case fence =>
      have hN : mmaCnt p L g (.inl ⟨.fence, x1, x2, x3⟩, n) = 3 := by
        simp only [mmaCnt]; have := hZ.2.1; have := hZ.2.2; omega
      rw [hN]
      exact .early _ (by show 172 < 256 + 6; decide)
    case bar =>
      have hN : mmaCnt p L g (.inl ⟨.bar, x1, x2, x3⟩, n) = 3 := by
        simp only [mmaCnt]; have := hZ.2.1; have := hZ.2.2; omega
      rw [hN]
      exact .early _ (by show 173 < 256 + 6; decide)
  · rcases d with s | ⟨u, d⟩
    · obtain ⟨h3, hv, hZ⟩ := hR
      have hN : mmaCnt p L g (.inr ⟨.mma, .inl s⟩, n) = 3 := by
        simp only [mmaCnt]; have := hZ.2.1; have := hZ.2.2; omega
      rw [hN]
      refine .early _ ?_
      simp only [Progress.time, Progress.roleTime, Progress.Mm.startT]
      split <;> omega
    · have hub0 : n .ub = 0 := by
        by_contra h
        obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
        cases kind <;> simp [Proof.cls] at hk
        exact hub ⟨(g, j), pc, _, hf⟩
      obtain ⟨⟨r, w, hQ, -⟩, hF⟩ := hR hub0
      exact role_cls hp hQ hF

end
end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
