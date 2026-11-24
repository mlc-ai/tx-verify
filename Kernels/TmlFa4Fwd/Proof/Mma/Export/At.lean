-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaPoll
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Mma.Counts
import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The place, the round, the commits and the time of the MMA warp's committing lane

`mma_at`: at every state of a lane of warp 12 that wins every election it makes, in a CTA with a
tile of `R` rounds, the lane's commits to every barrier are the closed form at a place `q` with `r`
rounds done, and its time is that of the place (before the pipeline, below the first slot's end of
the prime region; past the pipeline `q = 100` and `r = R`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (RefQ electAll commitAt)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The time of an MMA lane at place `q` with `r` rounds done. -/
def MmaTime (p : Params) (q r R t : Nat) : Prop :=
  (q = 0 ∧ r = 0 ∧ t + 1 < Progress.primeBase p + 1024) ∨
    (q < 86 ∧ (q < 20 → r = 0) ∧ (20 ≤ q ∧ q < 60 → r < R) ∧ (60 ≤ q → r = R) ∧
      t = Progress.Mm.pipeT p q r) ∨ (q = 100 ∧ r = R)

private theorem ord_tab (s : Mma.Site) : (s.pipe = true → s.ord < 86) ∧
    (s.pipe = false → s.late = true → s.ord = 100) ∧
    (s.pipe = false → s.late = false → s.ord = 0) := by
  cases s <;> simp [Mma.Site.pipe, Mma.Site.late, Mma.Site.ord]
  case wt k => revert k; decide
  case sh k => revert k; decide
  case eq k => revert k; decide
  case qk k _ => revert k; decide
  case ce k => revert k; decide
  case cm k => revert k; decide
  case ep k => revert k; decide
  case pv k j =>
    fin_cases k <;> simp <;> split <;> omega
  case mw k _ => revert k; decide

private theorem end_site {s : Mma.Site} {x : Bool × Nat} (h : Progress.Mm.endOff s = some x)
    (hl : s.late = false) : s.early = false ∧ s.epi = .exit false := by
  cases s <;> simp only [Progress.Mm.endOff, reduceCtorEq] at h <;>
    simp only [Mma.Site.late] at hl <;> subst hl <;> exact ⟨rfl, rfl⟩

private theorem late_not_early {s : Mma.Site} (h : s.late = true) : s.early = false := by
  cases s <;> first | rfl | cases h

private theorem late_epi {s : Mma.Site} (h : s.late = false) : s.epi.late = false := by
  cases s <;> first | rfl | exact h

/-- A lane with no election has no commit. -/
private theorem commit_zero {q r o : Nat} (h : electAll q r = 0) : commitAt q r o = 0 := by
  have hr : r = 0 := by
    simp only [electAll, Mma.pq] at h
    norm_num at h
    omega
  have hq : q ≤ 5 := by
    simp only [electAll, Mma.pq] at h
    norm_num at h
    omega
  subst hr
  have : ∀ q < 6, Mma.ringRel q 0 = 0 ∧
      ∀ x ∈ [8, 34, 14, 47, 61, 63, 83, 85], Mma.pq x q 0 = 0 := by decide
  obtain ⟨h1, h2⟩ := this q (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h2
  simp only [commitAt, h1, h2, Mma.ringCount]
  split_ifs <;> omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g = 12)
  (hwin : ∀ j pc mk inst ld, X.get (g, j) = some ⟨pc, .elect mk inst ld⟩ → ld = laneOf L g)
  {R : Nat} (hR : MmaRounds p L g R)
include hp hX hFw hub hg hw hwin hR

theorem mma_at {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    ∃ q r, (∀ o, ((X.tr g).take k).countP (commitsTo (obj L g o)) = commitAt q r o) ∧
      MmaTime p q r R (Progress.time p L g σ) := by
  have hJ := (goodR hp hX hFw hg k).2 σ hσ
  have hsp := Progress.scanBase_le_primeBase p
  have h4 : Progress.scanBase + 4 ≤ Progress.primeBase p := by unfold Progress.primeBase; omega
  have hzero : ∀ o, commitAt 0 0 o = 0 := fun o => by
    simp [commitAt, Mma.pq, Mma.ringRel, Mma.ringCount]
    intro _ _ _
    omega
  have hcom : ∀ o, ((X.tr g).take k).countP (commitsTo (obj L g o)) =
      σ.2 (.mma (.commit (obj L g o))) := fun o => by rw [mma_commits, count hσ]
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · have hS := (Mma.good hp hX (cuQReadsFromLaunch hp hX) hg hw k).2 _ hσ
    refine ⟨0, 0, fun o => ?_, .inl ⟨rfl, rfl, ?_⟩⟩
    · rw [hcom, hzero]; exact (hS.2.2.1 _).2
    · have hx : ∀ r, s.site ≠ .enter r := by
        intro r he
        have h1 := hS.1
        simp only [StartAt, he] at h1
      have h1 := Progress.startTime_lt hx
      simp only [Progress.time]
      omega
  cases i with
  | mma =>
    obtain ⟨-, hS⟩ := JR.mma hJ
    rcases d with s | ⟨u, d⟩
    · refine ⟨0, 0, fun o => ?_, .inl ⟨rfl, rfl, ?_⟩⟩
      · rw [hcom, hzero]; exact (hS.2.2.1 _).2
      · simp only [Progress.time, Progress.roleTime, Progress.Mm.startT]
        split <;> omega
    · have hub0 : n .ub = 0 := by
        by_contra h
        obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
        cases kind <;> simp [cls] at hk
        exact hub ⟨(g, j), pc, _, hf⟩
      obtain ⟨⟨r, w, hQ, -⟩, hF⟩ := hS hub0
      have hlost : n (.mma .lost) = 0 := by
        by_contra h
        obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
        cases kind <;> simp [cls, Mma.cls] at hk
        exact hk.2 (hwin _ _ _ _ _ hf)
      have hC : ∀ o, ((X.tr g).take k).countP (commitsTo (obj L g o)) =
          commitAt d.site.ord r o := by
        intro o
        rw [hcom]
        have h1 := hQ.com o
        change n (.mma (.commit (obj L g o))) = _ at h1
        simp only
        rw [h1]
        cases w with
        | true => rfl
        | false =>
          have h2 := hQ.lost
          change n (.mma .lost) = _ at h2
          rw [hlost] at h2
          simp only [Bool.false_eq_true, ite_false] at h2 ⊢
          exact (commit_zero h2.symm).symm
      refine ⟨_, r, hC, ?_⟩
      obtain ⟨o1, o2, o3⟩ := ord_tab d.site
      cases hpipe : d.site.pipe with
      | true =>
        right; left
        have h86 := o1 hpipe
        obtain ⟨R', bal, hC', hB⟩ := Mma.bs_ref (Mma.pmid_of hpipe) hF
        have hR' : MmaRounds p L g _ := ⟨R', bal, hC'.1, rfl⟩
        have hun := hR'.unique hR
        change (Mma.Bs p L g (mmaRef p L g R' bal)).toNat - 1 = R at hun
        have hB' : Mma.Bs p L g d.v = Mma.Bs p L g (mmaRef p L g R' bal) := hB
        refine ⟨h86, hQ.pre, fun hq => ?_, fun hq => ?_, ?_⟩
        · have h1 := (hQ.loop hq).1
          rw [hB'] at h1
          change (r : Int) + 1 < Mma.Bs p L g (mmaRef p L g R' bal) at h1
          generalize Mma.Bs p L g (mmaRef p L g R' bal) = B at h1 hun
          omega
        · have h1 := hQ.tail ⟨hq, Nat.lt_trans h86 (by decide)⟩
          rw [hB'] at h1
          change (r : Int) + 1 = Mma.Bs p L g (mmaRef p L g R' bal) ∨
            (r = 0 ∧ Mma.Bs p L g (mmaRef p L g R' bal) < 2) at h1
          generalize Mma.Bs p L g (mmaRef p L g R' bal) = B at h1 hun
          omega
        · simp only [Progress.time, Progress.roleTime, Progress.Mm.time, hpipe, ite_true]
          unfold Progress.Mm.pipeT
          by_cases h20 : d.site.ord < 20
          · simp only [h20, ite_true]
          · rw [Progress.Mm.round_eq (by omega) h86 hQ.ps]
      | false =>
        cases hlate : d.site.late with
        | true =>
          right; right
          refine ⟨o2 hpipe hlate, ?_⟩
          have hearly := late_not_early hlate
          obtain ⟨-, -, -, hl, -⟩ := Mma.mfits_main hearly hF
          obtain ⟨R', bal, hP, hps⟩ := hl hlate
          have hR' : MmaRounds p L g _ := ⟨R', bal, hP, rfl⟩
          have hun := hR'.unique hR
          have h1 := hQ.ps
          rw [o2 hpipe hlate, hps, Mma.pipeN, Progress.Mm.shAt_lin,
            Progress.Mm.shAt_lin 100 r] at h1
          change (Mma.Bs p L g (Mma.refV p L g R' bal)).toNat - 1 = R at hun
          omega
        | false =>
          left
          refine ⟨o3 hpipe hlate, hQ.pre (by rw [o3 hpipe hlate]; omega), ?_⟩
          obtain ⟨R', bal, hP, -⟩ := hR
          simp only [Progress.time, Progress.roleTime, Progress.Mm.time, hpipe,
            Bool.false_eq_true, ite_false]
          split
          · rename_i l o ho
            obtain ⟨he, hx⟩ := end_site ho hlate
            exact (noPicked_of_exit (Mma.mfits_main he hF).2.1 hx ⟨R', bal, hP⟩).elim
          split
          · omega
          have hc : Progress.Mm.scans d n ≤ Progress.cmax p + 2 := by
            have hb : Progress.Out.ballots d.site.toE ≤ 1 := by
              unfold Progress.Out.ballots; split <;> omega
            unfold Progress.Mm.scans Progress.cmax
            cases he : d.site.early with
            | true =>
              simp only [Mma.MFits, he, ite_true] at hF
              omega
            | false =>
              obtain ⟨h1, h2, -⟩ := Mma.mfits_main he hF
              have := Epilogue.fits_coll_le hp h2 (late_epi hlate)
              omega
          rw [hlate]
          simp only [Bool.false_eq_true, ite_false, Progress.passTime, Progress.primeBase]
          split <;> omega
  | softmax => have := (JR.softmax hJ).1; omega
  | correction => obtain ⟨h1, h2, -⟩ := JR.correction hJ (by omega); omega
  | epilogue => have := (JR.epilogue hJ).1; omega
  | loader b => have := (JR.loader hJ).1; omega
  | stub r => exact (JR.not_stub hJ).elim

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
