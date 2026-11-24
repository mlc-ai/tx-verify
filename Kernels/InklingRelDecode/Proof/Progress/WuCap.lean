-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WuLate

@[expose] public section

/-!
# The epoch tables of the virtual time

The state of a thread that has made `r` register requests (resp. `b` barrier-1 events) is timed no
later than `capR r` (resp. `capB b`), strictly earlier if its own instruction is not a request
(resp. not a barrier-1 event), and exactly at the cap if it is one. `capR` is for the default
partition or for a worker; `capB` is the same for every machine (the four generations of barrier 1
are at `c0`, `c1`, `c2`, `c3` in every machine).

The counts of a state are its phase (`tPh`) plus three per round of the workers' dispatch loop
(`LedgerInv.lean`). The round marker is read through `late_inv`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Ledger
open PTX.Kernels.InklingRelDecode.Proof.Progress PTX.Kernels.InklingRelDecode.Proof.Progress.Wt

noncomputable section
set_option maxRecDepth 100000
open Classical

/-- The cap of the time of a state that has made `r` register requests: the time of the state of
the request of ordinal `r`. -/
def capR (dflt : Bool) : Nat → Nat
  | 0 => if dflt then 100 else 30
  | 1 => 285
  | 2 => epi0 + 280
  | 3 => if dflt then epi0 + 310 else epi0 + 284
  | r + 4 => epi0 + 311 + r

/-- The cap of the time of a state that has made `b` barrier-1 events: the time of the barrier-1
event of ordinal `b`. -/
def capB : Nat → Nat
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => c3
  | b + 4 => epi0 + 311 + b

theorem capR_lt (dflt : Bool) {r r' : Nat} (h : r < r') : capR dflt r < capR dflt r' := by
  cases dflt <;> rcases r with _ | _ | _ | _ | r <;> rcases r' with _ | _ | _ | _ | r' <;>
    simp only [capR, Bool.false_eq_true, ↓reduceIte] <;> wt_omega

theorem capR_le (dflt : Bool) {r r' : Nat} (h : r ≤ r') : capR dflt r ≤ capR dflt r' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (capR_lt dflt h).le

theorem capB_lt {b b' : Nat} (h : b < b') : capB b < capB b' := by
  rcases b with _ | _ | _ | _ | b <;> rcases b' with _ | _ | _ | _ | b' <;>
    simp only [capB] <;> wt_omega

theorem capB_le {b b' : Nat} (h : b ≤ b') : capB b ≤ capB b' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (capB_lt h).le

theorem capR_true_ge {r : Nat} (h : 3 ≤ r) : epi0 + 310 ≤ capR true r := by
  rcases r with _ | _ | _ | _ | r <;> simp only [capR, ↓reduceIte] <;> wt_omega

theorem capR_false_ge {r : Nat} (h : 4 ≤ r) : epi0 + 311 ≤ capR false r := by
  rcases r with _ | _ | _ | _ | r <;> simp only [capR, Bool.false_eq_true, ↓reduceIte] <;>
    wt_omega

theorem capB_ge {b : Nat} (h : 4 ≤ b) : epi0 + 311 ≤ capB b := by
  rcases b with _ | _ | _ | _ | b <;> simp only [capB] <;> wt_omega

/-- The six statements of the tables for a time `T`, at counts `r` and `b`. -/
def Tbl (dflt : Bool) (T : Nat) (r b : Nat) (req b1 : Bool) : Prop :=
  T ≤ capR dflt r ∧ (req = false → T < capR dflt r) ∧ (req = true → capR dflt r ≤ T) ∧
  T ≤ capB b ∧ (b1 = false → T < capB b) ∧ (b1 = true → capB b ≤ T) ∧ T ≤ epi0 + 300

theorem pro_lt {s : ProA.Site} (h : s ≠ .bar18) : s.ctorIdx < 181 := by
  have h1 := Bound.ProA.ctorIdx_le_top s
  have h2 : Bound.ProA.top = 181 := rfl
  have h3 : s.ctorIdx ≠ 181 := by
    intro h4
    apply h
    cases s <;> first | rfl | exact absurd h4 (by decide)
  omega

/-- The default partition's tables. -/
theorem dcomp_tbl {L : Launch} {g : Nat} {Q : Params} {s : DComp.St} (hI : DComp.Inv L g Q s) :
    Tbl true (dcompT s) (dPh s).1 (dPh s).2 (dReq s).isSome (dB1 s) := by
  cases s with
  | dstart d =>
    have h1 := dstartT_le d
    have h2 := hI.2
    obtain ⟨s, tm⟩ := d
    simp only at h2
    cases s <;> simp [Tbl, dcompT, dstartT, dPh, dReq, dB1, dstartReq, capR, capB] at h2 h1 ⊢
    all_goals wt_omega
  | pro d =>
    have h1 := Bound.ProA.ctorIdx_le_top d.site
    have h2 : Bound.ProA.top = 181 := rfl
    obtain ⟨s, dt⟩ := d
    simp only at h1
    by_cases hb : s = .bar18
    · subst hb
      have h0 : ProA.Site.bar18.ctorIdx = 181 := rfl
      simp [Tbl, dcompT, proT, dPh, dReq, dB1, proReq, proB1, h0, capR, capB]
      wt_omega
    · have hl := pro_lt hb
      by_cases hm : s = .sMax
      · subst hm
        have h0 : ProA.Site.sMax.ctorIdx = 0 := rfl
        simp [Tbl, dcompT, proT, dPh, dReq, dB1, proReq, proB1, h0, capR, capB]
        wt_omega
      · have e1 : dPh (.pro ⟨s, dt⟩) = (1, 0) := by
          cases s <;> first | exact absurd rfl hm | rfl
        have e2 : dReq (.pro ⟨s, dt⟩) = none := by
          cases s <;> first | exact absurd rfl hm | rfl
        have e3 : dB1 (.pro ⟨s, dt⟩) = false := by
          cases s <;> first | exact absurd rfl hb | rfl
        simp [Tbl, dcompT, proT, e1, e2, e3, capR, capB]
        wt_omega
  | sm d =>
    have h1 := hI.i
    have h2 := Bound.Sm.r26_lt hI.ok
    obtain ⟨s, e0, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
    simp only at h1
    cases s <;>
      simp [Tbl, dcompT, smT, dPh, dReq, dB1, smReq, smB1, Bound.Sm.pos, capR, capB] at h2 h1 ⊢ <;>
      wt_omega
  | epi d =>
    have h1 := Bound.Epi.siteRank_le d.site
    obtain ⟨s, pr, o, sk⟩ := d
    simp only [Bound.Epi.top] at h1
    cases s <;>
      simp [Tbl, dcompT, epiT, dPh, dReq, dB1, epiReq, epiB1, Bound.Epi.siteRank, capR, capB]
        at h1 ⊢ <;> wt_omega

/-- The worker threads' tables. `t` is the number of rounds of the dispatch loop. -/
theorem wcomp_tbl {L : Launch} {g : Nat} {s : WComp.WSt} {t : Nat} (hI : WComp.Inv L g s)
    (hto : wTo s = false) (ht : t ≤ 1) (hk1 : wKind s = 1 → t = 0) (hk2 : wKind s = 2 → 1 ≤ t)
    (hl : ∀ P, (s = .worker ⟨.loop, P⟩ ∨ s = .worker ⟨.bar2, P⟩ ∨ s = .worker ⟨.ldRole, P⟩) →
      (Worker.late P ↔ t = 1)) :
    Tbl false (wcompT s) ((wPh s).1 + 3 * t) ((wPh s).2 + 3 * t)
      (wReqS s).isSome (wB1S s) := by
  cases s with
  | worker w =>
    obtain ⟨site, P⟩ := w
    have hx := hl P
    rcases (by omega : t = 0 ∨ t = 1) with rfl | rfl <;>
    cases site <;>
      first
      | (simp [wTo] at hto; done)
      | (have hP := hx (.inl rfl)
         simp [Tbl, wcompT, workerT, wPh, wReqS, wB1S, wReq, wB1, capR, capB] at hP ⊢
         (try simp [hP])
         (try wt_omega))
      | (have hP := hx (.inr (.inl rfl))
         simp [Tbl, wcompT, workerT, wPh, wReqS, wB1S, wReq, wB1, capR, capB] at hP ⊢
         (try simp [hP])
         (try wt_omega))
      | (have hP := hx (.inr (.inr rfl))
         simp [Tbl, wcompT, workerT, wPh, wReqS, wB1S, wReq, wB1, capR, capB] at hP ⊢
         (try simp [hP])
         (try wt_omega))
      | (simp [Tbl, wcompT, workerT, wPh, wReqS, wB1S, wReq, wB1, capR, capB]
         (try wt_omega))
  | idle d =>
    have ht0 := hk1 rfl
    subst ht0
    obtain ⟨s, P⟩ := d
    cases s <;> simp [Tbl, wcompT, idleT, wPh, wReqS, wB1S, idleReq, idleB1, capR, capB] <;>
      wt_omega
  | loader d P =>
    have ht0 := hk1 rfl
    subst ht0
    have hb : d.site.inLoop = true → d.i < 2 ^ 33 := fun hl => by
      have h1 := (hI.1.loop hl).2
      have h2 := Raw.word32Of_lt (hI.1.bits hl).2
      omega
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    cases s <;>
      simp [Loader.Site.inLoop] at hb <;>
      simp [Tbl, wcompT, loaderT, wPh, wReqS, wB1S, loaderReq, loaderB1, Bound.Loader.pos, capR,
        capB] <;> wt_omega
  | mma d P =>
    have ht0 := hk1 rfl
    subst ht0
    have hn := hI.1.n
    have hqk := hI.1.qk
    have hpv := hI.1.pv
    have hpre := hI.1.pre
    obtain ⟨s, i, n, tm, pro⟩ := d
    cases s <;>
      simp [Mma.QkSite, Mma.PvSite, Mma.PreSite] at hqk hpv hpre <;>
      simp [Tbl, wcompT, mmaT, wPh, wReqS, wB1S, mmaReq, mmaB1, Bound.Mma.pos, capR, capB] <;>
      wt_omega
  | exit x =>
    have ht1 := hk2 rfl
    obtain ⟨s, P⟩ := x
    have ht0 : t = 1 := by omega
    subst ht0
    cases s <;> simp [Tbl, wcompT, exitT, wPh, wReqS, wB1S, capR, capB] <;> wt_omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wu
