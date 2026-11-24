-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Export.CollCls
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.Migrated
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A block state of a loader warp: its place and its time -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (scanBase endBase primeBase doneBase passTime clk bandL)
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The collective a thread state of a loader warp is at. -/
def tagOf (p : Params) (L : Launch) (g : Nat) (σ : (thread p L g).D) : Option CollTag :=
  match σ with
  | (.inl s, _) => match s.site with | .sh j => some (.start j) | _ => none
  | (.inr ⟨.loader _, d⟩, _) => tagS d.site
  | _ => none

theorem tagOf_isSome (σ : (thread p L g).D) : (tagOf p L g σ).isSome = ldAt p L g σ := by
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  · simp only [tagOf, ldAt]; cases s.site <;> rfl
  all_goals first
    | rfl
    | (simp only [tagOf, ldAt, tagS]; cases d.site.wcoll <;> rfl)

/-- A block state's time. -/
theorem time_blk {d : D} {n : Cls → Nat} {o : Blk} (h : bc d.site = some o) :
    Progress.Ld.time p d n = if o = .prime then primeBase p + off d.site
      else clk p (Progress.Ld.slot p (Progress.Ld.idx d.site n)) (bandL + off d.site) := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [bc, reduceCtorEq, Option.some.injEq] at h
  case tw t | te t _ | ta t | tc t _ =>
    subst h
    simp only [Progress.Ld.time, off]
    by_cases h4 : t.val < 4
    · simp only [h4, ite_true]; omega
    · by_cases h6 : t.val < 6
      · simp only [h4, h6, ite_true, ite_false, reduceCtorEq]
        congr 1; omega
      · simp only [h4, h6, ite_false, reduceCtorEq]
  case pgLd per _ | pgSt per _ | rwSt per _ =>
    subst h
    cases per <;> simp only [Progress.Ld.time, off, ite_true, ite_false, reduceCtorEq] <;>
      first | omega | (congr 1; omega)
  case slot per v | commit per v | arrive per v | ptP per v _ | ptR per v _ | ptS per v _
    | lw per v _ | xl per v _ | xh per v _ | cp per v _ _ =>
    subst h
    cases per <;> cases v <;>
      simp only [Progress.Ld.time, off, ite_true, ite_false, reduceCtorEq, Bool.false_eq_true] <;>
      first | omega | (congr 1; omega) | congr 1

/-- The packet of a block site. -/
theorem idx_blk (s : Site) {n : Cls → Nat} {a : Nat}
    (hn : n (.load .commit) = 2 + 2 * a + inBlk s) : (Progress.Ld.idx s n - 2) / 2 = a := by
  unfold Progress.Ld.idx
  cases s <;> simp only [inBlk] at hn ⊢ <;> (try split_ifs at hn) <;> omega

/-- A scan state's ballots of its pass. -/
theorem ld_scan_band {dE : Epilogue.D} {ns nv : Nat} (hF : Epilogue.Fits p L g dE ns nv)
    {s : Site} (hs : s.scan = true) (he : dE.site = s.toE) :
    ∃ n0 v0, Epilogue.PassStart p L g s.lateL n0 v0 ∧ n0 ≤ ns ∧
      nv = v0 + Progress.Out.ballots (Progress.Ld.toE s) ∧
      s.wcoll = Progress.Out.coll (Progress.Ld.toE s) ∧ s.epi = s.toE ∧
      s.toE = Progress.Ld.toE s ∧ s.toE.late = s.lateL := by
  cases s <;> simp only [Site.scan, Bool.false_eq_true] at hs <;>
    simp only [Site.toE] at he <;> simp only [Epilogue.Fits, he] at hF <;>
    obtain ⟨r, n0, v0, hP, -, h1, h2, -⟩ := hF <;>
    exact ⟨n0, v0, hP, by omega, by
      simp only [Progress.Ld.toE, Progress.Out.ballots]; omega, rfl, rfl, rfl, rfl⟩

theorem time_scan {d : D} {n : Cls → Nat} (hs : d.site.scan = true) :
    Progress.Ld.time p d n = passTime (if d.site.lateL then endBase p else scanBase)
      (n .shfl - 32 * n (.load .commit) + Progress.Out.ballots (Progress.Ld.toE d.site))
      (Progress.Out.coll (Progress.Ld.toE d.site)) := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Site.scan, Bool.false_eq_true] at hs <;> rfl

theorem lc_cases (s : Site) : (lc s = .p1 → s.scan = true ∧ s.lateL = false) ∧
    (lc s = .p2 → s.scan = true ∧ s.lateL = true) ∧ (lc s = .early → s = .setmax) ∧
    (lc s = .req → s = .q0 ∨ s = .q1 ∨ s = .uk) ∧
    (lc s = .drain → (∃ j, s = .dw j) ∨ s = .dq ∨ s = .de ∨ s = .da ∨ s = .exit) := by
  cases s <;> simp only [lc, Site.scan, Site.lateL] <;> (try split_ifs) <;> simp_all

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hub : ¬ HasUb X)
  (hg : g < L.threads) {b : Bool} (hw : Prologue.warpIndex L g = wOf b)
include hp hX hub hg hw

omit hp hX hub hg hw in
theorem tma6_last {s : Site} (h : bc s = some .tma6) : s.lastGrp = true := by
  cases s <;> simp only [bc, reduceCtorEq, Option.some.injEq] at h
  case tw t | te t _ | ta t | tc t _ =>
    simp only [Site.lastGrp, beq_iff_eq]
    split_ifs at h
    omega
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | commit per _ | arrive per _
    | ptP per _ _ | ptR per _ _ | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _
    | cp per _ _ _ => cases per <;> cases h

omit hp hX hub hg hw in
theorem wOf_or : wOf b = 14 ∨ wOf b = 15 := by cases b <;> simp [wOf]

omit hp hX hub hg in
/-- A loader warp. -/
theorem wb : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15 := by
  rw [hw]; exact wOf_or

omit hub in
/-- The elections of a state, on the two warps. -/
theorem ld_els {d : D} {n : Cls → Nat} {T : Nat}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub0 : n .ub = 0) (h : Prologue.warpIndex L g = 14 → els X g k = T) :
    els X g k = if b then 0 else T := by
  cases b with
  | true => exact (elect_tot hp hX hg (wb hw) hσ hub0).2 hw
  | false => exact h hw

omit hp hX hub hg hw in
theorem tot_eq (b : Bool) (v : V) (P : Nat) : 32 * P + (if b then 0 else totEl v) =
    blkTot b (w0 v.su.r28) (decide (Last v)) P := by
  unfold blkTot totEl
  by_cases hl : Last v
  · simp only [hl, decide_true, ite_true]
  · simp only [hl, decide_false, Bool.false_eq_true, ite_false, Nat.mul_zero]

omit hp hX hub hg hw in
theorem tot_eq' (b : Bool) (v : V) (P : Nat) (s : Site) :
    32 * P + (if b then 0 else totEl v + drainEl s) =
      blkTot b (w0 v.su.r28) (decide (Last v)) P + drN b s := by
  rw [← tot_eq]
  unfold drN
  generalize totEl v = t
  generalize drainEl s = u
  clear * -
  cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false]
  omega

omit hp hX hub hg hw in
/-- The tile of a state. -/
theorem sus_tile {v : V} (hS : SuS p L g v) : ∃ R bal, Picked p L g R bal ∧
    Tile p L g (chN R bal) (w0 v.su.r28) (decide (Last v)) (pkts v.su.r28) := by
  obtain ⟨R, bal, hP, e1, e2⟩ := hS
  refine ⟨R, bal, hP, R, bal, hP, rfl, ?_, ?_, ?_⟩
  · rw [e1]; rfl
  · simp only [Last, e1, e2]; rfl
  · rw [e1]; rfl

omit hp hX hub hg hw in
theorem steady_el : AllSites fun s => (bc s != some .steady || blkEl s == 0) = true := by
  unfold AllSites; decide +kernel

omit hub in
/-- A block state's place. -/
theorem blk_plc {d : D} {n : Cls → Nat} {o : Blk}
    (hσ : Frame.stateAt (thread p L) X g k = some (some (LdWarp.linj p L g b d n)))
    (hub0 : n .ub = 0) (hRd : RoundsB (bc d.site) (inBlk d.site) d.v (n (.load .commit)))
    (ho : bc d.site = some o) (htm : b = true → isT d.site = false) :
    ∃ x, Plc (w0 d.v.su.r28) (decide (Last d.v)) (pkts d.v.su.r28) x o ∧
      els X g k + 32 * n (.load .commit) + pktSh d.site =
        plcN b (w0 d.v.su.r28) (decide (Last d.v)) x d.site ∧
      (o = .prime → x = 0) ∧ (o ≠ .prime → 1 ≤ x ∧
        n (.load .commit) = 2 + 2 * (x - 1) + inBlk d.site) := by
  have hB : ∀ T, (Prologue.warpIndex L g = 14 → els X g k = T) → els X g k = if b then 0 else T :=
    fun T h => ld_els hp hX hg hw hσ hub0 h
  have hL := fun h14 => ld_els_blk hp hX hg h14 hσ hub0 rfl
  have hw0 : 2 ≤ sv d.v.su.r28 → w0 d.v.su.r28 = wRn d.v.su.r28 := fun h => by
    unfold w0; rw [ite_eq_right (by omega)]
  rw [ho] at hRd
  cases o with
  | prime =>
    have hE := hB _ (fun h14 => (hL h14).1 ho)
    simp only [RoundsB] at hRd
    refine ⟨0, rfl, ?_, fun _ => rfl, fun h => absurd rfl h⟩
    rw [hE, hRd, plcN_prime, loc]
    omega
  | warm =>
    obtain ⟨r, -, h2, hr, hnc⟩ := hRd
    have hE := hB _ (fun h14 => (hL h14).2.1 (.inl ho) r hnc)
    rw [← hw0 h2] at hr
    refine ⟨r + 1, ⟨Nat.succ_pos r, hr⟩, ?_, (fun h => by cases h), fun _ => ⟨Nat.succ_pos r, hnc⟩⟩
    rw [hE, hnc, plcN_warm (by rw [ho]; simp) hr.le, loc]
    clear * -
    cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
  | tma6 =>
    obtain ⟨-, h2, hnc⟩ := hRd
    have hT := ((off_bound d.site).2.2.1 ho).2
    cases b with
    | true => rw [htm rfl] at hT; cases hT
    | false =>
      have hE := hB _ (fun h14 => (hL h14).2.1 (.inr ho) _ hnc)
      have hlast : Last d.v := (bias_num hp hX hg hw hσ hub0 false).2.2.1 (tma6_last ho)
      rw [← hw0 h2] at hnc hE
      refine ⟨w0 d.v.su.r28 + 1, ⟨rfl, by simpa using hlast⟩, ?_, (fun h => by cases h),
        fun _ => ⟨Nat.succ_pos _, hnc⟩⟩
      rw [hE, hnc, plcN_warm (by rw [ho]; simp) le_rfl, loc]
      clear * -
      simp only [Bool.false_eq_true, ite_false]
      omega
  | steady =>
    obtain ⟨r, -, h1, h2, hnc⟩ := hRd
    have hz : n (.load .commit) ≠ 0 := by
      rw [hnc]
      clear * -
      generalize w0 d.v.su.r28 = W
      generalize r - wRn d.v.su.r28 = y
      omega
    have hE := hB _ (fun h14 => (hL h14).2.2 ho hz)
    obtain ⟨-, -, -, hob⟩ := off_bound d.site
    have hT := (hob ho).2
    have hbl : blkEl d.site = 0 := by
      have := steady_el.ok d.site
      simpa [ho] using this
    obtain ⟨z, hz⟩ : ∃ z, z = sv (Flow.Arith32.addi d.v.su.r28 (-1)) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = wRn d.v.su.r28 := ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = r - wRn d.v.su.r28 := ⟨_, rfl⟩
    rw [← hz] at h2
    rw [← hq] at h1 hy
    rw [← hq, ← hy] at hnc
    have hpk : 2 * (w0 d.v.su.r28 + y + 1) + 2 ≤ pkts d.v.su.r28 := by
      unfold pkts
      rw [← hz, ← hq]
      generalize w0 d.v.su.r28 = W
      clear * - h1 h2 hy
      omega
    refine ⟨w0 d.v.su.r28 + y + 1, ⟨Nat.succ_le_succ (Nat.le_add_right _ _), hpk⟩, ?_,
      (fun h => by cases h),
      fun _ => ⟨Nat.succ_pos _, ?_⟩⟩
    · rw [hE, hnc, plcN_steady ho, loc, hbl, totEl]
      generalize w0 d.v.su.r28 = W
      by_cases hl : Last d.v
      · simp only [hl, decide_true, ite_true]
        clear * -
        cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
      · simp only [hl, decide_false, Bool.false_eq_true, ite_false]
        clear * -
        cases b <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
    · rw [hnc]
      clear * -
      generalize w0 d.v.su.r28 = W
      omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
