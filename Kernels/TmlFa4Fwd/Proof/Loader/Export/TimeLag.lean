-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Frame
public import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QGroup
public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
public import Kernels.TmlFa4Fwd.Proof.Loader.Move
public import Kernels.TmlFa4Fwd.Proof.Loader.Ref
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Parity
import Kernels.TmlFa4Fwd.Proof.Loader.Export.ArrRing
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A loader lane short of a packet is early

`ld_early`: a lane of warps 14 and 15 of a CTA that picked a tile, with no more arrive-ons on the
full barrier of packet `i`'s ring slot than packets before `i` in that slot, is before `Ld.bound p
i` in the time table. With `Ld.bound_le` that is before the MMA warp's poll of ring index `i`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A site of the tile's loads is of the first block or of the pipeline. -/
theorem blk_prime_pipe {s : Site} (h : s.blk = true) :
    Progress.Ld.prime s = true ∨ Progress.Ld.pipe s = true := by
  cases s <;> simp only [Site.blk, bc, Option.isSome_none, Bool.false_eq_true] at h
  case tw t | te t _ | ta t | tc t _ =>
    simp only [Progress.Ld.prime, Progress.Ld.pipe, decide_eq_true_eq]; omega
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | commit per _
    | arrive per _ | ptP per _ _ | ptR per _ _ | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _
    | cp per _ _ _ =>
    cases per <;> simp [Progress.Ld.prime, Progress.Ld.pipe]

/-- A lane that returns after the first pass picked no tile. -/
theorem noPick {d : Epilogue.D} {ns nv : Nat}
    (hF : Epilogue.Fits p L g { d with site := .exit false } ns nv) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) : False := by
  simp only [Epilogue.Fits, Epilogue.Fits.ExitAt] at hF
  obtain ⟨n0, v0, -, R', hE, h⟩ := hF
  obtain rfl := hE.unique hP.1
  rcases h with ⟨h, -⟩ | ⟨bal', hB, -, -, -, hN⟩
  · rw [hP.2.2.1] at h; cases h
  · obtain rfl := hB.unique hP.2.1
    exact hN trivial hP

/-- The packet of a state's time is its published packets. -/
theorem idx_eq (s : Site) (n : Cls → Nat) :
    Progress.Ld.idx s n = n (.load .commit) - (inPkt s).2 := by
  cases s <;> simp [Progress.Ld.idx, inPkt]

/-- A pipeline state has published the first block's two packets. -/
theorem pipe_two {w : Nat} {dn : D × (Cnt → Nat)} (hR : Ref p L g w dn)
    (h : Progress.Ld.pipe dn.1.site = true) : 2 ≤ dn.2 .commit - (inPkt dn.1.site).2 := by
  have hc := hR.commit
  have hw := hR.words
  obtain ⟨⟨s, v, k⟩, n⟩ := dn
  generalize posK (⟨s, v, k⟩, n) = kk at hc hw
  generalize posA (⟨s, v, k⟩, n) = A at hc hw
  have h2 : 2 ≤ kk → 2 ≤ arrAt s kk A := by
    intro hk
    cases s <;> simp only [Progress.Ld.pipe, Bool.false_eq_true, decide_eq_true_eq] at h
    case tw t | te t _ | ta t | tc t _ =>
      simp only [arrAt, tmaPk]; split_ifs <;> omega
    case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | commit per _
      | arrive per _ | ptP per _ _ | ptR per _ _ | ptS per _ _ | lw per _ _ | xl per _ _
      | xh per _ _ | cp per _ _ _ =>
      cases per <;> simp at h <;> simp only [arrAt, pkOf] <;> (try split_ifs) <;>
        omega
  have hk : 2 ≤ kk := by
    cases s <;> simp only [Progress.Ld.pipe, Bool.false_eq_true, decide_eq_true_eq] at h
    case tw t | te t _ | ta t | tc t _ =>
      have h4 : ¬ t.val < 4 := by omega
      simp only [ringCls, h4, ↓reduceIte] at hw
      split at hw <;> simp only [RingWords] at hw <;> first | exact hw.2 | exact hw.1.2
    case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | commit per _
      | arrive per _ | ptP per _ _ | ptR per _ _ | ptS per _ _ | lw per _ _ | xl per _ _
      | xh per _ _ | cp per _ _ _ =>
      cases per <;> simp at h <;> simp only [ringCls, RingWords] at hw <;>
        first | exact hw.2 | exact hw.1.2
  have := h2 hk
  simp only at hc ⊢
  omega

/-- **A loader state that has published at most `i` packets**, `i` less than the tile's, is more
than one before `Ld.bound p i`. -/
theorem state_early (hp : Pre p L m) {d : D} {n : Cls → Nat} {w : Nat}
    (hR : Ref p L g w (d, LdWarp.lcn n))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit))) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) {i : Nat} (hi : i < pkts (r28Ref p L g R bal))
    (hc : n (.load .commit) - (inPkt d.site).2 ≤ i) :
    Progress.Ld.time p d n + 1 < Progress.Ld.bound p i := by
  have hb := Progress.Ld.pipeBase_le_bound p i
  have hpb : Progress.primeBase p + 1024 = Progress.pipeBase p := rfl
  have hsp := Progress.scanBase_le_primeBase p
  have pass : ∀ s : Site, d.site = s → Progress.Ld.late s = false → lc s = .p1 →
      Progress.passTime Progress.scanBase (n .shfl - 32 * n (.load .commit) +
        Progress.Out.ballots (Progress.Ld.toE s)) (Progress.Out.coll (Progress.Ld.toE s)) + 1 <
        Progress.Ld.bound p i := by
    intro s hs hl hlc
    subst hs
    simp only [LFits, hlc] at hF
    have h1 := Epilogue.fits_coll_le hp hF.2 (by
      obtain ⟨s, v, k⟩ := d
      cases s <;> simp_all [Progress.Ld.late, toE, Site.epi, Epilogue.Site.late, lc])
    have h2 : Progress.Out.ballots (Progress.Ld.toE d.site) ≤ 1 := by
      unfold Progress.Out.ballots; split <;> omega
    have := Progress.pass_lt_prime (p := p) (c := n .shfl - 32 * n (.load .commit) +
      Progress.Out.ballots (Progress.Ld.toE d.site)) (by unfold Progress.cmax; omega)
      (Progress.Out.coll (Progress.Ld.toE d.site))
    omega
  have all : (SuRef p L g d.v ∧ n (.load .commit) = pkts d.v.su.r28) → (inPkt d.site).2 = 0 →
      False := by
    rintro ⟨⟨R', bal', hP', hr⟩, hn⟩ h0
    obtain ⟨rfl, rfl⟩ := hP'.unique hP
    rw [hr] at hn
    omega
  cases hlc : lc d.site with
  | blk =>
    rcases blk_prime_pipe (lc_blk.mp hlc) with h | h
    · have := Progress.Ld.time_prime (p := p) (d := d) (n := n) h; omega
    · refine Progress.Ld.time_pipe h ?_ ?_ <;> rw [idx_eq]
      · exact pipe_two hR h
      · exact hc
  | drain =>
    exfalso
    simp only [LFits, hlc] at hF
    obtain ⟨l, -, hFE, h1, -⟩ := hF
    cases l
    · exact noPick hFE hP
    · refine all (h1 rfl) ?_
      obtain ⟨s, v, k⟩ := d
      cases s <;> simp_all [lc, inPkt]
  | p2 =>
    exfalso
    simp only [LFits, hlc] at hF
    refine all hF.2.2 ?_
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp_all [lc, inPkt]
  | early =>
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp only [lc, reduceCtorEq] at hlc
    case setmax => simp only [Progress.Ld.time]; omega
    all_goals (try split at hlc) <;> cases hlc
  | req =>
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp only [lc, reduceCtorEq] at hlc
    case q0 | q1 | uk => simp only [Progress.Ld.time]; omega
    all_goals (try split at hlc) <;> cases hlc
  | p1 =>
    obtain ⟨s, v, k⟩ := d
    cases s <;> simp only [lc, reduceCtorEq] at hlc
    case word k | down k | total k | up k j =>
      have hl : k.late = false := by split at hlc <;> simp_all
      have := pass _ rfl (by simp [Progress.Ld.late, hl]) (by simp [lc, hl])
      simpa [Progress.Ld.time, Progress.Ld.late, hl] using this
    case vote l | pre l | tiles l =>
      have hl : l = false := by split at hlc <;> simp_all
      subst hl
      have := pass _ rfl rfl rfl
      simpa [Progress.Ld.time, Progress.Ld.late] using this

/-- The occurrences of packet `i`'s slot among more packets than `i` are more than those before
it. -/
theorem le_of_ringCnt {c i : Nat} (h : ringCnt c (i % 3) ≤ i / 3) : c ≤ i := by
  rw [ringCnt_eq c _ (Nat.mod_lt _ (by decide))] at h
  split_ifs at h <;> omega

/-- A state before the end of the first four TMA groups has published at most one packet. -/
theorem ppos_one {w : Nat} {dn : D × (Cnt → Nat)} (hR : Ref p L g w dn)
    (h : ppos (decide (dn.2 .commit = 0)) dn.1.site < 1000) :
    dn.2 .commit - (inPkt dn.1.site).2 ≤ 1 := by
  by_cases hz : dn.2 .commit = 0
  · omega
  have hc := hR.commit
  obtain ⟨⟨s, v, k⟩, n⟩ := dn
  generalize posK (⟨s, v, k⟩, n) = kk at hc
  generalize posA (⟨s, v, k⟩, n) = A at hc
  simp only at hc hz h ⊢
  rw [decide_eq_false hz] at h
  have h1 : arrAt s kk A ≤ 1 := by
    cases s <;> simp only [ppos, Bool.false_eq_true, ↓reduceIte] at h
    case tw t | te t _ | ta t | tc t _ =>
      have ht : t.val < 4 := by
        by_contra h4
        rw [ite_eq_right h4] at h; omega
      simp only [arrAt, tmaPk]
      split_ifs
      all_goals omega
    case pgLd per _ | pgSt per _ | rwSt per _ =>
      cases per <;> simp at h
      simp [arrAt, pkOf]
    case slot per v' | commit per v' | arrive per v' | ptP per v' _ | ptR per v' _ | ptS per v' _
      | lw per v' _ | xl per v' _ | xh per v' _ | cp per v' _ _ =>
      cases per <;> cases v' <;> simp at h
      simp [arrAt, pkOf]
    all_goals omega
  omega

theorem pkts_two (b : BitVec 64) : 2 ≤ pkts b := by
  unfold pkts; omega

/-- **The followed states of a loader lane** of a safe execution. -/
theorem lane_cases (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {k : Nat}
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Progress.time p L g σ + 1 < Progress.primeBase p ∨
      ∃ b d n, σ = LdWarp.linj p L g b d n ∧ n .ub = 0 ∧
        Ref p L g (Prologue.warpIndex L g) (d, LdWarp.lcn n) ∧
        LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) := by
  have hsp := Progress.scanBase_le_primeBase p
  have hR := (LdWarp.good hp hX hw hg rfl k).2 σ hσ
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i', d⟩
  · have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hR.1
      simp only [StartAt, he] at h1
    have := Progress.startTime_lt hx
    have h2 : Progress.scanBase + 4 ≤ Progress.primeBase p := by
      unfold Progress.primeBase; omega
    exact .inl (by simp only [Progress.time]; omega)
  cases i' with
  | loader b =>
    have hub0 : n .ub = 0 := by
      by_contra h
      obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
      cases kind <;> simp [Proof.cls] at hk
      exact hub ⟨(g, j), pc, _, hf⟩
    exact .inr ⟨b, d, n, rfl, hub0, hR.2 hub0⟩
  | _ => exact hR.elim

/-- **A state of a loader lane is early, with a tile picked, or past the first TMA groups.** -/
theorem group_early (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) {k : Nat}
    {σ : (thread p L g).D} (hσ : Frame.stateAt (thread p L) X g k = some (some σ)) :
    Progress.time p L g σ + 1 < Progress.pipeBase p ∨
      ∃ b d n, σ = LdWarp.linj p L g b d n ∧ n .ub = 0 ∧
        1000 ≤ ppos (decide (n (.load .commit) = 0)) d.site := by
  rcases lane_cases hp hX hub hg hw hσ with h | ⟨b, d, n, rfl, hub0, hJ, hF⟩
  · exact .inl (by unfold Progress.pipeBase; omega)
  by_cases h : ppos (decide (n (.load .commit) = 0)) d.site < 1000
  · exact .inl (state_early hp hJ hF hP (i := 1) (by have := pkts_two (r28Ref p L g R bal); omega)
      (ppos_one hJ h))
  · exact .inr ⟨b, d, n, rfl, hub0, by omega⟩

/-- The state of a loader lane's exit is at the end of the time table. -/
theorem exit_late (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {k pc : Nat} (hx : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ σ, Frame.stateAt (thread p L) X g k = some (some σ) ∧
      Progress.pipeBase p ≤ Progress.time p L g σ := by
  obtain ⟨σ, hσ, hJ⟩ := good_state hp hX hx (by intro _ _ h; cases h)
    (LdWarp.good hp hX hw hg rfl k)
  refine ⟨σ, hσ, ?_⟩
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · exfalso
    obtain ⟨hev, hx, -⟩ := start_fired hp hX hx hσ
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  cases i with
  | loader b =>
    have hev := (LdWarp.lfired hp hX hx hσ).1
    obtain ⟨site, v, kk⟩ := d
    cases site
    case exit =>
      have h1 : Progress.pipeBase p ≤ Progress.doneBase p := by
        unfold Progress.doneBase Progress.endBase Progress.tailBase Progress.clk; omega
      simp only [Progress.time, Progress.roleTime, Progress.Ld.time]
      omega
    all_goals exfalso
    all_goals simp only [Loader.Ev, Epilogue.Ev, Loader.Site.toE] at hev
    all_goals simp at hev
  | _ => exact hJ.elim

/-- **A loader lane short of packet `i` is early.** -/
theorem ld_early (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hub : ¬ HasUb X) (hg : g < L.threads)
    (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {R : Nat} {bal : BitVec 64}
    (hP : Epilogue.Picked p L g R bal) {i : Nat} (hi : i < pkts (r28Ref p L g R bal))
    (hc : (X.tr g).countP (cls L g (.asyncArrive (bl L g (32 + 8 * (i % 3))))) ≤ i / 3) :
    Sched.threadTime (Progress.timed p L) X g < Progress.Ld.bound p i := by
  have hb := Progress.Ld.pipeBase_le_bound p i
  have hpb : Progress.primeBase p + 1024 = Progress.pipeBase p := rfl
  have hle : ∀ k σ, Frame.stateAt (thread p L) X g k = some (some σ) →
      Progress.time p L g σ + 1 < Progress.Ld.bound p i := by
    intro k σ hσ
    rcases lane_cases hp hX hub hg hw hσ with h | ⟨b, d, n, rfl, hub0, hJ, hF⟩
    · omega
    refine state_early hp hJ hF hP hi (le_of_ringCnt ?_)
    have ha := Loader.arr_ring hp hX hg hw hσ hub0 ⟨i % 3, Nat.mod_lt _ (by decide)⟩
    simp only [LdWarp.lcn] at ha
    rw [← ha, ← count hσ]
    exact le_trans (List.take_sublist _ _).countP_le hc
  unfold Sched.threadTime
  split
  · rename_i d hd; have := hle _ _ hd; simp only [Progress.timed]; omega
  · omega
  · split
    · rename_i d hd; exact hle _ _ hd
    · omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
