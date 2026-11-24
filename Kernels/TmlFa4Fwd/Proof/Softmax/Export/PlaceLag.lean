-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Place
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Lib.ThreadTime
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A softmax lane short of a counted event is early

`soft_place_lag`: a softmax lane of a tile that has made no more events of a class than a state at
a place of the tile has passed has not exited and is no later than any time that bounds the states
up to the place. `soft_round_time` and `soft_time_lt` bound them at a round site. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before allSites mem_allSites Reg ordK
  val valT sm)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- A state of a softmax lane with its place in the tile. -/
structure SoftAt (p : Params) (L : Launch) (g B P : Nat) (d : Softmax.D) (n : Cls → Nat)
    (rb rp : Nat) : Prop where
  shfl : 3 ≤ n .shfl
  cnt : ∀ c, c.pointed = true → n (.soft c) = passed (ptsOf (Softmax.lz L g) c) d.site rb rp
  wait : ∀ c, d.site = .sldw c → d.k = 1
  fits : SmWarp.SFits p L g d (n .shfl) (n .vote)
  reg : Reg B P d.site rb rp
  tile : d.site.noTile = false

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) (hw : Prologue.warpIndex L g < 8)
  {B P : Nat} (hT : SoftTile p L g B P)
include hp hX hFw hub hg hw hT

/-- **A lane with no more events of a class than a place has passed** has not exited and is no later
than a bound of the states up to the place. -/
theorem soft_place_lag (f : Event → Bool) (pts : List Nat) (ex : Softmax.D → Nat)
    (hcnt : ∀ {k d n rb rp}, Frame.stateAt (thread p L) X g k =
        some (some (SmWarp.sinj p L g d n)) → k ≤ (X.tr g).length → SoftAt p L g B P d.scheduler n
            rb rp →
      ((X.tr g).take k).countP f = passed pts d.scheduler.site rb rp + ex d.scheduler)
    {s0 : Softmax.Site} {rb0 rp0 e0 T : Nat} (hR0 : Reg B P s0 rb0 rp0) (hn0 : s0.noTile = false)
    (he0 : e0 < pts.countP (· = s0.pos)) (hx0 : ∀ l, s0 ≠ .exit l)
    (hle : (X.tr g).countP f ≤ passed pts s0 rb0 rp0 + e0) (hT0 : Progress.scanBase ≤ T)
    (hfe : ∀ {k d n e}, Frame.stateAt (thread p L) X g k = some (some (SmWarp.sinj p L g d n)) →
      X.get (g, k) = some e → Softmax.Ev p L g d.scheduler e → d.scheduler.site = s0 → ex
          d.scheduler = e0 → f e = true)
    (hlt : ∀ {d n rb rp}, SoftAt p L g B P d n rb rp → ordK d.site rb rp < ordK s0 rb0 rp0 →
      Progress.Sm.time p L g d n < T)
    (heq : ∀ {d n}, SoftAt p L g B P d n rb0 rp0 → d.site = s0 → ex d ≤ e0 →
      Progress.Sm.time p L g d n ≤ T ∧ (ex d < e0 → Progress.Sm.time p L g d n < T)) :
    (∀ j pc, X.get (g, j) ≠ some ⟨pc, .exit⟩) ∧
      Sched.threadTime (Progress.timed p L) X g ≤ T := by
  have hne : ∀ {j e}, X.get (g, j) = some e → ∀ f, e.kind ≠ .ub f := fun {j e} he f hf =>
    hub ⟨(g, j), e.pc, f, by rw [he]; obtain ⟨pc, kd⟩ := e; simp only at hf; rw [hf]⟩
  have hk : ∀ k, ((X.tr g).take k).countP f ≤ passed pts s0 rb0 rp0 + e0 := fun k =>
    le_trans (List.take_sublist _ _).countP_le hle
  -- the place of a state
  have key : ∀ {k d n rb rp}, Frame.stateAt (thread p L) X g k =
      some (some (SmWarp.sinj p L g d n)) → k ≤ (X.tr g).length → SoftAt p L g B P d.scheduler n rb
          rp →
      ordK d.scheduler.site rb rp < ordK s0 rb0 rp0 ∨ (d.scheduler.site = s0 ∧ rb = rb0 ∧ rp = rp0 ∧
          ex d.scheduler ≤ e0) := by
    intro k d n rb rp hσ hkl hA
    have h1 := hcnt hσ hkl hA
    have h2 := hk k
    rcases Nat.lt_trichotomy (ordK d.scheduler.site rb rp) (ordK s0 rb0 rp0) with h | h | h
    · exact .inl h
    · right
      obtain ⟨e1, rfl, rfl⟩ := Softmax.ordK_eq hA.reg hR0 h
      have e2 := Softmax.pos_inj e1 (hA.tile.trans hn0.symm)
      rw [e2] at h1
      exact ⟨e2, rfl, rfl, by omega⟩
    · have := Softmax.passed_lt hR0 hA.reg hn0 hA.tile h pts
      omega
  have place : ∀ {k σ}, Frame.stateAt (thread p L) X g k = some (some σ) →
      (Progress.time p L g σ < T ∧ ∃ s n, σ = (.inl s, n)) ∨
        ∃ d n rb rp, σ = SmWarp.sinj p L g d n ∧ SoftAt p L g B P d.scheduler n rb rp := by
    intro k σ hσ
    rcases soft_place hp hX hFw hub hg hw hσ with ⟨h1, s, n, h2, -⟩ |
      ⟨d, n, rb, rp, rfl, -, h3, hc, hwt, hF, hreg, -⟩
    · exact .inl ⟨by omega, s, n, h2⟩
    · obtain ⟨hr, ht⟩ := hreg B P hT
      exact .inr ⟨d, n, rb, rp, rfl, h3, hc, hwt, hF, hr, ht⟩
  constructor
  · intro j pc hx
    have hjl := (List.getElem?_eq_some_iff.mp (show (X.tr g)[j]? = _ from hx)).1
    rcases SmWarp.open_ev hp hX hFw hw hx (hne hx) with ⟨s, n, -, -, -, hi, hev⟩ |
      ⟨d, n, hσ, h0, hR, -, hev⟩
    · have hx : exit L g s = none := hi.2
      obtain ⟨site, x1, x2, x3⟩ := s
      cases site with
      | sh j => fin_cases j <;> simp [Startup.Ev] at hev
      | elect j => simp [Startup.Ev] at hev
      | init q => simp [Startup.Ev] at hev
      | fence => simp [Startup.Ev] at hev
      | bar => simp [Startup.Ev] at hev
      | enter r => simp [exit] at hx
    · obtain ⟨l, hs⟩ := soft_exit_site hev.1
      rcases place hσ with ⟨-, s, n', h⟩ | ⟨d', n', rb, rp, h, hA⟩
      · cases h
      · cases h
        have hl : l = true := by
          have := hA.tile
          rw [hs] at this
          cases l
          · cases this
          · rfl
        subst hl
        have hp0 := Softmax.pos_exit hx0
        have hr := hA.reg
        rw [hs] at hr
        have hpe : (Softmax.Site.exit true).pos = 18410 := rfl
        rcases key hσ hjl.le hA with h | ⟨h, -⟩
        · rw [hs] at h
          unfold ordK at h
          unfold Reg at hr hR0
          rw [hpe] at h hr
          omega
        · exact hx0 true (by rw [← h, hs])
  · refine threadTime_le (fun σ hσ => ?_) fun σ e hσ he => ?_
    · rcases place hσ with ⟨h, -⟩ | ⟨d, n, rb, rp, rfl, hA⟩
      · exact h.le
      · rcases key hσ le_rfl hA with h | ⟨h, rfl, rfl, h'⟩
        · exact (hlt hA h).le
        · exact (heq hA h h').1
    · rcases place hσ with ⟨h, -⟩ | ⟨d, n, rb, rp, rfl, hA⟩
      · exact h
      · have hjl := (List.getElem?_eq_some_iff.mp
          (show (X.tr g)[(X.tr g).length - 1]? = _ from he)).1
        rcases key hσ (by omega) hA with h | ⟨h, rfl, rfl, h'⟩
        · exact hlt hA h
        · rcases Nat.lt_or_ge (ex d.scheduler) e0 with h0 | h0
          · exact (heq hA h h').2 h0
          exfalso
          have hev : Softmax.Ev p L g d.scheduler e := by
            rcases SmWarp.open_ev hp hX hFw hw he (hne he) with ⟨s, n', hσ', -⟩ |
              ⟨d', n', hσ', -, -, -, hev⟩
            · rw [hσ] at hσ'; cases hσ'
            · rw [hσ] at hσ'; cases hσ'; exact hev.1
          have hf := hfe hσ he hev h (by omega)
          have h1 := hcnt hσ (by omega) hA
          have h2 : ((X.tr g).take ((X.tr g).length - 1)).countP f < (X.tr g).countP f :=
            Frame.countP_take_lt_countP (P := f) (es := X.tr g) he hf
          rw [h] at h1
          omega

end

/-- **The time of a state at a round site.** -/
theorem soft_round_time {B P : Nat} {d : Softmax.D} {n : Cls → Nat} {rb rp : Nat}
    (hA : SoftAt p L g B P d n rb rp) {a : Nat × Nat}
    (ha : val (Progress.Sm.stage L g) d.site = some a) :
    Progress.Sm.time p L g d n ≤ valT p (rb + rp) a + Progress.Sm.subOff d ∧
      (1 + B + P ≤ Progress.bmax p →
        Progress.Sm.time p L g d n = valT p (rb + rp) a + Progress.Sm.subOff d) := by
  have hst : Progress.Sm.stage L g < 2 := by unfold Progress.Sm.stage; split <;> omega
  obtain ⟨bd, past, o, hpl, h1, h2, h3⟩ := Softmax.slot_of hst ha hA.reg (Softmax.lz L g)
  have hn := hA.cnt (.acquire 80) rfl
  have ht : Progress.Sm.time p L g d n = Progress.clk p
      (Progress.slotOf p (rb + rp + a.1)) (a.2 + Progress.Sm.subOff d) := by
    simp only [Progress.Sm.time, hpl, hn, h2, h1]
  have hm := Nat.mul_le_mul_left 4096
    (show Progress.slotOf p (rb + rp + a.1) ≤ rb + rp + a.1 from Nat.min_le_left _ _)
  rw [ht]
  refine ⟨?_, fun hb => ?_⟩
  · unfold Progress.clk valT Progress.span
    omega
  · rw [Progress.slotOf_eq (by omega)]
    unfold Progress.clk valT Progress.span
    omega

private def preChk (st : Nat) (s : Softmax.Site) : Bool :=
  (val st s).isSome || decide (15232 < s.pos) || (!Progress.Sm.late s &&
    decide ((SmWarp.epi s).late = false) && decide (s.pos < 10064) &&
      (Progress.Sm.endOff s).isNone && (match Progress.Sm.pre s with
        | some o => decide (o ≤ 3) | none => true))

private theorem pre_chk : [0, 1].all (fun st => allSites.all (preChk st)) = true := by
  decide +kernel

/-- **A state before a round site** is earlier than the site's time. -/
theorem soft_time_lt (hp : Pre p L m) {B P : Nat} {d : Softmax.D} {n : Cls → Nat}
    {rb rp rb' rp' : Nat} (hA : SoftAt p L g B P d n rb rp) {s : Softmax.Site} {a : Nat × Nat}
    (ha : val (Progress.Sm.stage L g) s = some a) (hR : Reg B P s rb' rp')
    (hs : s.pos ≤ 15232) (hK : ordK d.site rb rp < ordK s rb' rp') :
    Progress.Sm.time p L g d n < valT p (rb' + rp') a := by
  have hst : Progress.Sm.stage L g < 2 := by unfold Progress.Sm.stage; split <;> omega
  have hsub : Progress.Sm.subOff d ≤ sm d.site := by
    unfold Progress.Sm.subOff sm
    split <;> simp_all
  cases hv : val (Progress.Sm.stage L g) d.site with
  | some b =>
    have h1 := (soft_round_time hA hv).1
    have h2 := Softmax.val_lt hst hv ha hA.reg hR hK p
    omega
  | none =>
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp pre_chk (Progress.Sm.stage L g) (by
      rcases show Progress.Sm.stage L g = 0 ∨ Progress.Sm.stage L g = 1 by omega with h | h <;>
        simp [h])) d.site (mem_allSites _)
    simp only [preChk, hv, Option.isSome_none, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, Bool.not_eq_true', Option.isNone_iff_eq_none] at hchk
    rcases hchk with h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · exfalso
      have hr := hA.reg
      have := hA.tile
      unfold ordK at hK
      unfold Reg at hr hR
      omega
    · have hpl : Progress.Sm.place (Progress.Sm.stage L g) d.site = none := by
        unfold val at hv
        split at hv
        · cases hv
        · assumption
      have hpb : Progress.primeBase p + 1024 ≤ valT p (rb' + rp') a := by
        unfold valT Progress.pipeBase; omega
      have hprv : Progress.primeBase p = Progress.scanBase + 2 * Progress.cmax p + 4 := rfl
      simp only [Progress.Sm.time, hpl, h4]
      split
      · rename_i o ho
        rw [ho] at h5
        simp only [decide_eq_true_eq] at h5
        omega
      · simp only [h1, Bool.false_eq_true, ite_false]
        split_ifs
        · omega
        · omega
        · have h6 := Epilogue.fits_coll_le hp hA.fits.1 h2
          have h7 : Progress.Out.ballots (Progress.Sm.toE d.site) ≤ 1 := by
            unfold Progress.Out.ballots; split <;> omega
          have h8 := Progress.pass_lt_prime (p := p)
            (c := n .shfl + Progress.Out.ballots (Progress.Sm.toE d.site))
            (by unfold Progress.cmax; omega) (Progress.Out.coll (Progress.Sm.toE d.site))
          exact lt_of_lt_of_le h8 (by omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof
