-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.CollPos
import Kernels.TmlFa4Fwd.Proof.Lib.RoundsBound
import Kernels.TmlFa4Fwd.Proof.Protocol.Soft.Blk
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A state of the softmax rounds among its warp's collectives -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Progress (clk slotOf bandP primeBase endBase scanBase bmax
  passTime)
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain preR finR
  allSites mem_allSites)

namespace SoftColl
noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The P-full arrivals and the S-full polls of the current pass before a site. -/
def cA (b : Bool) (s : Softmax.Site) : Nat := (ptsOf b (.arrive 96)).countP (before s)
def cB (b : Bool) (s : Softmax.Site) : Nat := (ptsOf b (.acquire 80)).countP (before s)

/-- The round site check. -/
def rsChk (b : Bool) (s : Softmax.Site) : Bool :=
  [0, 1].all fun st => match Progress.Sm.place st s with
    | none => !s.rcoll && s.rem == 0
    | some (bd, past, o) =>
      let pb := if past then 1 else 0
      (SmWarp.epi s == .ready 0) && s.hasUk && decide (bd + o + 1 < Progress.span) &&
      decide (pb ≤ cB b s) && decide (s.rem / 2 ≤ cA b s) &&
      (if s.rcoll then
        cA b s == cB b s && past && bd == bandP st && ((preR s && cA b s == 1 &&
          (s == .pws .first && o == 18 || s == .pel .first && o == 20)) ||
        (inBias s.pos && cA b s == 2 && (s == .pws .bias && o == 18 || s == .pel .bias && o == 20))
        || (inPlain s.pos && cA b s == 2 &&
          (s == .pws .plain && o == 18 || s == .pel .plain && o == 20)))
      else (s.rem == 0 || s.rem == 2) &&
        (decide (cB b s - pb < cA b s - s.rem / 2) ||
          (cB b s - pb == cA b s - s.rem / 2 && decide (bd + o + 1 < bandP st + 18))) &&
        ((preR s && decide (cA b s - s.rem / 2 ≤ 1)) ||
          (inBias s.pos && decide (cA b s - s.rem / 2 ≤ 2)) ||
          (inPlain s.pos && decide (cA b s - s.rem / 2 ≤ 2)) ||
          (finR s && decide (cA b s - s.rem / 2 ≤ 1))))

theorem rs_chk : [false, true].all (fun b => allSites.all (rsChk b)) = true := by
  decide +kernel

theorem rs_ok (b : Bool) (s : Softmax.Site) : rsChk b s = true :=
  List.all_eq_true.mp (List.all_eq_true.mp rs_chk b (by cases b <;> simp)) s (mem_allSites s)

theorem rnd2 (b : Bool) : (ptsOf b (.acquire 80)).countP inBias = 1 ∧
    (ptsOf b (.acquire 80)).countP inPlain = 1 ∧ (ptsOf b (.arrive 96)).countP inBias = 1 ∧
      (ptsOf b (.arrive 96)).countP inPlain = 1 := by
  cases b <;> decide +kernel

theorem done_nat {r : Nat} {n : Int} (h : Softmax.Done r n) : n.toNat = r := by
  rcases h with h | ⟨rfl, h⟩ <;> omega

/-- The regions' rounds: the rounds done are the tile's, and a state's round is one of them. -/
theorem region {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp : Nat}
    (hQ : RefQ p L g d c rb rp) : let nb := (Softmax.nB p L g d.v).toNat
    let T := 1 + nb + (Softmax.nP p L g d.v).toNat
    (preR d.site = true → rb + rp = 0 ∧ 1 ≤ T) ∧
    (inBias d.site.pos = true → rp = 0 ∧ 1 + rb < 1 + nb ∧ 2 + rb + rp ≤ T) ∧
    (inPlain d.site.pos = true → rb = nb ∧ 2 + rb + rp ≤ T) ∧
    (finR d.site = true → 1 + rb + rp = T) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hQ.pre h
    omega
  · obtain ⟨rfl, -, h1, -⟩ := hQ.bias h
    omega
  · obtain ⟨-, h1, -, hd⟩ := hQ.plain h
    have := done_nat hd
    omega
  · obtain ⟨h1, h2⟩ := hQ.fin h
    have := done_nat h1
    have := done_nat h2
    omega

/-- **A state of the rounds.** -/
theorem round_M {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp st : Nat} {a : SoftRun}
    {n : Cls → Nat} (hQ : RefQ p L g d c rb rp) (hst : st = Progress.Sm.stage L g)
    (ha : a.nb = (Softmax.nB p L g d.v).toNat)
    (haT : a.T = 1 + a.nb + (Softmax.nP p L g d.v).toNat) (hT : a.T ≤ bmax p)
    (h80 : n (.soft (.acquire 80)) = c (.acquire 80))
    {x : Nat × Bool × Nat} (hpl : Progress.Sm.place st d.site = some x) {E : Nat}
    (hE : E + d.site.rem = 2 * c (.arrive 96)) :
    SoftM p st a (a.ch + E) (Progress.Sm.time p L g d n)
      (if d.site.rcoll then some d.site else none) := by
  obtain ⟨bd, past, o⟩ := x
  have hst2 : st ∈ [0, 1] := by
    rw [hst]; unfold Progress.Sm.stage; split <;> simp
  have hck := List.all_eq_true.mp (rs_ok (Softmax.lz L g) d.site) st hst2
  rw [hpl] at hck
  have hA := hQ.cnt (.arrive 96) rfl
  have hB := hQ.cnt (.acquire 80) rfl
  obtain ⟨t1, t2, t3, t4⟩ := rnd2 (Softmax.lz L g)
  simp only [passed, t1, t2, t3, t4, Nat.mul_one] at hA hB
  change c (.arrive 96) = cA (Softmax.lz L g) d.site + rb + rp at hA
  change c (.acquire 80) = cB (Softmax.lz L g) d.site + rb + rp at hB
  obtain ⟨r1, r2, r3, r4⟩ := region hQ
  rw [← ha] at r1 r2 r3 r4
  rw [← haT] at r1 r2 r3 r4
  have ht : Progress.Sm.time p L g d n = clk p (slotOf p (n (.soft (.acquire 80)) -
      if past then 1 else 0)) (bd + o + Progress.Sm.subOff d) := by
    rw [hst] at hpl
    simp only [Progress.Sm.time, hpl]
  have hso : Progress.Sm.subOff d ≤ 1 := by
    unfold Progress.Sm.subOff; split <;> omega
  rw [h80] at ht
  generalize cA (Softmax.lz L g) d.site = A at *
  generalize cB (Softmax.lz L g) d.site = B at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨-, -⟩, hspan⟩, hpb⟩, hrem⟩, hck⟩ := hck
  cases hrc : d.site.rcoll with
  | true =>
    simp only [hrc, ite_true, Bool.and_eq_true, beq_iff_eq] at hck
    obtain ⟨⟨⟨hAB, hpast⟩, hbd⟩, hcase⟩ := hck
    subst hAB hpast hbd
    simp only [ite_true] at ht hpb
    have hsub : Progress.Sm.subOff d = 0 := by
      unfold Progress.Sm.subOff
      revert hrc
      cases d.site <;> simp [Softmax.Site.rcoll]
    rw [hsub, Nat.add_zero] at ht
    have key : ∃ e : Bool, A + rb + rp ≤ a.T ∧
        o = 18 + (if e then 2 else 0) ∧ d.site.rem = (if e then 1 else 2) ∧
        d.site = if e then .pel (rdOf a.nb (A + rb + rp)) else .pws (rdOf a.nb (A + rb + rp)) := by
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcase
      rcases hcase with (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨⟨h1, h2⟩, h3⟩
      · have hr := r1 h1
        have hrd : rdOf a.nb (A + rb + rp) = .first := by
          unfold rdOf; rw [ite_eq_left (by omega)]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨false, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
        · exact ⟨true, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
      · have hr := r2 h1
        have hrd : rdOf a.nb (A + rb + rp) = .bias := by
          unfold rdOf; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨false, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
        · exact ⟨true, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
      · have hr := r3 h1
        have hrd : rdOf a.nb (A + rb + rp) = .plain := by
          unfold rdOf; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact ⟨false, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
        · exact ⟨true, by omega, h4, by rw [h3]; rfl, by rw [hrd, h3]; rfl⟩
    obtain ⟨e, hu, ho, hr, hs⟩ := key
    have hu1 : A + rb + rp - 1 + 1 = A + rb + rp := by omega
    refine .inr (.inr ⟨A + rb + rp - 1, e, by omega, by omega, ?_, ?_, ?_⟩)
    · rw [hr] at hE
      cases e <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hE ⊢ <;> omega
    · rw [ht, hB, Progress.slotOf_eq (by omega), ho]
      unfold clk
      omega
    · rw [hu1, ← hs]
      simp
  | false =>
    simp only [hrc, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq, decide_eq_true_eq] at hck
    obtain ⟨⟨hr, hk⟩, hreg⟩ := hck
    have hu : A - d.site.rem / 2 + rb + rp ≤ a.T := by
      rcases hreg with ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
      · have := r1 h1; omega
      · have := r2 h1; omega
      · have := r3 h1; omega
      · have := r4 h1; omega
    refine .inr (.inl ⟨rfl, A - d.site.rem / 2 + rb + rp, hu, by omega, ?_⟩)
    rw [ht, hB, Progress.slotOf_eq (p := p) (a := A - d.site.rem / 2 + rb + rp) (by omega)]
    rcases hk with hk | ⟨hk, hk2⟩
    · refine Progress.clk_lt_of_slot ?_ (by omega)
      have := Progress.slotOf_eq (p := p)
        (a := B + rb + rp - if past then 1 else 0) (by omega)
      rw [this]
      omega
    · have : B + rb + rp - (if past then 1 else 0) = A - d.site.rem / 2 + rb + rp := by omega
      rw [this, Progress.slotOf_eq (by omega)]
      exact Progress.clk_lt_of_off (by omega)

theorem late_tab : (∀ b : Bool, allSites.all (fun s => !Progress.Sm.late s ||
    (cB b s == 1 && cA b s == 1 && (ptsOf b .nb).countP (before s) == 2 && s.rem == 0)) = true) ∧
    ∀ b : Bool, (ptsOf b .nb).countP inBias = 1 ∧ (ptsOf b .nb).countP inPlain = 1 := by
  constructor
  · decide +kernel
  · intro b; cases b <;> decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {w : Nat} (hw8 : w < 8)
  (hw : Prologue.warpIndex L g = w)
include hp hX hFw hub hg hw8 hw

omit hX hFw hub hw8 in
/-- A state's tile, from the rounds. -/
theorem soft_tile {R : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L g R bal) :
    ∃ a : SoftRun, IsSoftTile p L w (g / L.block) g a ∧
      a.ch = 4 + 7 * (R + 1) + Epilogue.selN bal ∧
      a.nb = (Softmax.nB p L g (softRef p L g R bal)).toNat ∧
      a.T = 1 + a.nb + (Softmax.nP p L g (softRef p L g R bal)).toNat := by
  obtain ⟨nb, hnb⟩ : ∃ nb, nb = (Softmax.nB p L g (softRef p L g R bal)).toNat := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = 1 + nb + (Softmax.nP p L g (softRef p L g R bal)).toNat := ⟨_, rfl⟩
  have hTR : SoftRounds p L g T := ⟨R, bal, hP, by rw [hT, hnb]⟩
  obtain ⟨R', hR, h1⟩ := soft_mma hTR rfl
  have hle := mma_rounds_bmax hp hg hR
  exact ⟨⟨_, nb, T⟩, ⟨hw, rfl, by rw [h1]; exact hle, R, bal, hP, rfl, hnb, hT⟩, rfl, hnb, hT⟩

end

/-- The round's site facts. -/
theorem place_facts (s : Softmax.Site) {st : Nat} (hst : st ∈ [0, 1])
    {x : Nat × Bool × Nat} (h : Progress.Sm.place st s = some x) (b : Bool) :
    SmWarp.epi s = .ready 0 ∧ s.hasUk = true ∧ s.rem ≤ 2 * cA b s ∧ s.wcoll = s.rcoll := by
  have hck := List.all_eq_true.mp (rs_ok b s) st hst
  rw [h] at hck
  obtain ⟨bd, past, o⟩ := x
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hck
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h3⟩, h4⟩ := hck
  refine ⟨h1, h2, ?_, ?_⟩
  · cases hr : s.rcoll with
    | true =>
      simp only [hr, ite_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h4
      have : s.rem ≤ 2 := by revert hr; cases s <;> simp [Softmax.Site.rcoll, Softmax.Site.rem]
      omega
    | false =>
      simp only [hr, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq] at h4
      omega
  · revert h
    cases s <;> simp [Progress.Sm.place, Softmax.Site.wcoll, Softmax.Site.rcoll]

theorem none_tab : ∀ b : Bool, allSites.all (fun s =>
    [0, 1].all fun st => (Progress.Sm.place st s).isSome || Progress.Sm.late s ||
      (preR s && cA b s == 0 && s.rem == 0)) = true := by decide +kernel

theorem init_pc : ∀ q : Fin 34, (∀ i : Fin 16, startCnt 0 (.init q) ≤ i.val →
    (Startup.Site.init q).pc < (Startup.Site.elect i).pc) ∧ (Startup.Site.init q).pc ≤ 173 := by
  decide

end
end SoftColl
end PTX.Kernels.TmlFa4Fwd.Proof
