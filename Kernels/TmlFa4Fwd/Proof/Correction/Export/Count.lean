-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The correction warps' counts at their barrier events

A correction lane of warp `8 + k` meets softmax warp `k + 4 s` on named barrier `warp - 5 + 4 s`.
It arrives on P-full `96 + 8 s` before the rounds, once per rescale round and once after the final
O barrier, and on credit barrier `192 + 8 s` after each meeting. Here these counts are related at
each event, in the trace; the rounds are the tile's (`CorrRounds`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (RefQ ptsOf passed before inRound)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event}

/-- The rounds' values of the tile the first pass picked. -/
def corrRef (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : Correction.V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (Epilogue.chosen c),
                   c1 := Epilogue.qv p (Epilogue.addi (Epilogue.chosen c) 1) },
    ukw := BitVec.ofNat 64 (p.kLength (Epilogue.r32 (Epilogue.chosen c)).toNat) }

/-- **The correction lane's tile has `R` rescale rounds.** -/
def CorrRounds (p : Params) (L : Launch) (g R : Nat) : Prop :=
  ∃ r bal, Epilogue.Picked p L g r bal ∧
    (Correction.Bs p L g (corrRef p L g r bal)).toNat - 1 = R

/-- The tile's blocks at a site of the rounds' region. -/
private theorem rounds_at {d : Correction.D} {ns nv : Nat} (hF : CorrWarp.CFits p L h d ns nv)
    (hep : CorrWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true) :
    CorrRounds p L h ((Correction.Bs p L h d.v).toNat - 1) := by
  obtain ⟨rv, -, -, hFE, hu⟩ := hF
  simp only [Epilogue.Fits, CorrWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  have hb := CorrWarp.bs_ref hC h0 h1 (hu huk)
  exact ⟨R, bal, hC.1, by rw [hb]; rfl⟩

private theorem arr_sites : Correction.allSites.all (fun s =>
    (Correction.arrOff s != 96 || s == .arr 0 || s == .rarr 0 0 || s == .fdone 0 0) &&
      (Correction.arrOff s != 104 || s == .arr 1 || s == .rarr 1 0 || s == .fdone 1 0) &&
      (Correction.arrOff s != 192 || s == .free || s == .rarr 1 1 || s == .farr 0) &&
      (Correction.arrOff s != 200 || s == .farr0 || s == .rarr 0 1 || s == .farr 1)) = true := by
  decide +kernel

private theorem p_sites {s : Correction.Site} {q : Fin 2}
    (ha : Correction.arrOff s = 96 + 8 * q.val) : s = .arr q ∨ s = .rarr q 0 ∨ s = .fdone q 0 := by
  have h1 := List.all_eq_true.mp arr_sites s (Correction.mem_allSites s)
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h1
  obtain ⟨⟨⟨a, b⟩, -⟩, -⟩ := h1
  fin_cases q
  · have : Correction.arrOff s = 96 := ha
    simp only [this, ne_eq, not_true_eq_false, false_or] at a
    tauto
  · have : Correction.arrOff s = 104 := ha
    simp only [this, ne_eq, not_true_eq_false, false_or] at b
    tauto

private theorem credit_sites {s : Correction.Site} {q : Fin 2}
    (ha : Correction.arrOff s = 192 + 8 * q.val) :
    (q = 0 ∧ (s = .free ∨ s = .rarr 1 1 ∨ s = .farr 0)) ∨
      (q = 1 ∧ (s = .farr0 ∨ s = .rarr 0 1 ∨ s = .farr 1)) := by
  have h1 := List.all_eq_true.mp arr_sites s (Correction.mem_allSites s)
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h1
  obtain ⟨⟨-, a⟩, b⟩ := h1
  fin_cases q
  · have : Correction.arrOff s = 192 := ha
    simp only [this, ne_eq, not_true_eq_false, false_or] at a
    exact .inl ⟨rfl, by tauto⟩
  · have : Correction.arrOff s = 200 := ha
    simp only [this, ne_eq, not_true_eq_false, false_or] at b
    exact .inr ⟨rfl, by tauto⟩

/-- Points before the P-full arrival sites, the credit sites and the named-barrier sites. -/
private theorem cnt_tab : ∀ q : Fin 2,
    ([Correction.Site.arr q, .rarr q 0, .fdone q 0].map fun s =>
      ((ptsOf (.arrive (96 + 8 * q.val))).countP (before s), (ptsOf (.nb q)).countP (before s),
        (ptsOf (.acquire (144 + 8 * q.val))).countP (before s))) =
      [(0, 0, 0), (1, 2, 0), (1, 2, 1)] ∧
    ([(if q = 0 then Correction.Site.free else .farr0), (if q = 0 then .rarr 1 1 else .rarr 0 1),
      .farr q].map fun s => (ptsOf (.nb q)).countP (before s) -
        (ptsOf (.arrive (192 + 8 * q.val))).countP (before s)) = [1, 1, 1] ∧
    ([(if q = 0 then Correction.Site.free else .farr0), (if q = 0 then .rarr 1 1 else .rarr 0 1),
      .farr q].all fun s => decide ((ptsOf (.arrive (192 + 8 * q.val))).countP (before s) <
        (ptsOf (.nb q)).countP (before s))) = true ∧
    ([Correction.Site.nb q, .rbar q, .fbar q].map fun s => (ptsOf (.nb q)).countP (before s)) =
      [0, 1, 1] ∧
    [(ptsOf (.arrive (96 + 8 * q.val))).countP inRound,
      (ptsOf (.arrive (192 + 8 * q.val))).countP inRound, (ptsOf (.nb q)).countP inRound,
      (ptsOf (.acquire (144 + 8 * q.val))).countP inRound] = [1, 1, 1, 0] := by
  decide

private theorem ready_sites : Correction.allSites.all (fun s =>
    (Correction.arrOff s != 208 || s == .fdone 0 1) &&
      (Correction.arrOff s != 216 || s == .fdone 1 1)) = true := by
  decide +kernel

private theorem ready_tab : ∀ q : Fin 2,
    (ptsOf (.arrive (208 + 8 * q.val))).countP (before (.fdone q 1)) = 0 ∧
      (ptsOf (.arrive (208 + 8 * q.val))).countP inRound = 0 := by
  decide

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
include hp hX hFw hw hw1

/-- **A credit arrival** follows one more event on its named barrier than the lane's earlier
arrivals on it. -/
theorem corr_credit_arr (q : Fin 2) {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (192 + 8 * q.val)) tx c rel sc⟩) :
    ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h - 5 + 4 * q.val)) =
      arrivals (obj L h (192 + 8 * q.val)) ((X.tr h).take k) + 1 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := obj L h (192 + 8 * q.val)) rfl
    cases hc
  rcases corr_mbar2 hev (l := obj L h (192 + 8 * q.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  have ho : 192 + 8 * q.val = Correction.arrOff d.site := obj_inj hl
  have h1 := hQ.cnt (.arrive (192 + 8 * q.val)) (by simp)
  have h2 := hQ.cnt (.nb q) (by simp)
  obtain ⟨-, t2, t3, -, t5⟩ := cnt_tab q
  simp only [List.map, List.all, List.cons.injEq, and_true, Bool.and_eq_true,
    decide_eq_true_eq] at t2 t3 t5
  rw [corr_isBarId hw hw1, corr_arrivals, hc, hc, h1, h2]
  simp only [passed, t5, Nat.mul_one]
  have hs : d.site = (if q = 0 then Correction.Site.free else .farr0) ∨
      d.site = (if q = 0 then .rarr 1 1 else .rarr 0 1) ∨ d.site = .farr q := by
    rcases credit_sites ho.symm with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simpa using h
  rcases hs with hs | hs | hs <;> rw [hs] <;> omega

/-- **A P-full arrival**: the lane's first, before everything, or its `u`-th, after its `u`-th
event on its named barrier: a rescale round's, `u` at most the tile's rescale rounds, or the last,
after the final O barrier. -/
theorem corr_p_arr (q : Fin 2) {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (96 + 8 * q.val)) tx c rel sc⟩) :
    arrivals (obj L h (96 + 8 * q.val)) ((X.tr h).take k) = 0 ∨
      (((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h - 5 + 4 * q.val)) =
        arrivals (obj L h (96 + 8 * q.val)) ((X.tr h).take k) + 1 ∧
      ∃ R, CorrRounds p L h R ∧
        (arrivals (obj L h (96 + 8 * q.val)) ((X.tr h).take k) ≤ R ∨
          arrivals (obj L h (96 + 8 * q.val)) ((X.tr h).take k) = R + 1 ∧
            okPolls (obj L h (144 + 8 * q.val)) ((X.tr h).take k) = 1)) := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, hF, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := obj L h (96 + 8 * q.val)) rfl
    cases hc
  rcases corr_mbar2 hev (l := obj L h (96 + 8 * q.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  have ho : 96 + 8 * q.val = Correction.arrOff d.site := obj_inj hl
  have h1 := hQ.cnt (.arrive (96 + 8 * q.val)) (by simp)
  have h2 := hQ.cnt (.nb q) (by simp)
  have h3 := hQ.cnt (.acquire (144 + 8 * q.val)) (by simp)
  obtain ⟨t1, -, -, -, t5⟩ := cnt_tab q
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t5
  obtain ⟨a1, a2, a3⟩ := t1
  simp only [passed, t5, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at h1 h2 h3
  rw [corr_isBarId hw hw1, corr_arrivals, corr_okPolls, hc, hc, hc, h1, h2, h3]
  have hpre := hQ.pre
  have hloop := hQ.loop
  have htail := hQ.tail
  rcases p_sites ho.symm with hs | hs | hs
  · left
    rw [hs, a1.1, hpre (by rw [hs]; fin_cases q <;> decide)]
  · right
    have hl := hloop (by rw [hs]; fin_cases q <;> decide)
    have hr := rounds_at hF (by rw [hs]; fin_cases q <;> rfl) (by rw [hs]; fin_cases q <;> rfl)
    rw [hs, a2.1, a2.2.1, a2.2.2]
    exact ⟨by omega, _, hr, .inl (by omega)⟩
  · right
    have hl := htail (by rw [hs]; fin_cases q <;> decide)
    have hr := rounds_at hF (by rw [hs]; fin_cases q <;> rfl) (by rw [hs]; fin_cases q <;> rfl)
    rw [hs, a3.1, a3.2.1, a3.2.2]
    exact ⟨by omega, _, hr, .inr ⟨by omega, rfl⟩⟩

/-- **A ready arrival** is the lane's only one on its barrier. -/
theorem corr_ready_arr (q : Fin 2) {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (208 + 8 * q.val)) tx c rel sc⟩) :
    arrivals (obj L h (208 + 8 * q.val)) ((X.tr h).take k) = 0 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := obj L h (208 + 8 * q.val)) rfl
    cases hc
  rcases corr_mbar2 hev (l := obj L h (208 + 8 * q.val)) rfl with ⟨-, hl, -⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  have ho : 208 + 8 * q.val = Correction.arrOff d.site := obj_inj hl
  have hs : d.site = .fdone q 1 := by
    have h1 := List.all_eq_true.mp ready_sites d.site (Correction.mem_allSites d.site)
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h1
    revert ho
    fin_cases q
    · intro ho
      have ho' : Correction.arrOff d.site = 208 := ho.symm
      simpa [ho'] using h1.1
    · intro ho
      have ho' : Correction.arrOff d.site = 216 := ho.symm
      simpa [ho'] using h1.2
  have h1 := hQ.cnt (.arrive (208 + 8 * q.val)) (by simp)
  obtain ⟨t1, t2⟩ := ready_tab q
  rw [corr_arrivals, hc, h1, hs, passed, t1, t2, Nat.mul_zero]

/-- **A correction lane's named-barrier events**: the startup's, barrier 2 (a `bar.sync`, then a
`bar.arrive`), or its barrier with a softmax warp, a `bar.sync` with at most one more earlier ones
than the tile's rescale rounds. -/
theorem corr_bar {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (h, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id = 0 ∧ cnt = none ∧ mode = .sync) ∨
      (id = 2 ∧ cnt = some 416 ∧
        (mode = .sync ∧ ((X.tr h).take k).countP (Execution.isBarId 2) = 0 ∨
          mode = .arrive ∧ ((X.tr h).take k).countP (Execution.isBarId 2) = 1)) ∨
      ∃ q : Fin 2, id = Prologue.warpIndex L h - 5 + 4 * q.val ∧ cnt = some 64 ∧ mode = .sync ∧
        ∃ R, CorrRounds p L h R ∧ ((X.tr h).take k).countP (Execution.isBarId id) ≤ R + 1 := by
  rcases corr_counts_nonvote hp hX hFw hw hw1 he (fun f h => by cases h) (fun _ _ => nofun) with
    ⟨s, hev, hx⟩ | ⟨d, c, r, ℓ, ns, nv, hQ, hF, hev, hc⟩
  · refine .inl ?_
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => simp [exit] at hx
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    | fence => simp only [Startup.Ev] at hev; cases hev
    | bar =>
      simp only [Startup.Ev, Kind.bar.injEq] at hev
      exact hev
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  rcases corr_bar_site hev with ⟨hs, rfl, rfl⟩ | ⟨q, hs, rfl, rfl, rfl⟩
  · refine .inr (.inl ⟨rfl, rfl, ?_⟩)
    have h1 := hQ.cnt .bar2 (by simp)
    rw [corr_isBar2, hc, h1]
    have t : ∀ r, passed (ptsOf .bar2) .bar1 r = 0 ∧
        ∀ l, passed (ptsOf .bar2) (.barEnd l) r = 1 := by
      have : (ptsOf .bar2).countP inRound = 0 ∧ (ptsOf .bar2).countP (before .bar1) = 0 ∧
          ∀ l, (ptsOf .bar2).countP (before (.barEnd l)) = 1 := by decide
      intro r
      refine ⟨by rw [passed, this.1, this.2.1, Nat.mul_zero], fun l => ?_⟩
      rw [passed, this.1, this.2.2 l, Nat.mul_zero]
    rcases hs with ⟨hs, rfl⟩ | ⟨⟨l, hs⟩, rfl⟩
    · exact .inl ⟨rfl, by rw [hs]; exact (t r).1⟩
    · exact .inr ⟨rfl, by rw [hs]; exact (t r).2 l⟩
  · refine .inr (.inr ⟨q, corr_nbW hw hw1 q, rfl, rfl, ?_⟩)
    have h2 := hQ.cnt (.nb q) (by simp)
    obtain ⟨-, -, -, t4, t5⟩ := cnt_tab q
    simp only [List.map, List.cons.injEq, and_true] at t4 t5
    simp only [passed, t5, Nat.mul_one] at h2
    rw [corr_nbW hw hw1, corr_isBarId hw hw1, hc, h2]
    have hpre := hQ.pre
    have hloop := hQ.loop
    have htail := hQ.tail
    have hr := rounds_at hF (by rcases hs with hs | hs | hs <;> rw [hs] <;> fin_cases q <;> rfl)
      (by rcases hs with hs | hs | hs <;> rw [hs] <;> fin_cases q <;> rfl)
    refine ⟨_, hr, ?_⟩
    rcases hs with hs | hs | hs
    · rw [hpre (by rw [hs]; fin_cases q <;> decide), hs, t4.1]; omega
    · have hl := hloop (by rw [hs]; fin_cases q <;> decide)
      rw [hs, t4.2.1]; omega
    · have hl := htail (by rw [hs]; fin_cases q <;> decide)
      rw [hs, t4.2.2]; omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
