-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Softmax.Places
public import Kernels.TmlFa4Fwd.Proof.Softmax.Ref
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.SmWarp.P2Count
import Kernels.TmlFa4Fwd.Proof.Softmax.Align
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Mbar
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Lemmas.Flow.NthEv
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' counts at their barrier events

A softmax lane of stage `st` (warp `k + 4 st`) polls S-full (80) at the start of each round,
arrives on its named barrier with the correction warps (`warp + 3`), on P-full (96) and, when it
wins the round's election, on the second P barrier (112), and polls the credit barrier (192) before
the rounds and at the end of each. After the rounds it arrives once more on its named barrier. Here
these counts are related at each event, in the trace. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event}

/-- The stage's barrier at offset `a` of a softmax lane. -/
abbrev sobj (L : Launch) (h a : Nat) : Loc := obj L h (8 * (Prologue.warpIndex L h / 4) + a)

/-- The rounds' values of the tile the first pass picked. -/
def softRef (p : Params) (L : Launch) (g R : Nat) (bal : BitVec 64) : Softmax.V :=
  let c := Epilogue.chosenD p (g / L.block) R bal
  { sc := { c with c0 := Epilogue.qv p (Epilogue.chosen c),
                   c1 := Epilogue.qv p (Epilogue.addi (Epilogue.chosen c) 1) },
    ukw := BitVec.ofNat 64 (p.kLength (Epilogue.r32 (Epilogue.chosen c)).toNat) }

/-- **The softmax lane's tile has `T` rounds.** -/
def SoftRounds (p : Params) (L : Launch) (g T : Nat) : Prop :=
  ∃ R bal, Epilogue.Picked p L g R bal ∧
    1 + (Softmax.nB p L g (softRef p L g R bal)).toNat +
      (Softmax.nP p L g (softRef p L g R bal)).toNat = T

private theorem done_toNat' {r : Nat} {n : Int} (h : Softmax.Done r n) : n.toNat = r := by
  rcases h with h | ⟨rfl, h⟩ <;> omega

/-- The points before the sites read here: S-full polls, credit polls, named-barrier arrivals,
P-full arrivals, barrier 2. -/
private theorem cnt_tab (b : Bool) :
    ([Softmax.Site.narr .first, .narr .bias, .narr .plain, .finarr, .parr .first, .parr .bias,
      .parr .plain, .parr2 .first, .parr2 .bias, .parr2 .plain, .exit true, .exit false, .bar1,
      .barEnd true, .barEnd false].map
      fun s => ((ptsOf b (.acquire 80)).countP (before s), (ptsOf b (.acquire 192)).countP
        (before s), (ptsOf b .nb).countP (before s), (ptsOf b (.arrive 96)).countP (before s),
        (ptsOf b .bar2).countP (before s))) =
      [(1, 1, 0, 0, 1), (2, 2, 1, 1, 1), (2, 2, 1, 1, 1), (1, 2, 1, 1, 1), (1, 1, 1, 0, 1),
        (2, 2, 2, 1, 1), (2, 2, 2, 1, 1), (1, 1, 1, 1, 1), (2, 2, 2, 2, 1), (2, 2, 2, 2, 1),
        (1, 3, 2, 1, 2), (0, 1, 0, 0, 2), (0, 0, 0, 0, 0), (1, 3, 2, 1, 1), (0, 1, 0, 0, 1)] ∧
    [(ptsOf b (.acquire 80)).countP inBias, (ptsOf b (.acquire 80)).countP inPlain,
      (ptsOf b (.acquire 192)).countP inBias, (ptsOf b (.acquire 192)).countP inPlain,
      (ptsOf b .nb).countP inBias, (ptsOf b .nb).countP inPlain,
      (ptsOf b (.arrive 96)).countP inBias, (ptsOf b (.arrive 96)).countP inPlain,
      (ptsOf b .bar2).countP inBias, (ptsOf b .bar2).countP inPlain] =
      [1, 1, 1, 1, 1, 1, 1, 1, 0, 0] := by
  cases b <;> decide +kernel

/-- The reference counts at a site of `cnt_tab`, as numbers. -/
private theorem cnts {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp : Nat}
    (hQ : RefQ p L h d c rb rp) :
    (∀ r, d.site = .narr r → c (.acquire 80) = c .nb + 1 ∧ c (.acquire 192) = c .nb + 1) ∧
    (d.site = .finarr → c (.acquire 80) = c .nb ∧ c (.acquire 192) = c .nb + 1 ∧
      c .nb = 1 + rb + rp) ∧
    (∀ r, d.site = .parr r → c (.acquire 80) = c (.arrive 96) + 1) ∧
    (∀ r, d.site = .parr2 r → c (.acquire 80) = c (.arrive 96)) ∧
    (d.site = .exit true → c .nb = c (.acquire 80) + 1 ∧ 1 ≤ c (.acquire 80)) ∧
    (d.site = .exit false → c .nb = rb + rp) ∧
    (d.site = .bar1 → c .bar2 = 0) ∧ (∀ l, d.site = .barEnd l → c .bar2 = 1) := by
  obtain ⟨t1, t2⟩ := cnt_tab (Softmax.lz L h)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true] at t1 t2
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := t1
  have c1 := hQ.cnt (.acquire 80) rfl
  have c2 := hQ.cnt (.acquire 192) rfl
  have c3 := hQ.cnt .nb rfl
  have c4 := hQ.cnt (.arrive 96) rfl
  have c5 := hQ.cnt .bar2 rfl
  simp only [passed, t2] at c1 c2 c3 c4 c5
  clear hQ
  obtain ⟨s, v, kk, acc⟩ := d
  dsimp only at *
  refine ⟨fun r hs => ?_, fun hs => ?_, fun r hs => ?_, fun r hs => ?_, fun hs => ?_,
    fun hs => ?_, fun hs => ?_, fun l hs => ?_⟩
  all_goals subst hs
  · cases r <;> simp only [a1, a2, a3] at c1 c2 c3 <;> omega
  · simp only [a4] at c1 c2 c3; omega
  · cases r <;> simp only [a5, a6, a7] at c1 c4 <;> omega
  · cases r <;> simp only [a8, a9, a10] at c1 c4 <;> omega
  · simp only [a11] at c1 c3; omega
  · simp only [a12] at c3; omega
  · simp only [a13] at c5; omega
  · cases l <;> simp only [a14, a15] at c5 <;> omega

/-- The rounds' counts are the picked tile's. -/
theorem nBP {d : Softmax.D} {ns nv R : Nat} {bal : BitVec 64}
    (hC : Epilogue.ChosenVals p L h R bal (SmWarp.toE d) ns nv)
    (h0 : d.v.sc.c0 = Epilogue.qv p (Epilogue.chosen d.v.sc))
    (h1 : d.v.sc.c1 = Epilogue.qv p (Epilogue.addi (Epilogue.chosen d.v.sc) 1))
    (hu : d.v.ukw = Mma.ukv p (Epilogue.chosen d.v.sc)) :
    Softmax.nB p L h d.v = Softmax.nB p L h (softRef p L h R bal) ∧
      Softmax.nP p L h d.v = Softmax.nP p L h (softRef p L h R bal) := by
  obtain ⟨-, ht, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  have ht' : d.v.sc.tot = _ := ht
  have hgx' : d.v.sc.gx = _ := hgx
  have hcur' : d.v.sc.cur = _ := hcur
  have hbal' : d.v.sc.bal = _ := hbal
  have hpv' : d.v.sc.pv = _ := hpv
  have hnt' : d.v.sc.nt = _ := hnt
  have hch : Epilogue.chosen d.v.sc =
      Epilogue.chosen (Epilogue.chosenD p (h / L.block) R bal) := by
    simp only [Epilogue.chosen, Epilogue.chosenD, hbal', hgx']
  constructor <;>
  simp only [Softmax.nB, Softmax.nP, Softmax.r169, Softmax.r299, Softmax.r431, Softmax.r166,
    Softmax.r168, Softmax.r165, Softmax.r1808, Softmax.rowOff, Mma.coords, softRef, hu, h0, h1,
    hch, ht', hcur', hpv', hnt', Epilogue.chosenD, Mma.ukv]

/-- The tile's rounds at a site of the rounds' region. -/
private theorem rounds_at {d : Softmax.D} {ns nv rb rp : Nat} (hF : SmWarp.SFits p L h d ns nv)
    (hep : SmWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true)
    (hd : Softmax.Done rb (Softmax.nB p L h d.v) ∧ Softmax.Done rp (Softmax.nP p L h d.v)) :
    SoftRounds p L h (1 + rb + rp) := by
  obtain ⟨hFE, hu⟩ := hF
  simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  obtain ⟨eB, eP⟩ := nBP hC h0 h1 (hu huk)
  refine ⟨R, bal, hC.1, ?_⟩
  rw [← eB, ← eP, done_toNat' hd.1, done_toNat' hd.2]

/-- **The round of a state in the rounds' region**: the first round, or the biased and plain rounds
done after it; it is one of the tile's. -/
theorem soft_round_lt {d : Softmax.D} {c : Softmax.Cnt → Nat} {ns nv rb rp : Nat}
    (hQ : RefQ p L h d c rb rp) (hF : SmWarp.SFits p L h d ns nv)
    (hep : SmWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true)
    (hr : Softmax.preR d.site = true ∨ inBias d.site.pos = true ∨ inPlain d.site.pos = true) :
    ∃ T, SoftRounds p L h T ∧ rb + rp < T ∧
      (Softmax.preR d.site = true ∨ 1 + rb + rp < T) := by
  obtain ⟨hFE, hu⟩ := hF
  simp only [Epilogue.Fits, SmWarp.toE, hep] at hFE
  obtain ⟨R, bal, hC, h0, h1⟩ := hFE
  obtain ⟨eB, eP⟩ := nBP hC h0 h1 (hu huk)
  refine ⟨_, ⟨R, bal, hC.1, rfl⟩, ?_⟩
  rw [← eB, ← eP]
  rcases hr with hr | hr | hr
  · obtain ⟨rfl, rfl⟩ := hQ.pre hr
    exact ⟨by omega, .inl hr⟩
  · obtain ⟨rfl, -, h, -⟩ := hQ.bias hr
    exact ⟨by omega, .inr (by omega)⟩
  · obtain ⟨-, h, -, hd⟩ := hQ.plain hr
    have := done_toNat' hd
    exact ⟨by omega, .inr (by omega)⟩

private theorem b_tab : (∀ b : Bool,
    (ptsOf true (.acquire 320)).countP (before (.barr b)) =
      (ptsOf true (.arrive 336)).countP (before (.barr b)) + 1) ∧
    ([(ptsOf true (.acquire 320)).countP inBias, (ptsOf true (.acquire 320)).countP inPlain] =
      [(ptsOf true (.arrive 336)).countP inBias, (ptsOf true (.arrive 336)).countP inPlain]) := by
  decide +kernel

/-- The lane that frees the bias slot is lane 0. -/
private theorem lz_lane (hp : Pre p L m) (hz : Softmax.lz L h = true) : h % L.block % 32 = 0 := by
  have hb : h % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  simp only [Softmax.lz, Softmax.tidW_eq hp] at hz
  generalize h % L.block = n at *
  have key : ∀ n < 512, (!Epilogue.scmpi .ne .b (Epilogue.andi (BitVec.ofNat 64 n) 31) 0) = true →
      n % 32 = 0 := by decide +kernel
  exact key n hb hz

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hw : Prologue.warpIndex L h < 8)
include hp hX hFw hw

/-- **A P-full arrival** follows one more S-full poll than the lane's earlier P-full arrivals. -/
theorem soft_p_arr {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (sobj L h 96) tx c rel sc⟩) :
    okPolls (sobj L h 80) ((X.tr h).take k) = arrivals (sobj L h 96) ((X.tr h).take k) + 1 := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := sobj L h 96) rfl
    cases hc
  rcases soft_mbar hev (l := sobj L h 96) rfl with ⟨-, hl, hmem⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  rw [soft_bl hw] at hl
  have ho := obj_inj hl
  have hs : ∃ r, d.site = .parr r := by
    have ho : _ = Softmax.arrOff d.site := Nat.add_left_cancel ho
    revert ho
    cases d.site <;> simp [Softmax.arrOff]
  obtain ⟨r, hr⟩ := hs
  have h1 := (cnts hQ).2.2.1 r hr
  rw [soft_okPolls hw, soft_arrivals hw (by decide), hc _ rfl, hc _ rfl]
  exact h1

/-- **A second P arrival** follows more S-full polls than the lane's earlier second arrivals; as
many, plus one, when the lane lost no election. It follows an election the lane won. -/
theorem soft_p2_arr {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (sobj L h 112) tx c rel sc⟩) :
    arrivals (sobj L h 112) ((X.tr h).take k) + 1 ≤ okPolls (sobj L h 80) ((X.tr h).take k) ∧
      ((∀ j pc mask inst ld, X.get (h, j) = some ⟨pc, .elect mask inst ld⟩ → ld = laneOf L h) →
        arrivals (sobj L h 112) ((X.tr h).take k) + 1 =
          okPolls (sobj L h 80) ((X.tr h).take k)) := by
  have hub : ∀ f, (⟨pc, .arrive (sobj L h 112) tx c rel sc⟩ : Event).kind ≠ .ub f :=
    fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := sobj L h 112) rfl
    cases hc
  obtain ⟨⟨c', ⟨⟨rb, rp, hQ⟩⟩, hLk⟩, -⟩ := hR.2 h0
  rcases soft_mbar hev.1 (l := sobj L h 112) rfl with ⟨-, hl, hmem⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  rw [soft_bl hw] at hl
  have ho := obj_inj hl
  have hs : ∃ r, d.site = .parr2 r := by
    have ho : _ = Softmax.arrOff d.site := Nat.add_left_cancel ho
    revert ho
    cases d.site <;> simp [Softmax.arrOff]
  obtain ⟨r, hr⟩ := hs
  have h1 := (cnts hQ).2.2.2.1 r hr
  have h2 := p2_before hp hX hFw he hσ
  rw [hr] at h2
  simp only [midP2] at h2
  have h3 : okPolls (sobj L h 80) ((X.tr h).take k) =
      ((X.tr h).take k).countP (cls L h (.soft (.arrive 96))) := by
    rw [soft_okPolls hw, count hσ, count hσ, ← hLk _ rfl, ← hLk _ rfl]
    exact h1
  have hle : arrivals (sobj L h 112) ((X.tr h).take k) ≤ ((X.tr h).take k).countP (isP2 L h) := by
    refine List.countP_mono_left fun e _ hea => ?_
    obtain ⟨pce, ke⟩ := e
    cases ke <;> simp only [arrivesOn, sourceArrive, decide_eq_true_eq, Bool.false_eq_true] at hea
    simp [isP2, hea, soft_bl hw]
  refine ⟨by omega, fun hall => ?_⟩
  have heq : arrivals (sobj L h 112) ((X.tr h).take k) = ((X.tr h).take k).countP (isP2 L h) := by
    refine List.countP_congr fun e hme => ?_
    obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hme
    have hget : X.get (h, j) = some e := by
      rw [List.length_take] at hj
      change (X.tr h)[j]? = _
      rw [← hje, List.getElem_take, List.getElem?_eq_getElem]
    obtain ⟨pce, ke⟩ := e
    cases ke with
    | arrive m' => simp [arrivesOn, sourceArrive, isP2, soft_bl hw]
    | elect mask inst ld =>
      have := hall j _ _ _ _ hget
      simp [arrivesOn, sourceArrive, isP2, this]
    | _ => simp [arrivesOn, sourceArrive, isP2]
  omega

/-- **A second P arrival** follows an election the lane won. -/
theorem soft_p2_won {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (sobj L h 112) tx c rel sc⟩) :
    ∃ j pc' inst, j < k ∧ X.get (h, j) = some ⟨pc', .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ := by
  have hub : ∀ f, (⟨pc, .arrive (sobj L h 112) tx c rel sc⟩ : Event).kind ≠ .ub f :=
    fun f h => by cases h
  rcases SmWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, -, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := sobj L h 112) rfl
    cases hc
  rcases soft_mbar hev.1 (l := sobj L h 112) rfl with ⟨-, hl, hmem⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  rw [soft_bl hw] at hl
  have ho := obj_inj hl
  have hs : d.site.isParr2 = true := by
    have ho : _ = Softmax.arrOff d.site := Nat.add_left_cancel ho
    revert ho
    cases d.site <;> simp [Softmax.arrOff, Softmax.Site.isParr2]
  have h1 := won_count hp hX hFw (Frame.lt_of_get hX he) k _
    (Frame.noUbBefore_of_get hX he) hσ h0 hs
  obtain ⟨j, ⟨pc', kd⟩, hj, hget, hw', -⟩ := exists_nthEv (X := X) (g := h) (k := k)
    (p := isWonEl L h) (n := 0) (by omega)
  cases kd <;> simp [isWonEl] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  exact ⟨j, pc', _, hj, hget⟩

/-- **An arrival freeing the bias slot** (336) is lane 0's, after one more poll of the bias slot
(320) than its earlier arrivals. -/
theorem soft_b_arr {pc tx c : Nat} {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (sobj L h 336) tx c rel sc⟩) :
    h % L.block % 32 = 0 ∧
      okPolls (sobj L h 320) ((X.tr h).take k) =
        arrivals (sobj L h 336) ((X.tr h).take k) + 1 := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, _, _, hQ, -, hev, hc⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hx (l := sobj L h 336) rfl
    cases hc
  rcases soft_mbar hev (l := sobj L h 336) rfl with ⟨-, hl, hmem⟩ | ⟨_, _, hk, -⟩
  swap; · cases hk
  rw [soft_bl hw] at hl
  have ho := obj_inj hl
  have hs : ∃ b, d.site = .barr b := by
    have ho : _ = Softmax.arrOff d.site := Nat.add_left_cancel ho
    revert ho
    cases d.site <;> simp [Softmax.arrOff]
  obtain ⟨b, hr⟩ := hs
  have hlz := hQ.barr (by rw [hr]; rfl)
  refine ⟨?_, ?_⟩
  · exact lz_lane hp hlz
  · rw [soft_okPolls hw, soft_arrivals hw (by decide), hc _ rfl, hc _ rfl,
      hQ.cnt (.acquire 320) rfl, hQ.cnt (.arrive 336) rfl, hlz, hr]
    have t := b_tab.2
    simp only [List.cons.injEq, and_true] at t
    simp only [passed, b_tab.1 b, t.1, t.2]
    omega

/-- **A softmax lane's named-barrier events**: the startup's, barrier 2 (a `bar.sync`, then a
`bar.arrive`), the stage's barrier, or its barrier with the correction warps, an arrival. The
latter's `G`-th follows `G + 1` credit polls, and `G + 1` S-full polls or, after all `G` rounds of
the tile, `G`. -/
theorem soft_bar {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (h, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id = 0 ∧ cnt = none ∧ mode = .sync) ∨
      (id = 2 ∧ cnt = some 416 ∧
        (mode = .sync ∧ ((X.tr h).take k).countP (Execution.isBarId 2) = 0 ∨
          mode = .arrive ∧ ((X.tr h).take k).countP (Execution.isBarId 2) = 1)) ∨
      ((id = 11 ∨ id = 12) ∧ cnt = some 128 ∧ mode = .sync) ∨
      (id = Prologue.warpIndex L h + 3 ∧ cnt = some 64 ∧ mode = .arrive ∧
        okPolls (sobj L h 192) ((X.tr h).take k) =
          ((X.tr h).take k).countP (Execution.isBarId id) + 1 ∧
        (okPolls (sobj L h 80) ((X.tr h).take k) =
            ((X.tr h).take k).countP (Execution.isBarId id) + 1 ∨
          okPolls (sobj L h 80) ((X.tr h).take k) =
              ((X.tr h).take k).countP (Execution.isBarId id) ∧
            SoftRounds p L h (((X.tr h).take k).countP (Execution.isBarId id)))) := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, ns, nv, hQ, hF, hev, hc⟩
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
  obtain ⟨n1, n2, -, -, -, -, n7, n8⟩ := cnts hQ
  rcases soft_bar_site hev with ⟨hs, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨hs, rfl, rfl, rfl⟩
  · refine .inr (.inl ⟨rfl, rfl, ?_⟩)
    rw [soft_isBar2 hw, hc _ rfl]
    rcases hs with ⟨hs, rfl⟩ | ⟨⟨l, hs⟩, rfl⟩
    · exact .inl ⟨rfl, n7 hs⟩
    · exact .inr ⟨rfl, n8 l hs⟩
  · exact .inr (.inr (.inl ⟨by split <;> simp, rfl, rfl⟩))
  · refine .inr (.inr (.inr ⟨soft_nbW hw, rfl, rfl, ?_⟩))
    rw [soft_nbW hw, soft_isBarId hw, soft_okPolls hw, soft_okPolls hw, hc _ rfl, hc _ rfl,
      hc _ rfl]
    rcases hs with hs | ⟨r, hs⟩
    · obtain ⟨h1, h2, h3⟩ := n2 hs
      refine ⟨h2, .inr ⟨h1, ?_⟩⟩
      rw [h3]
      exact rounds_at hF (by rw [hs]; rfl) (by rw [hs]; rfl) (hQ.fin (by rw [hs]; decide))
    · obtain ⟨h1, h2⟩ := n1 r hs
      exact ⟨h2, .inl h1⟩

/-- **At its exit** a softmax lane without a tile made no arrival on its barrier with the correction
warps; one with a tile made one more than its S-full polls, at least two. -/
theorem soft_exit {pc : Nat} (he : X.get (h, k) = some ⟨pc, .exit⟩) :
    (¬ ∃ R bal, Epilogue.Picked p L h R bal) ∨
      ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) =
          okPolls (sobj L h 80) ((X.tr h).take k) + 1 ∧
        1 ≤ okPolls (sobj L h 80) ((X.tr h).take k) := by
  rcases soft_counts hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, ns, nv, hQ, hF, hev, hc⟩
  · exfalso
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => simp [exit] at hx
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> cases hk
    | fence | bar => simp only [Startup.Ev] at hev; cases hev
    | elect j =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hev
      rcases hev with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨-, -, -, -, n5, -, -, -⟩ := cnts hQ
  obtain ⟨l, hs⟩ := soft_exit_site' hev
  cases l
  · exact .inl (noPicked_of_exit hF.1 (by simp only [hs, SmWarp.epi]))
  · refine .inr ?_
    rw [soft_isBarId hw, soft_okPolls hw, hc _ rfl, hc _ rfl]
    exact n5 hs

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
