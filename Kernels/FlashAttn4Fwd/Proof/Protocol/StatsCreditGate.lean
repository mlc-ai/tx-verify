-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.StatsGen
public import Kernels.FlashAttn4Fwd.Proof.Interface.Tmem
public import Lemmas.Protocol.UnitBlocker

@[expose] public section

/-! # The statistics credit barriers are gated unit objects

Stage `st`'s credit barrier of CTA `c` (`statsBar`, count 128) is a unit object
(`MbarRing.Unit.Obj`, offset 1): its arrivals are the release arrivals without transaction bytes
of the CTA's 128 correction threads (`corrThread`), its polls the softmax threads' of the stage,
with the parity of their earlier successful polls plus one (`StatsFacts.credit_arrive`,
`credit_poll`; no copy, commit, bulk copy, cancellation request or invalidation touches it). Its
history starts with its only initialization (`StatsInit`, the premise of the ring barriers'
`RingInit` for these barriers).

It is gated by the softmax polls (`MbarRing.Unit.Gate`): correction thread `a` is paired with the
softmax threads of the stage's warp handling its rows (`softPair`). Its credit arrival of use
`s ≥ 1` follows its `bar.sync` of ordinal `s` on the statistics barrier (`corr_credit`), whose
generation the partner softmax lane's `bar.arrive` of ordinal `s` joins (a rendezvous,
`Sources.arrive_key_of_credit`), and that arrival follows the lane's credit poll with `s` earlier
successful ones (`soft_credit`), which spins: an enabling path poll, arrival, `bar.sync`, credit
arrival (`gate_path`). That the partner lane made its arrival of the ordinal is `SoftArrives`, a
premise: a passed `bar.sync` has every participant's arrival unless the participant exited, and an
exited softmax lane made all its arrivals (the role layer's exit counts).

So `StatsCredit` holds (`statsCredit`, `MbarRing.Unit.Gate.handoff`), and a softmax thread
blocked at its credit wait is one use ahead of the barrier's phase, which some correction thread
has not yet completed (`creditBlocked`, `MbarRing.Unit.Gate.blocked`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof CtaBarrier
open AsyncCopy

noncomputable section

namespace Stats

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- Correction thread `a` (of the 128) of CTA `c`. -/
def corrThread (L : Launch) (c : Nat) (a : Fin 128) : Nat := c * L.block + (256 + a.val)

/-- Softmax thread `h` of stage `st` handles the rows of correction thread `a` of CTA `c`. -/
def softPair (L : Launch) (c st : Nat) (a : Fin 128) (h : Nat) : Prop :=
  ctaOf L h = c ∧ warpOf L h = a.val / 32 + 4 * st

/-- **The initialization premise** of the credit barriers: each history starts with its only
initialization, without fault, with count 128. -/
def StatsInit (L : Launch) (X : Execution) : Prop :=
  ∀ c st, st < 2 → PairTmaRing.InitFirst X (statsBar L c st) 128

/-- **The partner arrival premise**: a passed `bar.sync` of a statistics barrier has, for every
lane of the barrier's softmax warp, its event on the barrier of the same ordinal. -/
def SoftArrives (L : Launch) (X : Execution) : Prop :=
  ∀ {y j pc st k h : Nat}, st < 2 → k < 4 → X.IsBarrier (y, j) (statsId st k) (some 64) pc →
    j + 1 < (X.tr y).length → h < L.threads → ctaOf L h = ctaOf L y → warpOf L h = k + 4 * st →
      ∃ i pc' cnt md, X.get (h, i) = some ⟨pc', .bar (statsId st k) cnt md⟩ ∧
        barOrd X h i (statsId st k) = barOrd X y j (statsId st k)

theorem corrThread_facts (hpre : Pre P L mem0) {c : Nat} (hc : c < L.grid) (a : Fin 128) :
    corrThread L c a < L.threads ∧ ctaOf L (corrThread L c a) = c ∧
      warpOf L (corrThread L c a) = 8 + a.val / 32 := by
  have hb := hpre.block
  have ha := a.isLt
  unfold corrThread ctaOf warpOf Launch.threads
  rw [hb] at *
  refine ⟨by nlinarith, by omega, by omega⟩

theorem corrThread_inj (L : Launch) (c : Nat) : Function.Injective (corrThread L c) := by
  intro a b h
  unfold corrThread at h
  exact Fin.ext (by omega)

/-- A correction thread of CTA `c` is one of its 128. -/
theorem corrThread_of (hpre : Pre P L mem0) {c g : Nat} (h : corrIn L c g) :
    ∃ a, g = corrThread L c a := by
  obtain ⟨-, hc, h8, h12⟩ := h
  have hb := hpre.block
  simp only [ctaOf, warpOf, hb] at hc h8 h12
  refine ⟨⟨g % 512 - 256, by omega⟩, ?_⟩
  unfold corrThread
  rw [hb]
  simp only
  omega

/-- A thread of CTA `c` is a launched thread when the arrival thread of `c` is. -/
theorem thread_lt_of_cta {g h : Nat} (hg : g < L.threads) (hc : ctaOf L h = ctaOf L g) :
    h < L.threads := by
  have := cta_lt hg
  unfold ctaOf Launch.threads at *
  rw [← hc] at this
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · rw [h0, Nat.mul_zero] at hg; omega
    · exact h0
  calc h < (h / L.block + 1) * L.block := by
        have := Nat.lt_div_mul_add (a := h) hb
        rw [Nat.add_mul, Nat.one_mul]
        exact this
    _ ≤ L.grid * L.block := Nat.mul_le_mul_right _ this

/-- **Stage `st`'s credit barrier of CTA `c` is a unit object** of the CTA's correction
threads. -/
theorem obj (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (htm : TmemFacts L X) (hinit : StatsInit L X) {c st : Nat} (hst : st < 2) :
    MbarRing.Unit.Obj X (statsBar L c st) 128 (corrThread L c) 1 where
  pos := by decide
  inj := corrThread_inj L c
  src r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (htm.no_inval he).elim
    | @arrive g j pc tx cnt rel sc hid he ha =>
      have hg := event_thread_lt hX he
      obtain ⟨h8, h12, hc, rfl, rfl, rfl⟩ := ht.credit_arrive hg hst he
      subst hc
      exact .arrive hid (corrThread_of hpre ⟨hg, rfl, h8, h12⟩) he ha
    | wait hid he ha => exact .poll hid he ha
    | tensor _ he hm _ => exact (ht.credit_tensor hst he hm).elim
    | increment _ he _ => exact (htm.no_arriveOn he).elim
    | arriveOn _ he _ _ _ => exact (htm.no_arriveOn he).elim
    | bulk _ he _ _ _ => exact (htm.no_bulk he).elim
    | commit _ he htg _ => exact (ht.credit_commit hst he htg).elim
    | clc _ he _ _ _ => exact (htm.no_clc he).elim
  init := hinit c st hst
  noInval := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => htm.no_inval he) _
  parity he := (ht.credit_poll (event_thread_lt hX he) hst he).2.2.2.1
  δ_le := le_refl 1

/-- **The gate path**: correction thread `a`'s credit arrival of use `s` is enabled by each
partner softmax lane's credit poll with `s` earlier successful ones. -/
theorem gate_path (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (hsoft : SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st : Nat} (hst : st < 2) {a : Fin 128} {h i pc : Nat} {sc : MbarScope}
    (hpair : softPair L c st a h)
    (he : X.get (corrThread L c a, i) = some ⟨pc, .arrive (statsBar L c st) 0 1 true sc⟩) :
    ∃ j pc' p acq sc', X.get (h, j) = some ⟨pc', .wait (statsBar L c st) p true acq sc'⟩ ∧
      okPolls (statsBar L c st) ((X.tr h).take j) + 1 =
        arrivals (statsBar L c st) ((X.tr (corrThread L c a)).take i) + 1 ∧
      Relation.TransGen (DepStep L K X) (.thread (h, j), true)
        (.thread (corrThread L c a, i), false) := by
  set g := corrThread L c a with hgdef
  set s := arrivals (statsBar L c st) ((X.tr g).take i) with hsdef
  have hg := event_thread_lt hX he
  obtain ⟨h8, h12, hcg, -⟩ := ht.credit_arrive hg hst he
  have hcl : c < L.grid := hcg ▸ cta_lt hg
  obtain ⟨-, hcg', hwg⟩ := corrThread_facts hpre hcl a
  set k := a.val / 32 with hkdef
  have hk : k < 4 := by have := a.isLt; omega
  have hid2 : statsId st k ≠ 2 := by unfold statsId; omega
  -- the correction's `bar.sync` of ordinal `s`
  have hcc := ht.corr_credit (g := g) (i := i) hg h8 h12 hst he (by rw [← hcg])
  rw [hwg, show 8 + k - 5 + 4 * st = statsId st k by unfold statsId; omega] at hcc
  obtain ⟨y, pcy, cnty, my, hyi, hyget, hyo⟩ :=
    exists_bar (X := X) (g := g) (x := i) (id := statsId st k) (c := s) (by omega)
  obtain ⟨hcy, st', k', hst', hk', hid', hw'⟩ := stats_of_bar ht hg hyget hid2
  obtain ⟨rfl, rfl⟩ := statsId_inj hk hk' hid'
  have hmy : my = .sync := by
    rcases hw' with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  subst hmy hcy
  have hf : X.IsBarrier (g, y) (statsId st k) (some 64) pcy := hyget
  have hpassed : y + 1 < (X.tr g).length := by have := len_of_get he; simp only at this; omega
  -- the partner softmax lane's arrival of ordinal `s`
  obtain ⟨hch, hwh⟩ := hpair
  have hh : h < L.threads := thread_lt_of_cta hg (by rw [hch, hcg'])
  obtain ⟨i', pc', cnt', md, hhget, hord⟩ := hsoft hst hk hf hpassed hh (by rw [hch, hcg'])
    (by omega)
  obtain ⟨hch', -, -, -, -, hidh, -⟩ := stats_of_bar ht hh hhget hid2
  subst hch'
  -- its credit poll with `s` earlier successful ones
  have hcr := ht.soft_credit hh (by omega) hhget hid2
  rw [show warpOf L h / 4 = st by omega, hch, hord, hyo] at hcr
  obtain ⟨j, pcw, p, acq, scw, hji, hw, hjq⟩ :=
    MbarRing.Poll.exists_nth (X := X) (m := statsBar L c st) (g := h) (k := i') (n := s)
      (by omega)
  have hnth : MbarRing.Poll.nth X (statsBar L c st) h s = j := by
    rw [← hjq, MbarRing.Poll.nth_eq hw]
  have g1 := MbarRing.Poll.guard (m := statsBar L c st) (g := h) (k := i') hspin
    (len_of_get hhget) (n := s) (by omega)
  rw [hnth] at g1
  -- the rendezvous of the arrival and the `bar.sync`
  have hS := sources ht (st := st) hk
  have hG := shape hpre hst hk
  have hsame : SameCta L h g := ⟨hh, hg, by
    unfold ctaOf at hch hcg'
    rw [hch, hcg']⟩
  have hke := hS.arrive_key_of_credit hX hG hhget hh hsame.2.2.symm hf hpassed
    (by unfold barOrd at hord; exact hord.symm)
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpassed
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  unfold barOrd at hord
  rw [hkey, ← hord] at hkf hdone
  obtain ⟨ic, hcomp⟩ := hdone
  -- the partner's arrival is a witness of the `bar.sync`'s return
  have hwit : Witness L X (.thread (h, i')) (g, y) :=
    Witness.of_ctaBarCounted hkf hcomp hke hsame.2.2
  have g2 : Resumes K X (g, y) (g, i) :=
    Resumes.of_blocking hyget (b := false) rfl ⟨rfl, hyi, len_of_get he⟩
  refine ⟨j, pcw, p, acq, scw, hw, by omega, ?_⟩
  exact ((Relation.TransGen.single (DepStep.of_resumes L g1)).tail
    (DepStep.of_witness L hwit)).tail (DepStep.of_resumes L g2)

/-- **Stage `st`'s credit barrier of CTA `c` is gated by the softmax polls.** -/
theorem gate (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (htm : TmemFacts L X) (hinit : StatsInit L X) (hsoft : SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit)
    {c st : Nat} (hst : st < 2) :
    MbarRing.Unit.Gate L K A X (statsBar L c st) 128 (corrThread L c) 1 (softIn L c st)
      (softPair L c st) where
  toObj := obj hpre hX ht htm hinit hst
  cover h hh := by
    obtain ⟨-, hc, hw8, hws⟩ := hh
    have hb := hpre.block
    refine ⟨⟨h % L.block % 128, by rw [hb]; omega⟩, hc, ?_⟩
    unfold warpOf at *
    rw [hb] at *
    simp only
    omega
  partner a := by
    have hb := hpre.block
    have ha := a.isLt
    refine ⟨c * L.block + (128 * st + a.val), ?_, ?_⟩ <;> simp only [ctaOf, warpOf, hb] <;>
      omega
  gate hpair he _ := gate_path hpre hX ht hsoft hspin hst hpair he
  acq hh he := (ht.credit_poll hh.1 hst he).2.2.2.2 rfl
  cta a h hh := by
    obtain ⟨hlt, hc, -, -⟩ := hh
    obtain ⟨hlt', hc', -⟩ := corrThread_facts hpre (hc ▸ cta_lt hlt) a
    exact ⟨hlt', hlt, by unfold ctaOf at hc hc'; rw [hc, hc']⟩

/-- **The statistics credit handoff** (`StatsCredit`). -/
theorem statsCredit (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (htm : TmemFacts L X) (hinit : StatsInit L X) (hsoft : SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit) :
    StatsCredit L X := fun _ _ hst =>
  MbarRing.UnitHandoff.mono ((gate hpre hX ht htm hinit hsoft hspin hst).handoff hX)
    (fun _ hg => corrThread_of hpre hg) (fun _ hh => hh)

/-- **Who blocks a softmax thread at its credit wait.** A softmax thread of stage `st` of CTA `c`
whose credit barrier ends in a phase of the parity its next poll does not find has polled
successfully once more than that phase, and some correction thread of the CTA has exactly that
phase's number of counted credit arrivals. -/
def CreditBlocked (L : Launch) (X : Execution) : Prop :=
  ∀ c st h, st < 2 → softIn L c st h → ∀ {before : MBarrier.State},
    MBarrier.stateBefore (X.objects (statsBar L c st)) (X.objects (statsBar L c st)).length =
      some before →
    before.phase % 2 = (okPolls (statsBar L c st) (X.tr h) + 1) % 2 →
      before.phase + 1 = okPolls (statsBar L c st) (X.tr h) ∧
        ∃ a, (X.objects (statsBar L c st)).countP
          (MbarRing.Unit.unitsOf (corrThread L c a)) = before.phase

theorem creditBlocked (hpre : Pre P L mem0) (hX : Consistent L K A mem0 X) (ht : StatsFacts L X)
    (htm : TmemFacts L X) (hinit : StatsInit L X) (hsoft : SoftArrives L X)
    (hspin : ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, K.CanonicalSpin pc exit) :
    CreditBlocked L X := fun _ _ _ hst hh _ hs hp =>
  (gate hpre hX ht htm hinit hsoft hspin hst).blocked hX hh hs hp

end Stats

end
end PTX.Kernels.FlashAttn4Fwd.Proof
