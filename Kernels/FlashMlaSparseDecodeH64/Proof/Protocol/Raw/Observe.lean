-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Raw.Obj
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.UnitCounted
public import Lemmas.Protocol.UnitItems
public import Lemmas.Protocol.PairTmaRing.Order
public import Lemmas.Order.WaitOrderEnables

@[expose] public section

/-! # What the raw ring's waits observe

Slot `s` of the raw ring of CTA `c` is a slot of a one-CTA ring of kinds (`MbarRing.KRing`,
library pattern `KindRing`): full barrier `rawReady s` (`rawReady_obj`, seventeen kinds: the TMA
lane's arrival and its sixteen loads of a use), empty barrier `rawFree s` (`rawFree_obj`, one
notification per dequant lane: its unit arrival), one producer (the TMA lane) and 128 consumers
(the dequant lanes). Then, from the acyclicity of the dependency order alone:

* `rawReady_observes`: a dequant lane's successful poll of `rawReady s` with `u` earlier ones
  observes the TMA lane's arrival of use `u` on it and its sixteen loads `16 u + a`;
* `rawFree_observes`: the TMA lane's successful poll of `rawFree s` with `u + 1` earlier ones
  observes every dequant lane's arrival of use `u` on it.

**Inputs** (`RawInputs`, trace counts of the lanes' own events; the machines run one block per
loop trip, block `t` on slot `t % 2`, its free wait before its loads and arrival, its ready wait
before its free arrival): the TMA lane's arrival and loads on `rawReady s` follow more successful
polls of `rawFree s` than their use (`tmaArr`, `tmaIss`), a dequant lane's arrival on `rawFree s`
more successful polls of `rawReady s` than its use (`deqArr`); and one TMA lane per CTA (`tmaOne`).

**Lag** (not here): the ring's blocked waits need, as `QueryTime`, the TMA lane's and the dequant
lanes' slot-waiter facts (a lane waiting at 2245 / 2677 has made its block's earlier arrivals) and
the fault-freedom of both objects (`TmaUnits.Gated` from `KRing.reachF`, `Unit.Gate` from
`KRing.reachE`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section

set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The inputs of the raw ring.** -/
structure RawInputs (L : Launch) (X : Execution) : Prop where
  /-- One TMA lane per CTA (lane A, `Iface/Elect/Tma.lean`). -/
  tmaOne : TmaOne L X
  /-- The TMA lane's arrival on `rawReady s` follows more successful polls of `rawFree s` than
  its earlier arrivals on `rawReady s` (lane A). -/
  tmaArr : ∀ {c i pc tx cnt : Nat} {s : Fin 2} {rel : Bool} {sc : MbarScope},
    X.get (tmaThread L X c, i) = some ⟨pc, .arrive (mbarLoc L c (.rawReady s)) tx cnt rel sc⟩ →
    arrivals (mbarLoc L c (.rawReady s)) ((X.tr (tmaThread L X c)).take i) <
      okPolls (mbarLoc L c (.rawFree s)) ((X.tr (tmaThread L X c)).take i)
  /-- The TMA lane's load on `rawReady s` follows more than a sixteenth of its earlier loads
  on `rawReady s` successful polls of `rawFree s` (lane A). -/
  tmaIss : ∀ {c i pc al : Nat} {s : Fin 2} {sp : TensorCopy.Spec},
    X.get (tmaThread L X c, i) = some ⟨pc, .tensorIssue al sp⟩ →
    sp.mbar = mbarLoc L c (.rawReady s) →
    ((X.tr (tmaThread L X c)).take i).countP (issuesTo (mbarLoc L c (.rawReady s))) <
      16 * okPolls (mbarLoc L c (.rawFree s)) ((X.tr (tmaThread L X c)).take i)
  /-- A dequant lane's arrival on `rawFree s` follows more successful polls of `rawReady s` than
  its earlier arrivals on `rawFree s` (lane D). -/
  deqArr : ∀ {c i pc : Nat} {s : Fin 2} {b : Fin 128} {sc : MbarScope},
    X.get (deqLane L c b, i) = some ⟨pc, .arrive (mbarLoc L c (.rawFree s)) 0 1 true sc⟩ →
    arrivals (mbarLoc L c (.rawFree s)) ((X.tr (deqLane L c b)).take i) <
      okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take i)

/-- A successful poll of `rawReady s` has the parity of its thread's earlier successful polls. -/
theorem rawReady_parity (hR : MbarRows P L X) (hX : Consistent L kernel Assumptions.all m X)
    {c g k pc p : Nat} {s : Fin 2} {acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait (mbarLoc L c (.rawReady s)) p true acq sc⟩) :
    p % 2 = (okPolls (mbarLoc L c (.rawReady s)) ((X.tr g).take k) + 0) % 2 := by
  rcases rawReady_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
    ⟨-, -, -, ⟨_, _, hk, -⟩ | hk⟩ | ⟨-, -, ⟨ok, hk⟩⟩
  · cases hk
  · cases hk
  · cases hk
  · simp only [Kind.wait.injEq] at hk
    obtain ⟨-, rfl, -⟩ := hk
    exact Nat.mod_mod _ _

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : RawInputs L X)
include hp hX hFw hR hI hB hN

/-- The TMA lane's item of use `t` on `rawReady s` follows `t + 1` successful polls of
`rawFree s`. -/
theorem rawSlot_polF {c : Nat} {s : Fin 2} {x : Fin 17 × Nat}
    (hx : x ∈ TmaUnits.S X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 2304) :
    ∃ i, TmaUnits.op X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 x.1 x.2 =
        (tmaThread L X c, i) ∧ i < (X.tr (tmaThread L X c)).length ∧
      x.2 + 1 ≤ okPolls (mbarLoc L c (.rawFree s)) ((X.tr (tmaThread L X c)).take i) := by
  have o := rawReady_obj hp hX hFw hR hI hB hN.tmaOne c s
  obtain ⟨-, h0, h1⟩ := o.source hx
  generalize hi : TmaUnits.op X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 x.1 x.2 = w
    at h0 h1
  obtain ⟨y, i⟩ := w
  have hy : y = tmaThread L X c := (congrArg Prod.fst hi).symm
  subst hy
  refine ⟨i, rfl, ?_⟩
  by_cases hz : x.1.val = 0
  · obtain ⟨⟨pc, rel, sc, hget⟩, hcnt⟩ := h0 hz
    have := hN.tmaArr hget
    exact ⟨len_of_get hget, by simp only at hcnt; omega⟩
  · obtain ⟨⟨pc, al, sp, hget, hm⟩, hcnt⟩ := h1 hz
    have := hN.tmaIss hget hm
    exact ⟨len_of_get hget, by simp only at hcnt; omega⟩

/-- **Slot `s` of the raw ring of CTA `c`** as a ring of kinds. -/
def rawSlot (c : Nat) (s : Fin 2) : KRing L kernel X 1 128 17 :=
  have o := rawReady_obj hp hX hFw hR hI hB hN.tmaOne c s
  have N := rawFree_obj hp hX hFw hR hI hB c s
  { F := mbarLoc L c (.rawReady s)
    E := mbarLoc L c (.rawFree s)
    prod := fun _ => tmaThread L X c
    cons := deqLane L c
    ownF := fun _ => 0
    opF := TmaUnits.op X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16
    itF := TmaUnits.it X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16
    cm := Unit.it X (mbarLoc L c (.rawFree s)) (deqLane L c)
    note := Unit.itRef X (mbarLoc L c (.rawFree s)) (deqLane L c)
    SF := TmaUnits.S X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 2304
    SE := Unit.S X (mbarLoc L c (.rawFree s)) (deqLane L c)
    cover := fun _ => ⟨0, Subsingleton.elim _ _⟩
    cF := o.counted
    cE := N.counted
    spins := fun _ _ _ _ _ _ he => poll_canonical hX he
    parF := fun _ _ _ _ _ _ he => rawReady_parity hR hX he
    parE := fun _ _ _ _ _ _ he => N.parity he
    fullF := fun _ _ hj => o.card_phase hX (by decide) (by decide) (δ := 0) (Nat.zero_le _)
      (MbarRing.Poll.alternates hX (o.counted.pclean hX) fun _ _ _ _ _ he =>
        rawReady_parity hR hX he) (Nat.zero_le _) hj
    fullE := fun _ _ hn hj => N.card_phase hX hn hj
    polF := fun _ hx => rawSlot_polF hp hX hFw hR hI hB hN hx
    polE := fun _ hy => N.pol (fun h => hN.deqArr h) hy
    issueF := fun _ hx => o.issue hX hx
    issueE := fun _ _ => .refl }

/-- **The raw wait observes the block.** A successful poll of `rawReady s` of CTA `c` with `u`
earlier ones is a dequant lane's, and it observes the TMA lane's arrival of use `u` on it,
expecting 36864 bytes, and its sixteen loads `16 u + a` of 2304 bytes. -/
theorem rawReady_observes {c : Nat} {s : Fin 2} {h j pc p : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c (.rawReady s)) p true acq sc⟩) :
    (∃ b, h = deqLane L c b) ∧
      (∃ i pc' rel sc', X.get (tmaThread L X c, i) =
          some ⟨pc', .arrive (mbarLoc L c (.rawReady s)) 36864 1 rel sc'⟩ ∧
        arrivals (mbarLoc L c (.rawReady s)) ((X.tr (tmaThread L X c)).take i) =
          okPolls (mbarLoc L c (.rawReady s)) ((X.tr h).take j) ∧
        WaitObserves X (.thread (tmaThread L X c, i)) (h, j) (mbarLoc L c (.rawReady s)) acq sc) ∧
      ∀ a : Fin 16, ∃ i pc' al sp, X.get (tmaThread L X c, i) = some ⟨pc', .tensorIssue al sp⟩ ∧
        sp.mbar = mbarLoc L c (.rawReady s) ∧ TensorTransfer.bytes sp.descriptor = 2304 ∧
        ((X.tr (tmaThread L X c)).take i).countP (issuesTo (mbarLoc L c (.rawReady s))) =
          16 * okPolls (mbarLoc L c (.rawReady s)) ((X.tr h).take j) + a.val ∧
        WaitObserves X (.async (tmaThread L X c, i) (.notify .load)) (h, j)
          (mbarLoc L c (.rawReady s)) acq sc := by
  have hb : ∃ b, h = deqLane L c b := by
    rcases rawReady_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
      ⟨-, -, -, ⟨_, _, hk, -⟩ | hk⟩ | ⟨hw, hc, -⟩
    · cases hk
    · cases hk
    · cases hk
    · obtain ⟨b, hb⟩ := deq_lane hp hw
      exact ⟨b, hc ▸ hb⟩
  obtain ⟨b, rfl⟩ := hb
  have o := rawReady_obj hp hX hFw hR hI hB hN.tmaOne c s
  have hu := PairTmaRing.okPolls_lt_of_get he
  have obs : ∀ k : Fin 17, (k, okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j))
      ∈ TmaUnits.S X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 2304 ∧
      MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.rawReady s)))
        (TmaUnits.it X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 k
          (okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j)))
        (.thread (deqLane L c b, j)) := fun k => by
    obtain ⟨hS, hub⟩ := (rawSlot hp hX hFw hR hI hB hN c s).full_observes hX (b := b) hu k
    have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.rawReady s)))
        (TmaUnits.it X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 k
          (okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j)))
        (.thread (deqLane L c b, MbarRing.Poll.nth X (mbarLoc L c (.rawReady s)) (deqLane L c b)
          (okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j)))) := hub
    rw [MbarRing.Poll.nth_eq he] at hub'
    exact ⟨hS, hub'⟩
  refine ⟨⟨b, rfl⟩, ?_, fun a => ?_⟩
  · obtain ⟨hS, hub⟩ := obs 0
    obtain ⟨-, h0, -⟩ := o.source hS
    obtain ⟨⟨pc', rel, sc', hget⟩, hcnt⟩ := h0 rfl
    refine ⟨(TmaUnits.op X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 0
      (okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j))).2, pc', rel, sc',
      hget, hcnt, ⟨pc, p, he⟩, ?_⟩
    simp only [TmaUnits.it, Fin.val_zero, ↓reduceIte] at hub
    exact hub
  · obtain ⟨hS, hub⟩ := obs a.succ
    obtain ⟨-, -, h1⟩ := o.source hS
    obtain ⟨⟨pc', al, sp, hget, hm⟩, hcnt⟩ := h1 (by simp)
    have hby : TensorTransfer.bytes sp.descriptor = 2304 := by
      rcases rawReady_use hR (Frame.lt_of_get hX hget) hget hm with ⟨n, hk⟩ |
        ⟨-, -, -, ⟨_, _, hk, -, hb⟩ | hk⟩ | ⟨-, -, ⟨ok, hk⟩⟩
      · cases hk
      · simp only [Kind.tensorIssue.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact hb
      · cases hk
      · cases hk
    refine ⟨(TmaUnits.op X (mbarLoc L c (.rawReady s)) (tmaThread L X c) 16 a.succ
      (okPolls (mbarLoc L c (.rawReady s)) ((X.tr (deqLane L c b)).take j))).2, pc', al, sp,
      hget, hm, hby, hcnt.trans (by simp), ⟨pc, p, he⟩, ?_⟩
    simp only [TmaUnits.it, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      ↓reduceIte] at hub
    exact hub

/-- **The free wait observes the block's release.** A successful poll of `rawFree s` of CTA `c`
with `u + 1` earlier ones is the TMA lane's, and it observes every dequant lane's arrival of use
`u` on it. -/
theorem rawFree_observes {c : Nat} {s : Fin 2} {h j pc p u : Nat} {acq : Bool} {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c (.rawFree s)) p true acq sc⟩)
    (hj : okPolls (mbarLoc L c (.rawFree s)) ((X.tr h).take j) = u + 1) :
    h = tmaThread L X c ∧ ∀ b : Fin 128, ∃ i pc' sc', X.get (deqLane L c b, i) =
        some ⟨pc', .arrive (mbarLoc L c (.rawFree s)) 0 1 true sc'⟩ ∧
      arrivals (mbarLoc L c (.rawFree s)) ((X.tr (deqLane L c b)).take i) = u ∧
      WaitObserves X (.thread (deqLane L c b, i)) (h, j) (mbarLoc L c (.rawFree s)) acq sc := by
  have hh : h = tmaThread L X c := by
    rcases rawFree_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ |
      ⟨hw, hu, hc, -⟩ | ⟨-, -, hk⟩
    · cases hk
    · have := tma_thread_eq hN.tmaOne he (notUb_of_kind (mbar_kind hX hR he rfl)) hw hu
      rwa [hc] at this
    · cases hk
  subst hh
  have N := rawFree_obj hp hX hFw hR hI hB c s
  have hu := PairTmaRing.okPolls_lt_of_get he
  rw [hj] at hu
  refine ⟨rfl, fun b => ?_⟩
  obtain ⟨hS, hub⟩ := (rawSlot hp hX hFw hR hI hB hN c s).empty_observes hX (a := 0) hu b
  have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.rawFree s)))
      (.thread (Unit.it X (mbarLoc L c (.rawFree s)) (deqLane L c) b u))
      (.thread (tmaThread L X c, MbarRing.Poll.nth X (mbarLoc L c (.rawFree s)) (tmaThread L X c)
        (u + 1))) := hub
  rw [← hj, MbarRing.Poll.nth_eq he] at hub'
  exact N.wait_obs hS he hub'

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
