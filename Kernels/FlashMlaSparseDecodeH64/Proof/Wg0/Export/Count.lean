-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs

@[expose] public section

/-! # Warpgroup 0's arrival counts

-- domain: consistent

The count facts the channels take from warpgroup 0, for lane `b < 128` of CTA `c` (thread
`c * L.block + b`), each over the lane's events before its arrival:

* `wg0_coordArr` (`CoordInputs.wg0Arr`, `Protocol/Coord/Observe.lean`): an arrival on
  `coordFree s` (pc 571) follows more successful polls of `coordReady s` than earlier arrivals on
  `coordFree s`;
* `wg0_soArr` (`Protocol/Score/Obj.lean`, the score ring's W1 input): an arrival on `soReady s`
  (pc 1122) follows more successful polls of `qkDone s` than earlier arrivals on `soReady s`;
* `wg0_lastArr` (`Protocol/Close/Obj.lean`, no reuse): an arrival on `lastStoreDone` (pc 200) is
  the lane's first.

Each arrival is fired from a warpgroup-0 state (`wg0_at`) at one of the three arrival sites; the
reference invariant's counts there (`Wg0/Objs.lean`) are the lane's prefix counts
(`wg0_okPolls`, `wg0_arrivals`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The prefix counts as the ledger's. -/
private abbrev pre (X : Execution) (g i : Nat) : Wg0.Cnt → Nat :=
  fun c => ((X.tr g).take i).countP (Wg0.cls c)

/-- **An arrival of a warpgroup-0 lane** is at one of the three arrival sites, with the counts of
its place. -/
private theorem arr_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g i pc : Nat} {l : Loc} {tx c : Nat} {r : Bool} {sc : MbarScope}
    (hw : warp L g < 4) (he : X.get (g, i) = some ⟨pc, .arrive l tx c r sc⟩) :
    (l = loc L g .lastStoreDone ∧ Wg0.Counts (Wg0.objs L g) (pre X g i) false 0 0 none) ∨
      (∃ n, l = loc L g (.coordFree (slot4 n)) ∧
        Wg0.Counts (Wg0.objs L g) (pre X g i) true n 2 none) ∨
      (∃ n, l = loc L g (.soReady (slot2 n)) ∧
        Wg0.Counts (Wg0.objs L g) (pre X g i) true n 3 none) := by
  have hub : ∀ f, Kind.arrive l tx c r sc ≠ .ub f := fun _ h => by cases h
  have hin := wg0_inRole hp hX hFw hw he (.inr (.inr (.inr ⟨_, _, _, _, _, rfl⟩)))
  simp only [Wg0.inRole, decide_eq_true_eq] at hin
  obtain ⟨d, hR, ⟨hpc, hk⟩, -⟩ := wg0_at hp hX hFw he hub (by simp only; omega)
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  clear hR
  cases hs : d.site.mb
  · exact absurd (by simp only [Frame.MbarOf]) (Wg0.evK_noMbarOf hs hub hk (l := l))
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp only [Wg0.Site.mb, Bool.false_eq_true] at hs <;>
    simp only [Wg0.EvK, Wg0.ArrEv, Wg0.PollEv] at hk <;>
    simp only [Wg0.RefCore, Wg0.RefAt, Wg0.Site.reg, Wg0.Site.idx, Wg0.Control.D.words] at hc
  case arrL =>
    rcases hk with hk | ⟨f, hk⟩
    · simp only [Kind.arrive.injEq] at hk
      exact .inl ⟨hk.1.trans (Wg0.arr_loc hp), hc⟩
    · cases hk
  case arrV =>
    obtain ⟨n, ⟨-, -, -, -, -, hvs, -⟩, hn⟩ := hc
    rcases hk with hk | ⟨f, hk⟩
    · simp only [Kind.arrive.injEq] at hk
      simp only at hvs
      subst hvs
      exact .inr (.inl ⟨n, hk.1.trans (Wg0.vFree_loc hp (slot4 n)), hn⟩)
    · cases hk
  case arrS =>
    obtain ⟨n, ⟨-, -, -, -, -, -, -, hsl, -⟩, hn⟩ := hc
    rcases hk with hk | ⟨f, hk⟩
    · simp only [Kind.arrive.injEq] at hk
      simp only at hsl
      subst hsl
      exact .inr (.inr ⟨n, hk.1.trans (Wg0.so_loc hp (slot2 n)), hn⟩)
    · cases hk
  all_goals
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩ <;> cases hk

/-- Lane `b < 128` of CTA `c` is a warpgroup-0 lane of CTA `c`. -/
private theorem lane_facts (hp : Pre P L m) {c b : Nat} (hb : b < 128) :
    warp L (c * L.block + b) < 4 ∧ (c * L.block + b) / L.block = c := by
  simp only [warp, tidOf_x_eq hp, hp.block]
  omega

/-- **`CoordInputs.wg0Arr`**: a warpgroup-0 lane's arrival on `coordFree s` follows more
successful polls of `coordReady s` than its earlier arrivals on `coordFree s`. -/
theorem wg0_coordArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c i pc b : Nat} {s : Fin 4} {sc : MbarScope} (hb : b < 128)
    (he : X.get (c * L.block + b, i) =
      some ⟨pc, .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.coordFree s)) ((X.tr (c * L.block + b)).take i) <
      okPolls (mbarLoc L c (.coordReady s)) ((X.tr (c * L.block + b)).take i) := by
  obtain ⟨hw, hc⟩ := lane_facts hp (c := c) hb
  have hloc : ∀ f, mbarLoc L c f = loc L (c * L.block + b) f := fun f => by rw [loc, hc]
  rw [hloc, hloc, wg0_arrivals hp hX hFw hw, wg0_okPolls hp hX hFw hw]
  rw [hloc] at he
  rcases arr_place hp hX hFw hw he with ⟨hl, -⟩ | ⟨n, hl, hq, ha⟩ | ⟨n, hl, -⟩
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · obtain rfl : s = slot4 n := MbarFam.coordFree.inj (Wg0.loc_inj.mp hl)
    have h1 := ha (loc L (c * L.block + b) (.coordFree (slot4 n)))
    have h2 := hq (loc L (c * L.block + b) (.coordReady (slot4 n)))
    dsimp only [pre] at h1 h2
    rw [h1, h2, Wg0.arr_free hp, Wg0.acq_ready hp]
    simp [Wg0.use, Wg0.ind, slot4]
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)

/-- **The score ring's W1 input**: a warpgroup-0 lane's arrival on `soReady s` follows more
successful polls of `qkDone s` than its earlier arrivals on `soReady s`. -/
theorem wg0_soArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c i pc b : Nat} {s : Fin 2} {sc : MbarScope} (hb : b < 128)
    (he : X.get (c * L.block + b, i) =
      some ⟨pc, .arrive (mbarLoc L c (.soReady s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.soReady s)) ((X.tr (c * L.block + b)).take i) <
      okPolls (mbarLoc L c (.qkDone s)) ((X.tr (c * L.block + b)).take i) := by
  obtain ⟨hw, hc⟩ := lane_facts hp (c := c) hb
  have hloc : ∀ f, mbarLoc L c f = loc L (c * L.block + b) f := fun f => by rw [loc, hc]
  rw [hloc, hloc, wg0_arrivals hp hX hFw hw, wg0_okPolls hp hX hFw hw]
  rw [hloc] at he
  rcases arr_place hp hX hFw hw he with ⟨hl, -⟩ | ⟨n, hl, -⟩ | ⟨n, hl, hq, ha⟩
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · obtain rfl : s = slot2 n := MbarFam.soReady.inj (Wg0.loc_inj.mp hl)
    have h1 := ha (loc L (c * L.block + b) (.soReady (slot2 n)))
    have h2 := hq (loc L (c * L.block + b) (.qkDone (slot2 n)))
    dsimp only [pre] at h1 h2
    rw [h1, h2, Wg0.arr_so hp, Wg0.acq_qk hp]
    simp [Wg0.use, Wg0.ind, slot2]

/-- **The block of a softmax-ready arrival**: a warpgroup-0 lane's arrival on `soReady s` is
block `n`'s, `s = n % 2`, and its earlier arrivals on both slots are the uses before block `n`. -/
theorem wg0_soArrBlk (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c i pc b : Nat} {s : Fin 2} {sc : MbarScope} (hb : b < 128)
    (he : X.get (c * L.block + b, i) =
      some ⟨pc, .arrive (mbarLoc L c (.soReady s)) 0 1 true sc⟩) :
    ∃ n, s = slot2 n ∧ ∀ s' : Fin 2, arrivals (mbarLoc L c (.soReady s'))
      ((X.tr (c * L.block + b)).take i) = ringUses 2 s' n := by
  obtain ⟨hw, hc⟩ := lane_facts hp (c := c) hb
  have hloc : ∀ f, mbarLoc L c f = loc L (c * L.block + b) f := fun f => by rw [loc, hc]
  rw [hloc] at he
  rcases arr_place hp hX hFw hw he with ⟨hl, -⟩ | ⟨n, hl, -⟩ | ⟨n, hl, -, ha⟩
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · obtain rfl : s = slot2 n := MbarFam.soReady.inj (Wg0.loc_inj.mp hl)
    refine ⟨n, rfl, fun s' => ?_⟩
    have h1 := ha (loc L (c * L.block + b) (.soReady s'))
    dsimp only [pre] at h1
    rw [hloc, wg0_arrivals hp hX hFw hw, h1, Wg0.arr_so hp]

/-- **No reuse of the last store's barrier**: a warpgroup-0 lane's arrival on `lastStoreDone` is
its first. -/
theorem wg0_lastArr (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {c i pc b : Nat} {sc : MbarScope} (hb : b < 128)
    (he : X.get (c * L.block + b, i) =
      some ⟨pc, .arrive (mbarLoc L c .lastStoreDone) 0 1 true sc⟩) :
    arrivals (mbarLoc L c .lastStoreDone) ((X.tr (c * L.block + b)).take i) = 0 := by
  obtain ⟨hw, hc⟩ := lane_facts hp (c := c) hb
  have hloc : ∀ f, mbarLoc L c f = loc L (c * L.block + b) f := fun f => by rw [loc, hc]
  rw [hloc, wg0_arrivals hp hX hFw hw]
  rw [hloc] at he
  rcases arr_place hp hX hFw hw he with ⟨-, -, ha⟩ | ⟨n, hl, -⟩ | ⟨n, hl, -⟩
  · have h1 := ha (loc L (c * L.block + b) .lastStoreDone)
    dsimp only [pre] at h1
    rw [h1]
    simp [Wg0.arrCnt, Wg0.use, Wg0.ind, ringUses]
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)
  · exact absurd (Wg0.loc_inj.mp hl) (by simp)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
