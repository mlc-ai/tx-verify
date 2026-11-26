-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.StaticPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.InitFirst
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.Mbar.TmaLane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.MbarUse.UnitObj
public import Lemmas.Protocol.KindRing
public import Lemmas.Protocol.PairTmaRing.Order
public import Lemmas.Protocol.UnitCounted

@[expose] public section

/-! # What the index ring's waits observe

Slot `s` of the index ring of CTA `c` is a slot of a one-CTA ring of kinds (`MbarRing.KRing`,
library pattern `KindRing`): full barrier `coordReady s` (`coordReady_obj`, 32 kinds: the index
lanes' unit arrivals), empty barrier `coordFree s` (`coordFree_obj`, one notification per
consumer: its unit arrival), 32 producers (the index lanes) and 129 consumers (warpgroup 0's 128
lanes and the TMA thread, `coordCons`). Then, from the acyclicity of the dependency order alone:

* `coordReady_observes`: a consumer's successful poll of `coordReady s` with `u` earlier ones
  observes every index lane's arrival of use `u` on it;
* `coordFree_observes`: an index lane's successful poll of `coordFree s` with `u + 1` earlier ones
  observes every consumer's arrival of use `u` on it.

The instance needs no case split on role state (risk 3): the consumers are fixed threads
(`coordCons`), and the TMA lane enters only through `TmaOne` and the counts below.

**Inputs** (`CoordInputs`, trace counts of the lanes' own events; block `t` uses slot `t % 4`, the
index lanes wait for its free slot before they arrive on its ready barrier, the consumers wait
for the ready barrier before they free it): an index lane's arrival on `coordReady s` follows more
successful polls of `coordFree s` than its earlier arrivals on `coordReady s` (`idxArr`), and a
consumer's arrival on `coordFree s` more successful polls of `coordReady s` than its earlier
arrivals on `coordFree s` (`wg0Arr`, `tmaArr`); and one TMA lane per CTA (`tmaOne`).

**Lag** (not here): the blocked waits at 264, 2234, 2446 and 2534 need, as `QueryTime`, each
lane's slot-waiter fact (a lane waiting on a slot has made its arrivals of the earlier uses of the
slot) and the fault-freedom of both objects (`Unit.Gate`, from `KRing.reachF` / `reachE`). -/

/-! # The index ring's barriers as objects

From `mbar_use` and the rows only. Slot `s` of the four-slot index ring of CTA `c` has two
barriers:

* `coordReady s` is named by the startup's initialization (count 32), the 32 index lanes' unit
  arrivals (pcs 2476, 2565; `idxLane L c a`, warp 7), and the polls of its consumers with the
  parity of their earlier successful polls: the 128 lanes of warpgroup 0 (pc 264) and the TMA
  lane (pc 2234) (`coordReady_use`). It is a `MbarRing.Unit.Obj` of the index lanes, polled with
  offset 0 (`coordReady_obj`; library pattern `UnitObject`).
* `coordFree s` is named by the initialization (count 129), the unit arrivals of the 129
  consumers (warpgroup 0 at pc 571, the TMA lane at pc 2308), and the index lanes' polls (pcs
  2446, 2534) with the parity of their earlier successful polls plus one (`coordFree_use`). It is
  a unit object of the consumers `coordCons L X c b` (`b < 128`: thread `b` of warpgroup 0;
  `b = 128`: `tmaThread`), polled with offset 1 (`coordFree_obj`).

The ring needs no case split on role state: the 129th producer is `tmaThread`, a warp-5 thread
of the CTA whether or not the CTA has a TMA lane, so the producers are distinct threads
(`coordCons_inj`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- Index lane `a` of CTA `c` (warp 7). -/
def idxLane (L : Launch) (c : Nat) (a : Fin 32) : Nat := c * L.block + 224 + a.val

/-- Consumer `b` of the index ring of CTA `c`: lane `b` of warpgroup 0, or the TMA thread. -/
def coordCons (L : Launch) (X : Execution) (c : Nat) (b : Fin 129) : Nat :=
  if b.val < 128 then c * L.block + b.val else tmaThread L X c

theorem idxLane_inj (L : Launch) (c : Nat) : Function.Injective (idxLane L c) := by
  intro a b h
  simp only [idxLane] at h
  exact Fin.ext (by omega)

theorem coordCons_inj (hp : Pre P L m) (c : Nat) : Function.Injective (coordCons L X c) := by
  intro a b h
  have ht := tmaThread_mod (X := X) hp c
  simp only [coordCons, hp.block] at h
  refine Fin.ext ?_
  split at h <;> split at h <;> omega

/-- **A warp-7 lane is an index lane of its CTA.** -/
theorem idx_lane (hp : Pre P L m) {g pc : Nat} (hw : MbarRow.IndexAt L g pc) :
    ∃ a, g = idxLane L (g / L.block) a := by
  obtain ⟨h7, -, -⟩ := hw
  simp only [MbarRow.warp, tidOf_x_eq hp] at h7
  refine ⟨⟨g % 384 - 224, by omega⟩, ?_⟩
  simp only [idxLane, hp.block]
  omega

/-- The consumer lanes of the index ring: warpgroup 0, or the TMA row's lane. -/
def CoordConsAt (L : Launch) (X : Execution) (g k : Nat) (e : Event) (l : Loc) : Prop :=
  MbarRow.Wg0At L g e.pc ∨ MbarRow.TmaAt L g e.pc ∧ MbarRow.TmaUse L X g k e l

/-- **A consumer lane is a consumer of its CTA's index ring.** -/
theorem coord_cons (hp : Pre P L m) (hO : TmaOne L X) {g k : Nat} {e : Event} {l : Loc}
    (he : X.get (g, k) = some e) (hn : ∀ f, e.kind ≠ .ub f) (hw : CoordConsAt L X g k e l) :
    ∃ b, g = coordCons L X (g / L.block) b := by
  rcases hw with ⟨h4, -, -⟩ | ⟨hw, hu⟩
  · simp only [MbarRow.warp, tidOf_x_eq hp] at h4
    refine ⟨⟨g % 384, by omega⟩, ?_⟩
    simp only [coordCons, hp.block, show g % 384 < 128 from by omega, ↓reduceIte]
    omega
  · refine ⟨⟨128, by omega⟩, ?_⟩
    simp only [coordCons, show ¬ (128 < 128) from by omega, ↓reduceIte]
    exact tma_thread_eq hO he hn hw hu

/-- **The uses of `coordReady s` of CTA `c`**: the initialization, a consumer's poll with the
parity of its earlier successful polls, or an index lane's unit arrival. -/
theorem coordReady_use (hR : MbarRows P L X) {c g k : Nat} {s : Fin 4} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c (.coordReady s))) :
    (∃ n, e.kind = .mbInit (mbarLoc L c (.coordReady s)) n) ∨
      ((∃ q, MbarRow.Wait e (mbarLoc L c (.coordReady s)) q ∧
          q % 2 = (okPolls (mbarLoc L c (.coordReady s)) ((X.tr g).take k) + 0) % 2) ∧
        g / L.block = c ∧ CoordConsAt L X g k e (mbarLoc L c (.coordReady s))) ∨
      MbarRow.IndexAt L g e.pc ∧ g / L.block = c ∧
        MbarRow.Arrive e (mbarLoc L c (.coordReady s)) 0 := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨hw, h⟩ | ⟨-, h⟩ | ⟨hw, h⟩ |
    ⟨hw, h⟩ | ⟨-, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | qkDone _ hl _ | coordFree _ hl _ | soReady _ hl _ | svDone _ hl _ =>
      nomatch (fam_eq hl).2
    | coordReady _ hl hk =>
      exact .inr (.inl ⟨⟨_, hk, by omega⟩, (fam_eq hl).1.symm, .inl hw⟩)
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | freeWait _ hl _ | rawLoad _ hl _ | rawArrive _ hl _
    | coordFree _ hl _ => nomatch (fam_eq hl).2
    | coordWait hpc hl hk =>
      exact .inr (.inl ⟨⟨_, hk, by omega⟩, (fam_eq hl).1.symm,
        .inr ⟨hw, .coordWait hpc hl hk⟩⟩)
  · cases h with
    | freeWait _ hl _ => nomatch (fam_eq hl).2
    | readyArrive _ hl hk => exact .inr (.inr ⟨hw, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2

/-- **The uses of `coordFree s` of CTA `c`**: the initialization, an index lane's poll with the
parity of its earlier successful polls plus one, or a consumer's unit arrival. -/
theorem coordFree_use (hR : MbarRows P L X) {c g k : Nat} {s : Fin 4} {e : Event}
    (hg : g < L.threads) (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (mbarLoc L c (.coordFree s))) :
    (∃ n, e.kind = .mbInit (mbarLoc L c (.coordFree s)) n) ∨
      ((∃ q, MbarRow.Wait e (mbarLoc L c (.coordFree s)) q ∧
          q % 2 = (okPolls (mbarLoc L c (.coordFree s)) ((X.tr g).take k) + 1) % 2) ∧
        g / L.block = c ∧ MbarRow.IndexAt L g e.pc) ∨
      CoordConsAt L X g k e (mbarLoc L c (.coordFree s)) ∧ g / L.block = c ∧
        MbarRow.Arrive e (mbarLoc L c (.coordFree s)) 0 := by
  rcases mbar_use hR hg he hm with ⟨-, ⟨-, j, -, -, hk⟩⟩ | ⟨hw, h⟩ | ⟨-, h⟩ | ⟨hw, h⟩ |
    ⟨hw, h⟩ | ⟨-, h⟩
  · exact .inl ⟨_, hk⟩
  · cases h with
    | lastStore _ hl _ | qkDone _ hl _ | coordReady _ hl _ | soReady _ hl _ | svDone _ hl _ =>
      nomatch (fam_eq hl).2
    | coordFree _ hl hk => exact .inr (.inr ⟨.inl hw, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | qLoad _ hl _ | qArrive _ hl _ | qWait _ hl _ _ | qCommit _ hl _ | qCopyWait _ hl _ _
    | kvWait _ hl _ | qkCommit _ hl _ | soWait _ hl _ | svCommit _ hl _ => nomatch (fam_eq hl).2
  · cases h with
    | qWait _ hl _ _ | lastWait _ hl _ _ | freeWait _ hl _ | rawLoad _ hl _ | rawArrive _ hl _
    | coordWait _ hl _ => nomatch (fam_eq hl).2
    | coordFree hpc hl hk =>
      exact .inr (.inr ⟨.inr ⟨hw, .coordFree hpc hl hk⟩, (fam_eq hl).1.symm, hk⟩)
  · cases h with
    | readyArrive _ hl _ => nomatch (fam_eq hl).2
    | freeWait _ hl hk => exact .inr (.inl ⟨⟨_, hk, Nat.mod_mod _ _⟩, (fam_eq hl).1.symm, hw⟩)
  · cases h with
    | qWait _ hl _ _ | rawWait _ hl _ | svWait _ hl _ | readyArrive _ hl _ | freeArrive _ hl _ =>
      nomatch (fam_eq hl).2

/-- **`coordReady s` of CTA `c` is a unit object of the CTA's 32 index lanes**, polled with
offset 0. -/
theorem coordReady_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (c : Nat) (s : Fin 4) :
    Unit.Obj X (mbarLoc L c (.coordReady s)) 32 (idxLane L c) 0 :=
  unit_of_uses hX hR (by decide) (idxLane_inj L c) (Nat.zero_le _)
    (initFirst hp hX hFw hR hI hB c (.coordReady s)) fun he hm => by
    rcases coordReady_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨hk, -, -⟩ | ⟨hw, hc, hk⟩
    · exact .inl hk
    · exact .inr (.inl hk)
    · obtain ⟨a, ha⟩ := idx_lane hp hw
      rw [hc] at ha
      exact .inr (.inr ⟨⟨a, ha⟩, hk⟩)

/-- **`coordFree s` of CTA `c` is a unit object of the CTA's 129 consumers**, polled with
offset 1. -/
theorem coordFree_obj (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X)
    (hO : TmaOne L X) (c : Nat) (s : Fin 4) :
    Unit.Obj X (mbarLoc L c (.coordFree s)) 129 (coordCons L X c) 1 :=
  unit_of_uses hX hR (by decide) (coordCons_inj hp c) le_rfl
    (initFirst hp hX hFw hR hI hB c (.coordFree s)) fun he hm => by
    rcases coordFree_use hR (Frame.lt_of_get hX he) he hm with hk | ⟨hk, -, -⟩ | ⟨hw, hc, hk⟩
    · exact .inl hk
    · exact .inr (.inl hk)
    · obtain ⟨b, hb⟩ := coord_cons hp hO he (notUb_of_kind (mbar_kind hX hR he hm)) hw
      rw [hc] at hb
      exact .inr (.inr ⟨⟨b, hb⟩, hk⟩)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow PTX.MbarRing PTX.AsyncCopy

noncomputable section
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The inputs of the index ring.** -/
structure CoordInputs (L : Launch) (X : Execution) : Prop where
  /-- One TMA lane per CTA (lane A, `Iface/Elect/Tma.lean`). -/
  tmaOne : TmaOne L X
  /-- An index lane's arrival on `coordReady s` follows more successful polls of `coordFree s`
  than its earlier arrivals on `coordReady s` (lane A). -/
  idxArr : ∀ {c i pc : Nat} {s : Fin 4} {a : Fin 32} {sc : MbarScope},
    X.get (idxLane L c a, i) = some ⟨pc, .arrive (mbarLoc L c (.coordReady s)) 0 1 true sc⟩ →
    arrivals (mbarLoc L c (.coordReady s)) ((X.tr (idxLane L c a)).take i) <
      okPolls (mbarLoc L c (.coordFree s)) ((X.tr (idxLane L c a)).take i)
  /-- A warpgroup-0 lane's arrival on `coordFree s` follows more successful polls of
  `coordReady s` than its earlier arrivals on `coordFree s` (lane W1). -/
  wg0Arr : ∀ {c i pc b : Nat} {s : Fin 4} {sc : MbarScope}, b < 128 →
    X.get (c * L.block + b, i) = some ⟨pc, .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc⟩ →
    arrivals (mbarLoc L c (.coordFree s)) ((X.tr (c * L.block + b)).take i) <
      okPolls (mbarLoc L c (.coordReady s)) ((X.tr (c * L.block + b)).take i)
  /-- The TMA thread's arrival on `coordFree s` follows more successful polls of `coordReady s`
  than its earlier arrivals on `coordFree s` (lane A). -/
  tmaArr : ∀ {c i pc : Nat} {s : Fin 4} {sc : MbarScope},
    X.get (tmaThread L X c, i) = some ⟨pc, .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc⟩ →
    arrivals (mbarLoc L c (.coordFree s)) ((X.tr (tmaThread L X c)).take i) <
      okPolls (mbarLoc L c (.coordReady s)) ((X.tr (tmaThread L X c)).take i)

/-- The consumers' arrivals, by consumer. -/
theorem CoordInputs.consArr (hN : CoordInputs L X) {c i pc : Nat} {s : Fin 4} {b : Fin 129}
    {sc : MbarScope}
    (he : X.get (coordCons L X c b, i) =
      some ⟨pc, .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc⟩) :
    arrivals (mbarLoc L c (.coordFree s)) ((X.tr (coordCons L X c b)).take i) <
      okPolls (mbarLoc L c (.coordReady s)) ((X.tr (coordCons L X c b)).take i) := by
  by_cases hb : b.val < 128
  · simp only [coordCons, hb, ↓reduceIte] at he ⊢
    exact hN.wg0Arr hb he
  · simp only [coordCons, hb, ↓reduceIte] at he ⊢
    exact hN.tmaArr he

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
  (hR : MbarRows P L X) (hI : InitRows L X) (hB : Bar0Rows L X) (hN : CoordInputs L X)
include hp hX hFw hR hI hB hN

/-- **Slot `s` of the index ring of CTA `c`** as a ring of kinds. -/
def coordSlot (c : Nat) (s : Fin 4) : KRing L kernel X 32 129 32 :=
  have O := coordReady_obj hp hX hFw hR hI hB c s
  have N := coordFree_obj hp hX hFw hR hI hB hN.tmaOne c s
  { F := mbarLoc L c (.coordReady s)
    E := mbarLoc L c (.coordFree s)
    prod := idxLane L c
    cons := coordCons L X c
    ownF := id
    opF := Unit.it X (mbarLoc L c (.coordReady s)) (idxLane L c)
    itF := Unit.itRef X (mbarLoc L c (.coordReady s)) (idxLane L c)
    cm := Unit.it X (mbarLoc L c (.coordFree s)) (coordCons L X c)
    note := Unit.itRef X (mbarLoc L c (.coordFree s)) (coordCons L X c)
    SF := Unit.S X (mbarLoc L c (.coordReady s)) (idxLane L c)
    SE := Unit.S X (mbarLoc L c (.coordFree s)) (coordCons L X c)
    cover := fun a => ⟨a, rfl⟩
    cF := O.counted
    cE := N.counted
    spins := fun _ _ _ _ _ _ he => poll_canonical hX he
    parF := fun _ _ _ _ _ _ he => O.parity he
    parE := fun _ _ _ _ _ _ he => N.parity he
    fullF := fun _ _ hj => O.card_phase hX (Nat.zero_le _) hj
    fullE := fun _ _ hn hj => N.card_phase hX hn hj
    polF := fun _ hx => O.pol (fun h => hN.idxArr h) hx
    polE := fun _ hy => N.pol (fun h => hN.consArr h) hy
    issueF := fun _ _ => .refl
    issueE := fun _ _ => .refl }

/-- **The coordinate waits observe the indices.** A successful poll of `coordReady s` of CTA `c`
with `u` earlier ones is a consumer's, and it observes every index lane's arrival of use `u`. -/
theorem coordReady_observes {c : Nat} {s : Fin 4} {h j pc p : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c (.coordReady s)) p true acq sc⟩) :
    (∃ b, h = coordCons L X c b) ∧ ∀ a : Fin 32, ∃ i pc' sc', X.get (idxLane L c a, i) =
        some ⟨pc', .arrive (mbarLoc L c (.coordReady s)) 0 1 true sc'⟩ ∧
      arrivals (mbarLoc L c (.coordReady s)) ((X.tr (idxLane L c a)).take i) =
        okPolls (mbarLoc L c (.coordReady s)) ((X.tr h).take j) ∧
      WaitObserves X (.thread (idxLane L c a, i)) (h, j) (mbarLoc L c (.coordReady s)) acq sc := by
  have hb : ∃ b, h = coordCons L X c b := by
    rcases coordReady_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ | ⟨-, hc, hw⟩ |
      ⟨-, -, hk⟩
    · cases hk
    · obtain ⟨b, hb⟩ := coord_cons hp hN.tmaOne he (notUb_of_kind (mbar_kind hX hR he rfl)) hw
      exact ⟨b, hc ▸ hb⟩
    · cases hk
  obtain ⟨b, rfl⟩ := hb
  refine ⟨⟨b, rfl⟩, fun a => ?_⟩
  have O := coordReady_obj hp hX hFw hR hI hB c s
  obtain ⟨hS, hub⟩ := (coordSlot hp hX hFw hR hI hB hN c s).full_observes hX (b := b)
    (PairTmaRing.okPolls_lt_of_get he) a
  have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.coordReady s)))
      (.thread (Unit.it X (mbarLoc L c (.coordReady s)) (idxLane L c) a
        (okPolls (mbarLoc L c (.coordReady s)) ((X.tr (coordCons L X c b)).take j))))
      (.thread (coordCons L X c b, MbarRing.Poll.nth X (mbarLoc L c (.coordReady s))
        (coordCons L X c b)
        (okPolls (mbarLoc L c (.coordReady s)) ((X.tr (coordCons L X c b)).take j)))) := hub
  rw [MbarRing.Poll.nth_eq he] at hub'
  exact O.wait_obs hS he hub'

/-- **The free waits observe the release.** A successful poll of `coordFree s` of CTA `c` with
`u + 1` earlier ones is an index lane's, and it observes every consumer's arrival of use `u`. -/
theorem coordFree_observes {c : Nat} {s : Fin 4} {h j pc p u : Nat} {acq : Bool}
    {sc : MbarScope}
    (he : X.get (h, j) = some ⟨pc, .wait (mbarLoc L c (.coordFree s)) p true acq sc⟩)
    (hj : okPolls (mbarLoc L c (.coordFree s)) ((X.tr h).take j) = u + 1) :
    (∃ a, h = idxLane L c a) ∧ ∀ b : Fin 129, ∃ i pc' sc', X.get (coordCons L X c b, i) =
        some ⟨pc', .arrive (mbarLoc L c (.coordFree s)) 0 1 true sc'⟩ ∧
      arrivals (mbarLoc L c (.coordFree s)) ((X.tr (coordCons L X c b)).take i) = u ∧
      WaitObserves X (.thread (coordCons L X c b, i)) (h, j) (mbarLoc L c (.coordFree s))
        acq sc := by
  have ha : ∃ a, h = idxLane L c a := by
    rcases coordFree_use hR (Frame.lt_of_get hX he) he rfl with ⟨n, hk⟩ | ⟨-, hc, hw⟩ |
      ⟨-, -, hk⟩
    · cases hk
    · obtain ⟨a, ha⟩ := idx_lane hp hw
      exact ⟨a, hc ▸ ha⟩
    · cases hk
  obtain ⟨a, rfl⟩ := ha
  refine ⟨⟨a, rfl⟩, fun b => ?_⟩
  have N := coordFree_obj hp hX hFw hR hI hB hN.tmaOne c s
  have hu := PairTmaRing.okPolls_lt_of_get he
  rw [hj] at hu
  obtain ⟨hS, hub⟩ := (coordSlot hp hX hFw hR hI hB hN c s).empty_observes hX (a := a) hu b
  have hub' : MBarrier.UpdateBeforeWait (X.objects (mbarLoc L c (.coordFree s)))
      (.thread (Unit.it X (mbarLoc L c (.coordFree s)) (coordCons L X c) b u))
      (.thread (idxLane L c a, MbarRing.Poll.nth X (mbarLoc L c (.coordFree s)) (idxLane L c a)
        (u + 1))) := hub
  rw [← hj, MbarRing.Poll.nth_eq he] at hub'
  exact N.wait_obs hS he hub'

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
