-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Ledger
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' reference invariant

The fields that following needs (rule F1): the ring registers at every state (`RefRing`) and the
two counts the steps and sources read (`RefCounts`: the commits and the local stores), as closed
forms in the site, the packet `k` of the current warm or steady block's K half and the number `A`
of packets of the tile. `k` and `A` are functions of the state and its commits (`posK`, `posA`),
so `Ref` has no witnesses; the step proofs build the witness form `RefE` and convert (`RefE.ref`).

* The packets in issue order: the first block's K and V (packets 0 and 1), then each later block's
  K and V (packets `k` and `k + 1`, with `k = 2, 4, …`). The round counters (`%r6114`, `%r6121`)
  are not related to `k` here: the ring registers follow the packets, and the number of rounds
  matters only for progress.
* Packet `j` goes to ring slot `j mod 3` and waits for its empty barrier at parity
  `(j / 3 + 1) mod 2`; the drain waits for the next three packets' slots. The second scheduler
  pass and the drain come after all `A` packets.
* The Bias stage parities (`%r6117`, `%r6118`) are the warm rounds done modulo 2 on warp 14 (plus
  one past the round's second Bias group), and 1 on warp 15.

Every other count of the ledger is a standalone fact in `Facts/`, proved from the step spec
(`Spec.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32)

noncomputable section

/-- The shared location at offset `o` of the lane's CTA. -/
abbrev bl (L : Launch) (g o : Nat) : Loc := ⟨.shared, g / L.block, L.sharedBase + o⟩

/-- A site of the scheduler's second pass. -/
def Site.late : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l => l
  | _ => false

/-- A site of warp 14's TMA groups. -/
def Site.isTma : Site → Bool
  | .tw _ | .te _ _ | .ta _ | .tc _ _ | .dq | .de | .da => true
  | _ => false

/-- The packet of half `v` of a period's block, where `k` is the packet of the K half of the
current warm or steady block (the first block's packets are 0 and 1). -/
def pkOf (per : Per) (v : Bool) (k : Nat) : Nat :=
  (match per with | .prime => 0 | _ => k) + if v then 1 else 0

/-- The packets before TMA group `t` (they are all published and acquired). -/
def tmaPk (t : Fin 7) (k : Nat) : Nat :=
  if t.val < 4 then 1 else if t.val < 6 then k + 1 else k

/-- The packets a state has published. -/
def arrAt (s : Site) (k A : Nat) : Nat :=
  match s with
  | .pgLd per _ | .pgSt per _ | .rwSt per _ => pkOf per false k
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v => pkOf per v k
  | .tw t | .te t _ | .ta t | .tc t _ => tmaPk t k
  | .dw _ | .dq | .de | .da | .exit => A
  | .word sk | .down sk | .up sk _ | .total sk => if sk.late then A else 0
  | .vote l | .pre l | .tiles l => if l then A else 0
  | _ => 0

/-- The copies and commits of the current packet before a state. -/
def inPkt (s : Site) : Nat × Nat :=
  match s with
  | .cp _ _ i c => (2 * i.val + c.val, 0)
  | .lw _ _ h => (16 * h.val, 0)
  | .xl _ _ i | .xh _ _ i => (2 * i.val, 0)
  | .commit _ _ => (32, 0)
  | .arrive _ _ => (32, 1)
  | _ => (0, 0)

/-- The class of a site for the ring and Bias registers: the first scheduler pass and the
request's reads, the first block's K half, its V half, warp 14's first four groups (`z`: after the
last election of the fourth, which clears the first Bias parity), a warm round (`f`: past the
round's second Bias group, which flips the Bias parities), a steady round or the last Bias group,
and the second pass with the drain. -/
inductive RingCls where
  | first | primeK | primeV | tma0 (z : Bool) | warm (f : Bool) | later | drain
  deriving DecidableEq

def ringCls : Site → RingCls
  | .pgLd per _ | .pgSt per _ | .rwSt per _ =>
    match per with | .prime => .primeK | .warm => .warm false | .steady => .later
  | .slot per v | .ptP per v _ | .ptR per v _ | .ptS per v _ | .lw per v _ | .xl per v _
  | .xh per v _ | .cp per v _ _ | .commit per v | .arrive per v =>
    match per with
    | .prime => if v then .primeV else .primeK
    | .warm => .warm v
    | .steady => .later
  | .tw t | .te t _ | .ta t =>
    if t.val < 4 then .tma0 false else if t.val < 6 then .warm false else .later
  | .tc t c =>
    if t.val < 4 then .tma0 (t.val = 3 ∧ c.val = 1) else if t.val < 6 then .warm false
    else .later
  | .dw _ | .dq | .de | .da | .exit => .drain
  | .word sk | .down sk | .up sk _ | .total sk => if sk.late then .drain else .first
  | .vote l | .pre l | .tiles l => if l then .drain else .first
  | _ => .first

/-- The ring slot and parity registers hold those of packet `j`: slot `j mod 3`, parity
`(j / 3 + 1) mod 2`. -/
def SlotIs (v : V) (j : Nat) : Prop :=
  v.slot = BitVec.ofNat 64 (j % 3) ∧ v.par = BitVec.ofNat 64 ((j / 3 + 1) % 2)

/-- The ring words of a site of class `c` (`w` is the warp, `k` the packet of the current block's K
half, `A` the packets of the tile): the ring registers in a warm or steady round (where `k` is at
least 2) and in the drain, and the Bias parities of warp 14 (`%r6117`, `%r6118`: the warm rounds
done modulo 2, plus one past a round's second Bias group; 1 on warp 15). -/
def RingWords (w : Nat) (c : RingCls) (v : V) (k A : Nat) : Prop :=
  match c with
  | .first | .primeK => True
  | .primeV => v.bq0 = BitVec.ofNat 64 (if w = 14 then 0 else 1)
  | .tma0 z => v.bq0 = BitVec.ofNat 64 (if z then 0 else 1)
  | .warm f =>
    (SlotIs v k ∧ 2 ≤ k) ∧ v.bq0 = v.bq1 ∧
      v.bq0 = BitVec.ofNat 64
        (if w = 14 then ((r32 v.rnd).toNat + if f then 1 else 0) % 2 else 1)
  | .later => SlotIs v k ∧ 2 ≤ k
  | .drain => SlotIs v A

/-- **The ring fields of the loader's reference invariant**. -/
structure RefRing (_p : Params) (_L : Launch) (_g w : Nat) (d : D) (k A : Nat) : Prop where
  /-- The TMA groups and the drain's Q wait run on warp 14 only. -/
  tma : d.site.isTma = true → w = 14
  /-- The ring words of the site's class. -/
  words : RingWords w (ringCls d.site) d.v k A

theorem refRing_iff {p : Params} {L : Launch} {g w : Nat} {d : D} {k A : Nat} :
    RefRing p L g w d k A ↔
      (d.site.isTma = true → w = 14) ∧ RingWords w (ringCls d.site) d.v k A :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- `RefRing` depends on the state only through the site's class and the ring words. -/
theorem refRing_congr {p : Params} {L : Launch} {g w : Nat} {d d' : D} {k A : Nat}
    (h : RefRing p L g w d k A) (hc : ringCls d'.site = ringCls d.site)
    (ht : d'.site.isTma = d.site.isTma)
    (hrnd : d'.v.rnd = d.v.rnd) (hslot : d'.v.slot = d.v.slot) (hpar : d'.v.par = d.v.par)
    (hb0 : d'.v.bq0 = d.v.bq0) (hb1 : d'.v.bq1 = d.v.bq1) : RefRing p L g w d' k A := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [ht]; exact h1, ?_⟩
  unfold RingWords SlotIs at h2 ⊢
  rw [hc, hrnd, hslot, hpar, hb0, hb1]
  exact h2

/-! ### Local stores

Per block, the lane stores eight local words in this order: the page and the row of page round 0
(offsets 96, 64) and of round 1 (100, 68), then the K half's two row addresses (at 0 and 8 in the
first block, at 32 and 40 in the later ones), then the V half's (0, 8). The pointer rounds load
the page and row words back, the packets the row addresses. -/

/-- The offsets of a block's local stores, in order (`pr`: the first block). -/
def lstSeq (pr : Bool) : List Nat :=
  [96, 64, 100, 68, if pr then 0 else 32, if pr then 8 else 40, 0, 8]

/-- The local offsets the lane stores to. -/
def lstOffs : List Nat := [96, 100, 64, 68, 0, 8, 32, 40]

/-- The stores at offset `o` before later block `b` (`b ≥ 1`: the first block and `b - 1` later
ones). -/
def lstCum (b o : Nat) : Nat :=
  if o = 0 ∨ o = 8 then b + 1 else if o = 32 ∨ o = 40 then b - 1 else b

/-- The local stores of the current block before a state. -/
def lstPos : Site → Nat
  | .pgLd _ it | .pgSt _ it => 2 * it.val
  | .rwSt _ it => 2 * it.val + 1
  | .slot _ v => if v then 6 else 4
  | .ptP _ v it | .ptR _ v it | .ptS _ v it => (if v then 6 else 4) + it.val
  | .lw _ v _ | .xl _ v _ | .xh _ v _ | .cp _ v _ _ | .commit _ v | .arrive _ v =>
    if v then 8 else 6
  | .tw t | .te t _ | .ta t | .tc t _ => if t.val < 6 then 6 else 0
  | _ => 0

/-- The stores at offset `o` after the tile's `A` packets (`A / 2` blocks). -/
def lstEnd (A o : Nat) : Nat := if A = 0 then 0 else lstCum (A / 2) o

/-- The lane's local stores at offset `o` before a state: in the first block, those of the block
so far; in later block `k / 2`, those before it and of the block so far; at the second pass and
the drain, all of the tile's. -/
def lstAt (s : Site) (k A o : Nat) : Nat :=
  match s with
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ =>
    match per with
    | .prime => ((lstSeq true).take (lstPos s)).count o
    | _ => lstCum (k / 2) o + ((lstSeq false).take (lstPos s)).count o
  | .tw t | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then ((lstSeq true).take (lstPos s)).count o
    else lstCum (k / 2) o + ((lstSeq false).take (lstPos s)).count o
  | .dw _ | .dq | .de | .da | .exit => lstEnd A o
  | .word sk | .down sk | .up sk _ | .total sk => if sk.late then lstEnd A o else 0
  | .vote l | .pre l | .tiles l => if l then lstEnd A o else 0
  | _ => 0

/-- **The count fields of the loader's reference invariant** at a counted state, for a tile of `A`
packets (`A = 0` without a tile): the two that following reads (the commits fix the loop positions
`posK`, `posA`; the local stores are the sources of the pointer rounds' and packets' loads). The
other counts are standalone facts (`Facts/`). -/
structure RefCounts (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) (k A : Nat) : Prop where
  /-- The commits: the published packets and the one whose arrival is pending. -/
  commit : dn.2 .commit = arrAt dn.1.site k A + (inPkt dn.1.site).2
  /-- The local stores at each offset (the pointer rounds and the packets load them back). -/
  lst : ∀ o ∈ lstOffs, dn.2 (.lst o) = lstAt dn.1.site k A o

/-! ### Loop positions

The packet `k` of the current block and the packets `A` of the tile are functions of the state and
the ledger (`posK`, `posA`): the commits less those of the current block before the site. The
closed forms read `k` only at a warm or steady block's sites and the TMA groups after the first
block (`Site.readsK`), and `A` only at the second pass and the drain (`Site.readsA`). -/

/-- The sites whose closed forms read the packet `k` of the current block. -/
def Site.readsK : Site → Bool
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ => per != .prime
  | .tw t | .te t _ | .ta t | .tc t _ => decide (4 ≤ t.val)
  | _ => false

/-- The sites whose closed forms read the packets `A` of the tile. -/
def Site.readsA (s : Site) : Bool := ringCls s == .drain

/-- The commits of the current block before a site that reads `k`. -/
def kOff (s : Site) : Nat := arrAt s 0 0 + (inPkt s).2

/-- **The packet of the current block's K half**: the commits less those of the block before the
site. -/
def posK (dn : D × (Cnt → Nat)) : Nat := dn.2 .commit - kOff dn.1.site

/-- **The packets of the tile** (at the second pass and the drain): the commits. -/
def posA (dn : D × (Cnt → Nat)) : Nat := dn.2 .commit

/-- **The loader warps' reference invariant** at a counted state: the ring and count fields at the
state's loop positions. -/
structure Ref (p : Params) (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) : Prop
    extends RefRing p L g w dn.1 (posK dn) (posA dn), RefCounts L g w dn (posK dn) (posA dn)

/-- The reference invariant with its loop positions as witnesses: the form the step proofs build
(`RefE.ref`). -/
def RefE (p : Params) (L : Launch) (g w : Nat) (dn : D × (Cnt → Nat)) : Prop :=
  ∃ k A, RefRing p L g w dn.1 k A ∧ RefCounts L g w dn k A

variable {p : Params} {L : Launch} {g w : Nat}

set_option hygiene false in
/-- Close `forms_pos` at a site: by the position the site reads, or by the closed forms' values. -/
local macro "pos_tac" : tactic => `(tactic| first
  | exact ⟨rfl, fun _ => rfl⟩
  | (obtain rfl := hA rfl; exact ⟨rfl, fun _ => rfl⟩)
  | (obtain rfl := hk rfl; exact ⟨rfl, fun _ => rfl⟩))

/-- The closed forms read `k` and `A` only where `readsK` and `readsA` say. -/
theorem forms_pos {s : Site} {k A k' A' : Nat} (hk : s.readsK = true → k' = k)
    (hA : s.readsA = true → A' = A) :
    arrAt s k' A' = arrAt s k A ∧ ∀ o, lstAt s k' A' o = lstAt s k A o := by
  cases s
  case word sk | down sk | up sk _ | total sk => cases sk <;> pos_tac
  case vote l | pre l | tiles l => cases l <;> pos_tac
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | ptP per _ _ | ptR per _ _
    | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _ | cp per _ _ _ | commit per _
    | arrive per _ => cases per <;> pos_tac
  case tw t | te t _ | ta t | tc t _ =>
    by_cases h4 : 4 ≤ t.val
    · obtain rfl := hk (by simp [Site.readsK, h4]); exact ⟨rfl, fun _ => rfl⟩
    · have h4' : t.val < 4 := by omega
      simp [arrAt, lstAt, tmaPk, h4']
  all_goals pos_tac

/-- At a site that reads `k`, the published packets are `k` plus those of the block before it. -/
theorem arrAt_readsK {s : Site} (h : s.readsK = true) (k A : Nat) :
    arrAt s k A = k + arrAt s 0 0 := by
  cases s <;> simp only [Site.readsK, Bool.false_eq_true] at h
  case tw t | te t _ | ta t | tc t _ =>
    have h4 : 4 ≤ t.val := by simpa using h
    simp only [arrAt, tmaPk, show ¬ t.val < 4 by omega, ↓reduceIte]
    split_ifs <;> omega
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | ptP per _ _ | ptR per _ _
    | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _ | cp per _ _ _ | commit per _
    | arrive per _ => cases per <;> simp_all [arrAt, pkOf]

/-- At a site that reads `A`, the published packets are `A` and no packet is in progress. -/
theorem arrAt_readsA {s : Site} (h : s.readsA = true) (k A : Nat) :
    arrAt s k A = A ∧ (inPkt s).2 = 0 := by
  cases s
  case word sk | down sk | up sk _ | total sk =>
    cases sk <;> simp_all [Site.readsA, ringCls, arrAt, inPkt, Epilogue.Scan.late]
  case vote l | pre l | tiles l => cases l <;> simp_all [Site.readsA, ringCls, arrAt, inPkt]
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | ptP per _ _ | ptR per _ _
    | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _ | cp per _ _ _ | commit per _
    | arrive per _ =>
    cases per <;> simp only [Site.readsA, ringCls, beq_iff_eq] at h <;> (try split_ifs at h) <;>
      simp_all
  case tw t | te t _ | ta t | tc t _ =>
    simp only [Site.readsA, ringCls, beq_iff_eq] at h; split_ifs at h
  all_goals simp_all [Site.readsA, ringCls, arrAt, inPkt]

/-- A warm or steady class reads `k`. -/
theorem readsK_of_cls {s : Site} (h : (∃ f, ringCls s = .warm f) ∨ ringCls s = .later) :
    s.readsK = true := by
  cases s
  case tw t | te t _ | ta t | tc t _ =>
    simp only [Site.readsK, decide_eq_true_eq]
    by_contra h4
    simp only [ringCls] at h
    rcases h with ⟨f, h⟩ | h <;> split_ifs at h <;> simp_all
  case pgLd per _ | pgSt per _ | rwSt per _ | slot per _ | ptP per _ _ | ptR per _ _
    | ptS per _ _ | lw per _ _ | xl per _ _ | xh per _ _ | cp per _ _ _ | commit per _
    | arrive per _ =>
    cases per <;> simp only [ringCls, Site.readsK] at h ⊢ <;> (try split_ifs at h) <;> simp_all
  case word sk | down sk | up sk _ | total sk =>
    cases sk <;> simp_all [ringCls, Epilogue.Scan.late]
  case vote l | pre l | tiles l => cases l <;> simp_all [ringCls]
  all_goals simp_all [ringCls]

/-- `RefRing` reads `k` and `A` only where `readsK` and `readsA` say. -/
theorem refRing_pos {d : D} {k A k' A' : Nat} (hk : d.site.readsK = true → k' = k)
    (hA : d.site.readsA = true → A' = A) (h : RefRing p L g w d k A) : RefRing p L g w d k' A' := by
  refine ⟨h.tma, ?_⟩
  have h2 := h.words
  unfold RingWords at h2 ⊢
  cases hc : ringCls d.site <;> simp only [hc] at h2 ⊢
  case warm => rw [hk (readsK_of_cls (.inl ⟨_, hc⟩))]; exact h2
  case later => rw [hk (readsK_of_cls (.inr hc))]; exact h2
  case drain => rw [hA (by simp [Site.readsA, hc])]; exact h2
  all_goals exact h2

/-- `RefCounts` reads `k` and `A` only where `readsK` and `readsA` say. -/
theorem refCounts_pos {dn : D × (Cnt → Nat)} {k A k' A' : Nat}
    (hk : dn.1.site.readsK = true → k' = k) (hA : dn.1.site.readsA = true → A' = A)
    (h : RefCounts L g w dn k A) : RefCounts L g w dn k' A' := by
  obtain ⟨f2, f3⟩ := forms_pos hk hA
  exact ⟨by rw [f2]; exact h.commit, fun o ho => by rw [f3]; exact h.lst o ho⟩

/-- `Ref` with its positions as witnesses. -/
theorem Ref.refE {dn : D × (Cnt → Nat)} (h : Ref p L g w dn) : RefE p L g w dn :=
  ⟨_, _, h.toRefRing, h.toRefCounts⟩

/-- **The positions of `RefE`'s witnesses are the state's**, where the closed forms read them. -/
theorem RefE.ref {dn : D × (Cnt → Nat)} (h : RefE p L g w dn) : Ref p L g w dn := by
  obtain ⟨k, A, hR, hC⟩ := h
  have hc := hC.commit
  have hk : dn.1.site.readsK = true → posK dn = k := fun hs => by
    simp only [posK, kOff, hc, arrAt_readsK hs k A]; omega
  have hA : dn.1.site.readsA = true → posA dn = A := fun hs => by
    simp only [posA, hc, (arrAt_readsA hs k A).1, (arrAt_readsA hs k A).2, Nat.add_zero]
  exact ⟨refRing_pos hk hA hR, refCounts_pos hk hA hC⟩
end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
