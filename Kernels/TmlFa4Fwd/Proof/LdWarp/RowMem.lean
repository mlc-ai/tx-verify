-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.RowWords
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrStep
import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.TileBlk
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # What a loader lane's local memory holds in a block

A block's sites are in order (`blkPos`). After the page round `it` of a block its page word and its
row are in the lane's local memory, after the pointer round `it` of a packet the row's address is,
and the packet's address words are its halves (`RowInv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

/-! ### The order of a block's sites -/

/-- The period of a block's site. -/
def perOf : Site → Option Per
  | .pgLd per _ | .pgSt per _ | .rwSt per _ | .slot per _ | .ptP per _ _ | .ptR per _ _
  | .ptS per _ _ | .lw per _ _ | .xl per _ _ | .xh per _ _ | .cp per _ _ _ | .commit per _
  | .arrive per _ => some per
  | .tw t | .te t _ | .ta t | .tc t _ =>
    if t.val < 4 then some .prime else if t.val < 6 then some .warm else none
  | _ => none

/-- The place of a site in its block. -/
def blkPos : Site → Nat
  | .pgLd _ it => 3 * it.val
  | .pgSt _ it => 1 + 3 * it.val
  | .rwSt _ it => 2 + 3 * it.val
  | .slot _ c => if c then 20 else 6
  | .ptP _ c it => (if c then 21 else 7) + 3 * it.val
  | .ptR _ c it => (if c then 22 else 8) + 3 * it.val
  | .ptS _ c it => (if c then 23 else 9) + 3 * it.val
  | .lw _ c _ | .xl _ c _ | .xh _ c _ | .cp _ c _ _ | .commit _ c => if c then 27 else 13
  | .arrive _ c => if c then 28 else 14
  | .tw t | .te t _ | .ta t | .tc t _ => if t.val < 6 then 15 else 0
  | _ => 0

/-- After the page store of round `it`. -/
def aftPg (per : Per) (it : Fin 2) (s : Site) : Bool :=
  perOf s == some per && decide (1 + 3 * it.val < blkPos s)
/-- After the row store of round `it`. -/
def aftRw (per : Per) (it : Fin 2) (s : Site) : Bool :=
  perOf s == some per && decide (2 + 3 * it.val < blkPos s)
/-- After the address store of round `it` of packet `c`, until the next packet. -/
def aftPt (per : Per) (c : Bool) (it : Fin 2) (s : Site) : Bool :=
  perOf s == some per && decide ((if c then 23 else 9) + 3 * it.val < blkPos s) &&
    (c || decide (blkPos s < 20))
/-- After the length of a later block. -/
def aftLen (per : Per) (s : Site) : Bool :=
  perOf s == some per && decide (12 < blkPos s)

/-- The half of a packet's rows. -/
def rowAt : Site → Option (Per × Bool × Fin 2)
  | .xl per c i | .xh per c i | .cp per c i _ => some (per, c, ⟨i.val / 8, by omega⟩)
  | _ => none

/-- The step from `s` into an after-site keeps the block or is from the store. -/
def aftChk (_ : Bool) (s s' : Site) : Bool :=
  ([Per.prime, .warm, .steady].all fun per =>
    (!aftLen per s' || aftLen per s || s == .ptS per false 1) &&
    [(0 : Fin 2), 1].all fun it =>
      (!aftPg per it s' || aftPg per it s || s == .pgSt per it) &&
      (!aftRw per it s' || aftRw per it s || s == .rwSt per it) &&
      [false, true].all fun c => !aftPt per c it s' || aftPt per c it s || s == .ptS per c it) &&
  (!(decide (1 < blkPos s')) || (!s.blkEnd && s.blk))
theorem aft_edges : Edges aftChk := by unfold Edges AllSites; decide +kernel

/-- A packet's row site is from its address load or a row of the same half. -/
def rowsChk (_ : Bool) (s s' : Site) : Bool :=
  match rowAt s' with
  | none => true
  | some (per, c, h) => rowAt s == some (per, c, h) || s == .lw per c h
theorem rows_edges : Edges rowsChk := by unfold Edges AllSites; decide +kernel

/-- The steps into the pointer rounds. -/
def ptChk (_ : Bool) (s s' : Site) : Bool :=
  match s' with
  | .ptR per c it => s == .ptP per c it
  | .ptS per c it => s == .ptR per c it
  | .pgSt per it => match s with | .pgLd per' it' => per == per' && it == it' | _ => true
  | _ => true
theorem pt_edges : Edges ptChk := by unfold Edges AllSites; decide +kernel

/-! ### The lane's local memory -/

/-- The lane's last store at an offset before position `k` wrote `bs`. -/
def Mem (L : Launch) (X : Execution) (g k o : Nat) (bs : List Byte) : Prop :=
  ∃ j a, LastAt L X g k o j a bs

theorem Mem.mono {k o : Nat} {bs : List Byte} (h : Mem L X g k o bs)
    (hne : ∀ a bs', X.Writes (g, k) a bs' → a.loc ≠ ⟨.local, g, L.localBase + o⟩) :
    Mem L X g (k + 1) o bs := by
  obtain ⟨j, a, h1, h2, h3, h4⟩ := h
  refine ⟨j, a, by omega, h2, h3, fun j' hj hk' a' bs' hw => ?_⟩
  rcases Nat.lt_or_ge j' k with h | h
  · exact h4 j' hj h a' bs' hw
  · obtain rfl : j' = k := by omega
    exact hne _ _ hw

theorem Mem.new {k o : Nat} {a : Acc} {bs : List Byte} (hw : X.Writes (g, k) a bs)
    (hl : a.loc = ⟨.local, g, L.localBase + o⟩) : Mem L X g (k + 1) o bs :=
  ⟨k, a, Nat.lt_succ_self _, hw, hl, fun j' h1 h2 => by omega⟩

theorem Mem.eq {k o j : Nat} {a : Acc} {bs bs' : List Byte} (h : Mem L X g k o bs)
    (h' : LastAt L X g k o j a bs') : bs' = bs := by
  obtain ⟨j0, a0, h0⟩ := h
  exact (h'.unique h0).2

theorem bits_inj {wd : Nat} {x y : BitVec 64} (hwd : wd = 32 ∨ wd = 64)
    (h : (Value.bits wd x).toBytes = (Value.bits wd y).toBytes) : x = y := by
  have := congrArg List.head? h
  rcases hwd with rfl | rfl <;>
    simpa [Value.toBytes, Value.bytes, Value.byteAt, List.range_succ_eq_map] using this

/-- **The rows' words of a block state.** -/
structure RowInv (p : Params) (b : Nat) (L : Launch) (X : Execution) (g k : Nat) (d : D) :
    Prop where
  pw : ∀ per it, d.site = .pgSt per it → d.v.pw = pgW p b L g d.v per it
  pg : ∀ per it, aftPg per it d.site = true →
    Mem L X g k (96 + 4 * it.val) (Value.bits 32 (pgW p b L g d.v per it)).toBytes
  rw : ∀ per it, aftRw per it d.site = true →
    Mem L X g k (64 + 4 * it.val) (Value.bits 32 (rwW p L g d.v per it)).toBytes
  lp : ∀ per c it, d.site = .ptR per c it ∨ d.site = .ptS per c it →
    d.v.lp = pgW p b L g d.v per it
  lr : ∀ per c it, d.site = .ptS per c it → d.v.lr = rwW p L g d.v per it
  ad : ∀ per c it, aftPt per c it d.site = true →
    Mem L X g k (lwO per c it) (Value.bits 64 (adW p b L g d.v per c it)).toBytes
  mid : ∀ per c h, d.site = .lw per c h → d.k.val = 1 →
    d.v.l0.toNat = (adW p b L g d.v per c h).toNat % 2 ^ 32
  row : ∀ per c h, rowAt d.site = some (per, c, h) →
    d.v.l0.toNat = (adW p b L g d.v per c h).toNat % 2 ^ 32 ∧
      d.v.l1.toNat = (adW p b L g d.v per c h).toNat / 2 ^ 32
  len : ∀ per, per ≠ .prime → aftLen per d.site = true → d.v.len = lenW L g d.v per

/-! ### No step stays at a packet's arrival -/

def NoArr (d : D) : Prop := ∀ per c, d.site ≠ .arrive per c

theorem noArr_iteS {c : Bool} {a b : D} (ha : NoArr a) (hb : NoArr b) : NoArr (D.iteS c a b) := by
  cases c
  · exact hb
  · exact ha

theorem noArr_pg (d : D) (per : Per) (it : Fin 2) : NoArr (pgEnter p L g d per it) :=
  noArr_iteS (fun _ _ h => by cases h) (fun _ _ h => by cases h)

theorem noArr_pass (late : Bool) (d : D) : NoArr (passStart p L g late d) := by
  intro per it h
  unfold passStart D.ite at h
  split at h <;> (try split at h) <;> cases h

theorem noArr_tail (d : D) : NoArr (afterTail p L g d) :=
  noArr_iteS (noArr_pass _ _) (noArr_pg _ _ _)

theorem noArr_warm (d : D) : NoArr (afterWarm p L g w d) :=
  noArr_iteS (noArr_tail _) (fun _ _ h => by cases h)

theorem noArr_arrive (d : D) (per : Per) : NoArr (afterArrive p L g w d per true) := by
  cases per
  · exact noArr_iteS (noArr_warm _) (noArr_pg _ _ _)
  · exact noArr_iteS (noArr_pg _ _ _) (noArr_warm _)
  · exact noArr_iteS (noArr_pg _ _ _) (noArr_pass _ _)

/-- A step into a later site of a block is inside the block. -/
theorem step_in {d d' : D} {e : Event} {nc : Cnt → Nat} (hm : Move L g w (d, nc) e d')
    (hn : succ p L g w d e = some (some d')) (hp1 : 1 < blkPos d'.site) (hb' : d'.site.blk = true) :
    d.site.blk = true ∧ d.site.blkEnd = false := by
  rcases hm.edge with h | h
  · simp only at h
    refine ⟨h ▸ hb', ?_⟩
    by_contra hx
    simp only [Bool.not_eq_false] at hx
    rw [h] at hp1
    obtain ⟨s, v, kk⟩ := d
    cases s <;> simp only [Site.blkEnd, Bool.false_eq_true, decide_eq_true_eq] at hx
    · subst hx
      simp only [succ, Option.some.injEq] at hn
      subst hn
      exact noArr_arrive _ _ _ _ h
    · rename_i t i
      obtain ⟨h1, -⟩ := hx
      simp [blkPos, h1] at hp1
    · rename_i t i
      obtain ⟨h1, -⟩ := hx
      simp [blkPos, h1] at hp1
  · have hc := aft_edges.ok h
    simp only [aftChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hc
    rcases hc.2 with h1 | h1
    · exact (h1 hp1).elim
    · exact ⟨h1.2, h1.1⟩

theorem step_keep {d d' : D} {e : Event} {nc : Cnt → Nat} (hm : Move L g w (d, nc) e d')
    (hev : Ev p L g w d e) (hn : succ p L g w d e = some (some d')) (hp1 : 1 < blkPos d'.site)
    (hb' : d'.site.blk = true) : KeepW d.v d'.v := by
  obtain ⟨h1, h2⟩ := step_in hm hn hp1 hb'
  obtain ⟨-, k2, k3, -, -, -, -, k8, k9, -⟩ := blk_step h1 h2 hev hn
  exact ⟨k2, k3, k9, k8⟩

/-! ### The after-sites of a step -/

theorem aft_of {per : Per} {n : Nat} {s : Site}
    (h : (perOf s == some per && decide (n < blkPos s)) = true) :
    perOf s = some per ∧ n < blkPos s := by
  simpa using h

/-- The address stores of a packet after one are at other offsets. -/
theorem pt_off_ne : ∀ {per per1 : Per} {c c1 : Bool} {it it1 : Fin 2},
    aftPt per c it (.ptS per1 c1 it1) = true → lwO per c it ≠ lwO per1 c1 it1 := by
  intro per per1 c c1 it it1
  cases per <;> cases per1 <;> cases c <;> cases c1 <;> revert it it1 <;> decide

theorem aft_prev {n14 : Bool} {s s' : Site} (h : s' ∈ nexts n14 s) (per : Per) :
    (aftLen per s' = true → aftLen per s = true ∨ s = .ptS per false 1) ∧ ∀ it : Fin 2,
      (aftPg per it s' = true → aftPg per it s = true ∨ s = .pgSt per it) ∧
      (aftRw per it s' = true → aftRw per it s = true ∨ s = .rwSt per it) ∧ ∀ c : Bool,
        aftPt per c it s' = true → aftPt per c it s = true ∨ s = .ptS per c it := by
  have hc := aft_edges.ok h
  simp only [aftChk, Bool.and_eq_true] at hc
  have h1 := List.all_eq_true.mp hc.1 per (by cases per <;> simp)
  simp only [Bool.and_eq_true] at h1
  obtain ⟨h2, h3⟩ := h1
  refine ⟨fun ha => by simpa [ha] using h2, fun it => ?_⟩
  have h4 := List.all_eq_true.mp h3 it (by fin_cases it <;> simp)
  simp only [Bool.and_eq_true] at h4
  obtain ⟨⟨h5, h6⟩, h7⟩ := h4
  refine ⟨fun ha => by simpa [ha] using h5, fun ha => by simpa [ha] using h6, fun c ha => ?_⟩
  have h8 := List.all_eq_true.mp h7 c (by cases c <;> simp)
  simpa [ha] using h8

/-- The sites of the lane's stores. -/
def isSt : Site → Bool
  | .pgSt .. | .rwSt .. | .ptS .. => true
  | _ => false

/-- A store site's event is its store. -/
theorem st_wr {d : D} {pc : Nat} {kind : Kind} (hev : Ev p L g w d ⟨pc, kind⟩)
    (hnu : ∀ f, (⟨pc, kind⟩ : Event).kind ≠ .ub f) (hst : isSt d.site = true) :
    ∃ a bs, kind = .wr a bs := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [isSt, Bool.false_eq_true] at hst <;> simp only [Ev] at hev <;>
    (rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩
     · exact ⟨_, _, hk⟩
     · exact (hnu f hk).elim)

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
