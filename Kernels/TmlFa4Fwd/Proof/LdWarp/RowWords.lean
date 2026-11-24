-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.LastStore
public import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrLocal
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrStep
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The words of a loader lane's rows

In a block of a tile of request `b` a lane loads two rows (`row0`, one per page round): the page
word of round `it` (`pgW`), its row in the page (`rwW`), the address a pointer round stores for the
K or V cache (`adW`) and the length of its rows in the block (`lenW`). They depend on the setup and
the round only (`KeepW`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g w : Nat}

/-- The page word of page round `it`: zero for a row past the used length. -/
def pgW (p : Params) (b : Nat) (L : Launch) (g : Nat) (v : V) (per : Per) (it : Fin 2) :
    BitVec 64 :=
  if rowCond p L g v per it then i32 0 else W (p.page b ((row0 p L g v per it).toNat / 16))

/-- The row in its page. -/
def rwW (p : Params) (L : Launch) (g : Nat) (v : V) (per : Per) (it : Fin 2) : BitVec 64 :=
  sub32 (row0 p L g v per it) (mul32 (pgIdx (row0 p L g v per it)) (i32 16))

/-- The layout of a packet's cache. -/
def layOf (p : Params) (c : Bool) : CacheLayout := if c then p.vLayout else p.kLayout

/-- The address a pointer round stores, from the page and the row words it read back. -/
def adOf (p : Params) (v : V) (c : Bool) (lp lr : BitVec 64) : BitVec 64 :=
  add64 (if c then v.su.rd13 else v.su.rd12)
    (shl64 (mad64 (BitVec.ofNat 64 (layOf p c).rowStride) (sx32 lr)
      (mul64 (BitVec.ofNat 64 (layOf p c).pageStride) (sx32 lp))) 1)

/-- The address of the row of round `it` in the cache of half `c`. -/
def adW (p : Params) (b : Nat) (L : Launch) (g : Nat) (v : V) (per : Per) (c : Bool) (it : Fin 2) :
    BitVec 64 :=
  adOf p v c (pgW p b L g v per it) (rwW p L g v per it)

/-- The length word of a later block. -/
def lenW (L : Launch) (g : Nat) (v : V) (per : Per) : BitVec 64 :=
  sel (scmpi .lt .s (startWarm v) 0) (i32 0)
    (if per = .warm then lenWarm L g v else lenSteady L g v)

/-- The fields the words depend on are unchanged. -/
def KeepW (v v' : V) : Prop :=
  v'.su = v.su ∧ v'.rnd = v.rnd ∧ v'.r56 = v.r56 ∧ v'.ukw = v.ukw

section
variable {v v' : V} (h : KeepW v v')
include h

theorem KeepW.row0 (per : Per) (it : Fin 2) :
    Loader.row0 p L g v' per it = Loader.row0 p L g v per it := by
  obtain ⟨h1, h2, h3, -⟩ := h
  simp only [Loader.row0, h1, h2, h3]

theorem KeepW.cond (per : Per) (it : Fin 2) :
    rowCond p L g v' per it = rowCond p L g v per it := by
  unfold rowCond
  rw [h.row0, h.2.2.2]

theorem KeepW.pgW {b : Nat} (per : Per) (it : Fin 2) :
    LdWarp.pgW p b L g v' per it = LdWarp.pgW p b L g v per it := by
  unfold LdWarp.pgW
  rw [h.row0, h.cond]

theorem KeepW.rwW (per : Per) (it : Fin 2) :
    LdWarp.rwW p L g v' per it = LdWarp.rwW p L g v per it := by
  unfold LdWarp.rwW
  rw [h.row0]

theorem KeepW.adW {b : Nat} (per : Per) (c : Bool) (it : Fin 2) :
    LdWarp.adW p b L g v' per c it = LdWarp.adW p b L g v per c it := by
  unfold LdWarp.adW adOf
  rw [h.pgW, h.rwW, h.1]

theorem KeepW.lenW (per : Per) : LdWarp.lenW L g v' per = LdWarp.lenW L g v per := by
  obtain ⟨-, h2, h3, h4⟩ := h
  simp only [LdWarp.lenW, startWarm, lenWarm, lenSteady, h2, h3, h4]

end

/-- The address a pointer round stores. -/
theorem rv_adOf (p : Params) (L : Launch) (g w : Nat) (per : Per) (c : Bool) (it : Fin 2) (v : V)
    (kk : Fin 2) : rv p L g w ⟨.ptS per c it, v, kk⟩ (ptRegs (pk per c)).ad =
      adOf p v c v.lp v.lr := by
  cases per <;> cases c <;> rfl

set_option maxHeartbeats 4000000 in
/-- **The store of a loader state**, exactly. -/
theorem wr_exact (hp : Pre p L m) {d : D} {e : Event} (hev : Ev p L g w d e) {a : Acc}
    {bs : List Byte} (hk : e.kind = .wr a bs) :
    (∃ per it, d.site = .pgSt per it ∧ a.loc = ⟨.local, g, L.localBase + (96 + 4 * it.val)⟩ ∧
      bs = (Value.bits 32 d.v.pw).toBytes) ∨
    (∃ per it, d.site = .rwSt per it ∧ a.loc = ⟨.local, g, L.localBase + (64 + 4 * it.val)⟩ ∧
      bs = (Value.bits 32 (rwW p L g d.v per it)).toBytes) ∨
    ∃ per c it, d.site = .ptS per c it ∧ a.loc = ⟨.local, g, L.localBase + lwO per c it⟩ ∧
      bs = (Value.bits 64 (adOf p d.v c d.v.lp d.v.lr)).toBytes := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  cases s
  case pgSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    swap
    · cases hk
    simp only [Kind.wr.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hx : rv p L g w ⟨.pgSt per it, v, kk⟩ (pgStA per) =
        add64 (BitVec.ofNat 64 (L.localBase + 96)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
      cases per <;> rfl
    have hv : v' = .bits 32 v.pw := by
      rw [pg_val] at hv'
      simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
    subst hv
    refine .inl ⟨per, it, rfl, ?_, rfl⟩
    rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc]
    exact lacc_loc hp (by omega) 4
  case rwSt per it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    swap
    · cases hk
    simp only [Kind.wr.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hx : rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStA per) =
        add64 (BitVec.ofNat 64 (L.localBase + 64)) (wideU4 (i32 ((it.val : Nat) : Int))) := by
      cases per <;> rfl
    have hrw : rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStV per) = rwW p L g v per it := by
      cases per <;> rfl
    have hv : v' = .bits 32 (rwW p L g v per it) := by
      rw [hrw] at hv'
      simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
    subst hv
    refine .inr (.inl ⟨per, it, rfl, ?_, rfl⟩)
    rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc]
    exact lacc_loc hp (by omega) 4
  case ptS per c it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    swap
    · cases hk
    simp only [Kind.wr.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hx : rv p L g w ⟨.ptS per c it, v, kk⟩ (ptRegs (pk per c)).u =
        add64 (BitVec.ofNat 64 (L.localBase + ptOff per c))
          (shl64 (m64 ((it.val : Nat) : Int)) 3) := by
      cases per <;> cases c <;> rfl
    have hv : v' = .bits 64 (adOf p v c v.lp v.lr) := by
      rw [rv_adOf] at hv'
      simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
    subst hv
    refine .inr (.inr ⟨per, c, it, rfl, ?_, rfl⟩)
    rw [hx, shl64_fin3, add64_ofNat, Nat.add_assoc]
    have hlt : ptOff per c + 8 * it.val < 128 := by
      cases per <;> cases c <;> simp [ptOff] <;> omega
    exact lacc_loc hp hlt 8
  all_goals
    simp only [Ev, Epilogue.Ev, Site.toE] at hev
    shape_destruct hev
    all_goals contradiction

/-- A state that skips a page load has a zero page word and a row past the used length. -/
def Skips (p : Params) (L : Launch) (g : Nat) (d : D) : Prop :=
  ∀ per it, d.site = .pgSt per it → rowCond p L g d.v per it = true ∧ d.v.pw = i32 0

theorem skips_pg (d : D) (per : Per) (it : Fin 2) : Skips p L g (pgEnter p L g d per it) := by
  intro per' it' h
  unfold pgEnter D.iteS at h ⊢
  cases hc : rowCond p L g d.v per it <;>
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · simp [D.mk'] at h
  · simp only [D.mk', Site.pgSt.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, trivial⟩

theorem skips_iteS {c : Bool} {a b : D} (ha : Skips p L g a) (hb : Skips p L g b) :
    Skips p L g (D.iteS c a b) := by
  cases c
  · intro per it h; exact hb per it h
  · intro per it h; exact ha per it h

theorem skips_pass (late : Bool) (d : D) : Skips p L g (passStart p L g late d) := by
  intro per it h
  unfold passStart D.ite at h
  split at h <;> (try split at h) <;> cases h

theorem skips_tail (d : D) : Skips p L g (afterTail p L g d) :=
  skips_iteS (skips_pass _ _) (skips_pg _ _ _)

theorem skips_warm (d : D) : Skips p L g (afterWarm p L g w d) :=
  skips_iteS (skips_tail _) (fun _ _ h => by cases h)

theorem skips_prime (d : D) : Skips p L g (afterPrime p L g w d) :=
  skips_iteS (skips_warm _) (skips_pg _ _ _)

theorem skips_warmEnd (d : D) : Skips p L g (warmEnd p L g w d) :=
  skips_iteS (skips_pg _ _ _) (skips_warm _)

theorem skips_steady (d : D) : Skips p L g (steadyEnd p L g d) :=
  skips_iteS (skips_pg _ _ _) (skips_pass _ _)

theorem skips_group (d : D) (t : Fin 7) : Skips p L g (groupEnd p L g d t) := by
  fin_cases t
  case «6» => exact skips_tail d
  all_goals
    intro per it h
    cases h

def skChk (_ : Bool) (s s' : Site) : Bool :=
  match s' with
  | .pgSt .. => (match s with
    | .pgLd .. | .uk | .rwSt .. | .arrive _ true | .te 6 _ | .tc 6 _ => true | _ => false)
  | _ => true
theorem sk_edges : Edges skChk := by unfold Edges AllSites; decide +kernel

set_option maxHeartbeats 4000000 in
/-- **A page round that skips its load** starts with a zero page word, for a row past the used
length. -/
theorem pg_skip {d d' : D} {e : Event} (hl : ∀ per it, d.site ≠ .pgLd per it)
    (hm : d'.site ∈ nexts (not14 w) d.site)
    (hn : succ p L g w d e = some (some d')) : Skips p L g d' := by
  intro per it hs
  have hc := sk_edges.ok hm
  simp only [skChk, hs] at hc
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  refine (show Skips p L g d' from ?_) per it hs
  cases s
  case pgLd per0 it0 => exact (hl _ _ rfl).elim
  case uk =>
    simp only [succ] at hn
    cases kind <;> simp only [reduceCtorEq] at hn
    split at hn
    · obtain ⟨y, rfl, rfl⟩ := word32_inv hn
      exact skips_pg _ _ _
    · simp at hn
  case rwSt per0 it0 =>
    simp only [succ] at hn
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
    · exact skips_pg _ _ _
    · cases hs
  case arrive per0 c0 =>
    cases c0
    · simp at hc
    simp only [succ, Option.some.injEq] at hn
    subst hn
    cases per0
    · exact skips_prime _
    · exact skips_warmEnd _
    · exact skips_steady _
  case te t i =>
    simp only [succ] at hn
    cases kind <;> simp only [reduceCtorEq] at hn
    simp only [Option.some.injEq] at hn
    subst hn
    split
    · intro per it h
      fin_cases i <;> cases h
    · fin_cases i
      · intro per it h; cases h
      · intro per it h; cases h
      · exact skips_group _ _
  case tc t c =>
    simp only [succ] at hn
    split at hn <;> simp only [Option.some.injEq] at hn <;> subst hn
    · cases hs
    · exact skips_group _ _
  all_goals exact absurd hc Bool.false_ne_true

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
