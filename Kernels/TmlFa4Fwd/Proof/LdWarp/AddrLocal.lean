-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.LastStore
import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.Loader.Local
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.PageWord
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Kernels.TmlFa4Fwd.Proof.Lib.Start
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The row addresses of a loader lane's packets

At every state of a loader lane (`AddrOk`): the page word and the words a pointer round read back
are a page and a row, the setup's head bases are a head's, and in a packet the two words `l0`, `l1`
are the two halves of the address of one row of the cache: both loads of the half read the lane's
last pointer store at one offset. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- A site of a packet after its address load. -/
def isRow : Site → Bool
  | .xl .. | .xh .. | .cp .. => true
  | _ => false

/-- The offset a packet's address load reads. -/
def lwO (per : Per) (b : Bool) (h : Fin 2) : Nat :=
  (if per ≠ .prime ∧ b = false then 32 else 0) + 8 * h.val

/-- The two words are the halves of a row's address. -/
def Halves (p : Params) (x0 x1 : BitVec 64) : Prop :=
  ∃ y, RowA p y ∧ x0.toNat = y.toNat % 2 ^ 32 ∧ x1.toNat = y.toNat / 2 ^ 32

/-- **The address words of a loader lane's state before position `k`.** -/
structure AddrOk (p : Params) (L : Launch) (X : Execution) (g k : Nat) (d : D) : Prop where
  pw : PageW p d.v.pw
  lp : PageW p d.v.lp
  lr : RowV d.v.lr
  head : d.site.blk = true → HeadOk p d.v
  mid : ∀ per b h, d.site = .lw per b h → d.k.val = 1 → ∃ j a y, RowA p y ∧
    LastAt L X g k (lwO per b h) j a (Value.bits 64 y).toBytes ∧ d.v.l0.toNat = y.toNat % 2 ^ 32
  row : isRow d.site = true → Halves p d.v.l0 d.v.l1

def rowChk (_ : Bool) (s s' : Site) : Bool :=
  !isRow s' || isRow s || match s with | .lw .. => true | _ => false
theorem row_edges : Edges rowChk := by unfold Edges AllSites; decide +kernel

def blkChk (_ : Bool) (s s' : Site) : Bool := !s'.blk || s.blk || decide (s = .uk)
theorem blk_edges : Edges blkChk := by unfold Edges AllSites; decide +kernel

def lwChk (_ : Bool) (s s' : Site) : Bool :=
  match s' with | .lw .. => (match s with | .ptS .. | .cp .. => true | _ => false) | _ => true
theorem lw_edges : Edges lwChk := by unfold Edges AllSites; decide +kernel

set_option maxHeartbeats 4000000 in
/-- **A store of a loader state with its address words.** -/
theorem store_ok (hp : Pre p L m) {d : D} {e : Event} {k : Nat} (hA : AddrOk p L X g k d)
    (hev : Ev p L g w d e) : ∀ a bs, e.kind = .wr a bs → StoreOk p L g a bs := by
  intro a bs hk
  obtain ⟨-, -, o, hl, hz⟩ := (wr_ev hp hev).1 a bs hk
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
    refine ⟨96 + 4 * it.val, ?_, .inl ⟨by omega, rfl, _, hA.pw, rfl⟩⟩
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
    have hv : v' = .bits 32 (rv p L g w ⟨.rwSt per it, v, kk⟩ (rwStV per)) := by
      simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
    subst hv
    refine ⟨64 + 4 * it.val, ?_, .inr (.inl ⟨by omega, rfl, _, rw_val p L g w per it v kk, rfl⟩)⟩
    rw [hx, wideU4_fin, add64_ofNat, Nat.add_assoc]
    exact lacc_loc hp (by omega) 4
  case ptS per b it =>
    simp only [Ev] at hev
    rcases hev with ⟨v', hv', hk⟩ | ⟨f, hk⟩
    swap
    · cases hk
    simp only [Kind.wr.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hv : v' = .bits 64 (rv p L g w ⟨.ptS per b it, v, kk⟩ (ptRegs (pk per b)).ad) := by
      simp [storeValue, Value.bytes, pure, Except.pure] at hv'; exact hv'.symm
    subst hv
    refine ⟨o, hl, .inr (.inr ⟨?_, rfl, _, pt_row hp (hA.head (by cases per <;> rfl)) hA.lp hA.lr,
      rfl⟩)⟩
    rcases hz with ⟨-, h⟩ | ⟨h, -⟩
    · simp [lacc] at h
    · exact h
  all_goals
    simp only [Ev, Epilogue.Ev, Site.toE] at hev
    shape_destruct hev
    all_goals contradiction

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

/-- The earlier stores of a lane, from its earlier states' address words. -/
theorem stores_before {k : Nat} (IH : ∀ j ≤ k, ∀ b d n,
      Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) → n .ub = 0 →
      AddrOk p L X g j d) :
    ∀ j < k, ∀ a bs, X.Writes (g, j) a bs → StoreOk p L g a bs := by
  intro j hj a bs ⟨pc, he⟩
  have hG := good hp hX hw hg rfl j
  rcases good_cases hp hX he (fun _ _ h => by cases h) hG with ⟨s, n, hσ, hS, -⟩ |
    ⟨b, d, n, hσ, hb, hub, -, -⟩
  · exact (start_no_wr (start_fired hp hX he hσ).1 hS (.inl rfl)).elim
  · exact store_ok hp (IH j hj.le b d n hσ hub) (lfired hp hX he hσ).1 a bs rfl

/-- **A local load of a loader state** reads the lane's last store at its offset. -/
theorem load_at {k : Nat} {b : Bool} {d : D} {n : Cls → Nat} {a : Acc}
    {bs : List (Option Byte)} {pc : Nat} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hJ : Loader.Ref p L g (wOf b) (d, lcn n))
    (IH : ∀ j ≤ k, ∀ b d n,
      Frame.stateAt (thread p L) X g j = some (some (linj p L g b d n)) → n .ub = 0 →
      AddrOk p L X g j d) {o q : Nat} (hl : a.loc = ⟨.local, g, L.localBase + o + q⟩)
    (hz : a.size = 4) (hq : q = 0 ∨ q = 4 ∧ (o = 0 ∨ o = 8 ∨ o = 32 ∨ o = 40))
    (hoff : o ∈ lstOffs) (hlst : ∀ kk A, 1 ≤ lstAt d.site kk A o) :
    ∃ j a' bs', LastAt L X g k o j a' bs' ∧ StoreOk p L g a' bs' ∧ bs.length = 4 ∧
      ∀ i < 4, bs[i]? = some (bs'[q + i]?) := by
  obtain ⟨k0, A0, -, hC⟩ := hJ.refE
  have hls := hC.lst o hoff
  have h0 : 0 < n (.load (.lst o)) := by
    have := hlst k0 A0; simp only [lcn] at hls; omega
  obtain ⟨j0, hj0, f0, hf0, hc0⟩ := exists_of_count hσ h0
  obtain ⟨pc0, kind0⟩ := f0
  obtain ⟨a0, bs0, rfl, hl0⟩ : ∃ a0 bs0, kind0 = .wr a0 bs0 ∧
      a0.loc = ⟨.local, g, L.localBase + o⟩ := by
    cases kind0 <;> simp [Proof.cls, Loader.cls] at hc0
    exact ⟨_, _, rfl, hc0⟩
  have hall := stores_before hp hX hg hw IH
  obtain ⟨j, a', bs', hL⟩ := exists_last hj0 ⟨pc0, hf0⟩ hl0
  have hr : X.Reads (g, k) a bs := ⟨pc, he⟩
  have hlen := (hX.rf (.thread (g, k)) a bs (Or.inl hr)).1
  exact ⟨j, a', bs', hL, hall j hL.1 _ _ hL.2.1, by omega, load_last hX hall hr hl hz hL hq⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
