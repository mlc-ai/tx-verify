-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Addr
public import Lemmas.Tcgen05.TcFence
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A row shuffle receives a row address's low word

A packet's row shuffle `xl` takes the low word of a row's address from lane `i mod 8` of its group.
The source lane made its shuffle of the same count (`lshfl_src`); two lanes of one CTA at shuffle
states with one count are both in a packet at the same shuffle of it (`pkt_same`: the scan's
shuffles come before the CTA's choice, the packets' after it, `bband`), so the source lane was at
the same row's `xl` and sent its recorded low word `l0` (`rv_xl`). With the source lane's
row-address pattern (`AOk`) at that state, the received word is a multiple of 16 (`recv_low`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (Picked)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat} {w : Nat}

/-- **Two lanes of one CTA at a packet's shuffle and at a shuffle with one shuffle count** are
both at a packet's shuffle, the same one of their packets. -/
theorem pkt_same {d d' : D} {ns nv nc ns' nv' nc' : Nat} (hc : g / L.block = h / L.block)
    (hF : LFits p L g d ns nv nc) (hp : d.site.pkt = true)
    (hF' : LFits p L h d' ns' nv' nc') (hs' : d'.site.lsh = true) (hn : ns = ns') :
    d'.site.pkt = true ∧ pktSh d'.site = pktSh d.site ∧ nv = 1 ∧ nv' = 1 := by
  rcases lsh_cases hs' with hp' | hse'
  · obtain ⟨R, bal, hPk, hns, hnv, hlt⟩ := bband hF (pkt_blk hp)
    obtain ⟨R', bal', hPk', hns', hnv', hlt'⟩ := bband hF' (pkt_blk hp')
    obtain ⟨rfl, rfl⟩ := (Picked.cta hc hPk).unique hPk'
    have h1 := pkt_pktSh hp
    have h2 := pkt_pktSh hp'
    refine ⟨hp', ?_, hnv, hnv'⟩
    omega
  · exfalso
    have hs : d.site.lsh = true := by simp [Site.lsh, hp]
    obtain ⟨he, -⟩ := lshfl_same hc.symm hF' hse' hF hs hn.symm
    rw [he] at hp
    rw [shfl_not_pkt hse'] at hp
    cases hp

/-- The word a row shuffle `xl` sends: the state's low word of the row address. -/
theorem rv_xl (p : Params) (L : Launch) (g w : Nat) (per : Per) (b : Bool) (i : Fin 16) (v : V)
    (kk : Fin 2) : rv p L g w ⟨.xl per b i, v, kk⟩ (xSrc (pk per b) i false) = v.l0 := by
  cases per <;> cases b <;> fin_cases i <;> rfl

theorem pktSh_xl {s : Site} {per : Per} {b : Bool} {i : Fin 16} (hp : s.pkt = true)
    (h : pktSh s = pktSh (.xl per b i)) : ∃ per' b', s = .xl per' b' i := by
  cases s <;> simp only [Site.pkt, Bool.false_eq_true] at hp
  · rename_i per' b' i'
    refine ⟨per', b', ?_⟩
    simp only [pktSh] at h
    have : i' = i := Fin.ext (by omega)
    subst this; rfl
  · simp only [pktSh] at h; omega

set_option maxHeartbeats 4000000 in
/-- **A row shuffle receives a multiple of 16**, given the row-address pattern at the source
lanes' states with at most the receiver's collectives before them. -/
theorem recv_low (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = w) {k pc : Nat} {mode : ShflMode}
    {a recv : Value} {bb c : Nat} {ok : Bool} {b : Bool} {d : D} {n : Cls → Nat}
    {per : Per} {v : Bool} {i : Fin 16}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a bb c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)))
    (IH : GoodUpTo p L w X (n .shfl + n .vote)) (hs : d.site = .xl per v i)
    (hA : ∀ h j b' d' n', InWarp L w h → j < (X.tr h).length →
      ((X.tr h).take j).countP isColl ≤ n .shfl + n .vote →
      Frame.stateAt (thread p L) X h j = some (some (linj p L h b' d' n')) → AOk d'.v) :
    ∀ x, recv = .bits 32 x → x.toNat % 16 = 0 := by
  intro x hx
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs⟩ := lshfl_src hp hX hg hw he hσ hF IH
  set src := g - laneOf L g + (shflSource mode (laneOf L g) bb c).1 with hsrc
  have hl := Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) bb c
  obtain ⟨hsg, hsw, hsc, -, -⟩ := lane_facts hp hg hw hl
  have h3 := lfits_three hF
  obtain ⟨b1, d1, n1, hσ1, hb1, -, hF1, hev1, hs1, hv1⟩ := role_at hp hX hj hG
    (.inr (.inr ⟨rfl, by rw [hjs]; exact h3⟩))
  have hlsh := (lev_class hev1).1 rfl
  have hpkt : d.site.pkt = true := by rw [hs]; rfl
  obtain ⟨hp1, hsh1, hnv, hnv1⟩ := pkt_same hsc.symm hF hpkt hF1 hlsh (by rw [← hs1, hjs])
  rw [hs] at hsh1
  obtain ⟨per1, v1, hs1'⟩ := pktSh_xl hp1 hsh1
  have hA1 := hA src j b1 d1 n1 ⟨hsg, hsw⟩ (List.getElem?_eq_some_iff.mp
    (show (X.tr src)[j]? = _ from hj)).1 (by
    rw [countColl]; omega) hσ1
  -- the source's event sends its low word
  obtain ⟨s1, v1', kk1⟩ := d1
  simp only at hs1'
  subst hs1'
  simp only [Ev] at hev1
  obtain ⟨recv1, ok1, hk1⟩ := hev1
  simp only [Kind.shfl.injEq] at hk1
  obtain ⟨-, hrecv, -⟩ := hk1
  rw [rv_xl] at hrecv
  rw [hrecv] at hx
  simp only [Value.bits.injEq, true_and] at hx
  rw [← hx]
  exact hA1.1

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
