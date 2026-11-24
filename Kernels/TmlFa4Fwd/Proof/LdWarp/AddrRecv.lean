-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrLocal
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrStep
import Kernels.TmlFa4Fwd.Proof.LdWarp.PosFact
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.AddrTrace
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Recv
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Lemmas.Flow.NthEv
import Lemmas.Step.WarpShfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A row's two shuffles receive one row address

The shuffles `xl` and `xh` of a row read one source lane, which is at the same two shuffles, one
after the other, with its address words unchanged; so the two received words are the halves of the
source lane's row address (`recv_ok`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat} {w : Nat}

/-- The source lane of a row's shuffles. -/
def srcOf (L : Launch) (g : Nat) (i : Fin 16) : Nat :=
  g - laneOf L g + (shflSource .idx (laneOf L g) (i.val % 8) 6175).1

theorem rv_xh (p : Params) (L : Launch) (g w : Nat) (per : Per) (b : Bool) (i : Fin 16) (v : V)
    (kk : Fin 2) : rv p L g w ⟨.xh per b i, v, kk⟩ (xSrc (pk per b) i true) = v.l1 := by
  cases per <;> cases b <;> fin_cases i <;> rfl

theorem pktSh_xh {s : Site} {per : Per} {b : Bool} {i : Fin 16} (hp : s.pkt = true)
    (h : pktSh s = pktSh (.xh per b i)) : ∃ per' b', s = .xh per' b' i := by
  cases s <;> simp only [Site.pkt, Bool.false_eq_true] at hp
  · simp only [pktSh] at h; omega
  · rename_i per' b' i'
    refine ⟨per', b', ?_⟩
    simp only [pktSh] at h
    have : i' = i := Fin.ext (by omega)
    subst this; rfl

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

/-- **The source state of a packet's shuffle.** -/
theorem pkt_recv {k pc : Nat} {a recv : Value} {bb c : Nat} {ok : Bool} {mode : ShflMode}
    {b : Bool} {d : D} {n : Cls → Nat}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a bb c recv ok⟩)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit))) (hpk : d.site.pkt = true) :
    ∃ src j b1 d1 n1 e1, src = g - laneOf L g + (shflSource mode (laneOf L g) bb c).1 ∧
      src < L.threads ∧ Prologue.warpIndex L src = Prologue.warpIndex L g ∧
      X.get (src, j) = some e1 ∧
      Frame.stateAt (thread p L) X src j = some (some (linj p L src b1 d1 n1)) ∧
      n1 .ub = 0 ∧ Ev p L src (wOf b1) d1 e1 ∧ d1.site.pkt = true ∧ pktSh d1.site = pktSh d.site ∧
      ((X.tr src).take j).countP Execution.isShfl = ((X.tr g).take k).countP Execution.isShfl ∧
      (∃ pc' b' c' r' o', e1 = ⟨pc', .shfl mode recv b' c' r' o'⟩) := by
  have hcoll : isColl ⟨pc, .shfl mode a bb c recv ok⟩ = true := rfl
  have hup := upTo_of_prev (fun _ => ref_init) he hcoll
    (fun j _ hjw => not_bad_of_good (good hp hX hw hjw.1 hjw.2) j.2)
  rw [countColl ((X.tr g).take k), (counts hσ).1, (counts hσ).2] at hup
  obtain ⟨j, pc', b', c', r', o', hj, hG, hjs⟩ := lshfl_src hp hX hg rfl he hσ hF hup
  have hl := Step.shflSource_lt mode (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) bb c
  obtain ⟨hsg, hsw, hsc, -, -⟩ := lane_facts hp hg rfl hl
  have h3 := lfits_three hF
  obtain ⟨b1, d1, n1, hσ1, hb1, -, hF1, hev1, hs1, hv1⟩ := role_at hp hX hj hG
    (.inr (.inr ⟨rfl, by rw [hjs]; exact h3⟩))
  have hlsh := (lev_class hev1).1 rfl
  obtain ⟨hp1, hsh1, hnv, hnv1⟩ := pkt_same hsc.symm hF hpk hF1 hlsh (by rw [← hs1, hjs])
  exact ⟨_, j, b1, d1, n1, _, rfl, hsg, hsw, hj, hσ1, ub_zero hX hj hσ1, hb1 ▸ hev1, hp1, hsh1,
    by rw [hjs, (counts hσ).1], _, _, _, _, _, rfl⟩

end

/-- What a packet's row shuffles have received before position `k`. -/
def RecvOk (p : Params) (L : Launch) (X : Execution) (g k : Nat) (d : D) : Prop :=
  match d.site with
  | .xh _ _ i => ∃ j b1 d1 n1, srcOf L g i < L.threads ∧
      Frame.stateAt (thread p L) X (srcOf L g i) j = some (some (linj p L (srcOf L g i) b1 d1 n1)) ∧
      n1 .ub = 0 ∧ j < (X.tr (srcOf L g i)).length ∧ (∃ per b, d1.site = .xl per b i) ∧
      ((X.tr (srcOf L g i)).take j).countP Execution.isShfl + 1 =
        ((X.tr g).take k).countP Execution.isShfl ∧ d.v.x0 = d1.v.l0
  | .cp _ _ i _ => Halves p d.v.x0 d.v.x1 ∧ ∃ j b1 d1 n1, srcOf L g i < L.threads ∧
      Frame.stateAt (thread p L) X (srcOf L g i) j = some (some (linj p L (srcOf L g i) b1 d1 n1)) ∧
      n1 .ub = 0 ∧ j < (X.tr (srcOf L g i)).length ∧ (∃ per b, d1.site = .xl per b i) ∧
      ((X.tr (srcOf L g i)).take j).countP Execution.isShfl + 2 =
        ((X.tr g).take k).countP Execution.isShfl ∧ d.v.x0 = d1.v.l0 ∧ d.v.x1 = d1.v.l1
  | _ => True

def xhChk (_ : Bool) (s s' : Site) : Bool :=
  match s' with
  | .xh _ _ i => (match s with | .xl _ _ i' => decide (i = i') | _ => false)
  | .cp _ _ i _ => (match s with | .xh _ _ i' | .cp _ _ i' _ => decide (i = i') | _ => false)
  | _ => true
theorem xh_edges : Edges xhChk := by unfold Edges AllSites; decide +kernel

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
  (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
include hp hX hg hw

set_option maxHeartbeats 2000000 in
/-- **A row's two received words are the halves of a row address.** -/
theorem recv_ok : ∀ k, k ≤ (X.tr g).length → ∀ b d n,
    Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)) → n .ub = 0 →
    RecvOk p L X g k d := by
  refine pos_at (I := fun k d => RecvOk p L X g k d) (fun k b => trivial)
    (fun k b d n e d' he hσ hub hJ hF hev hnu hn hm IH => ?_) hp hX hg hw
  obtain ⟨s, v, kk⟩ := d
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hone : Execution.isShfl e = true → ((X.tr g).take (k + 1)).countP Execution.isShfl =
      ((X.tr g).take k).countP Execution.isShfl + 1 := by
    intro h
    rw [List.take_add_one, show (X.tr g)[k]? = some e from he, List.countP_append]
    simp [h]
  by_cases hs : ∃ per bb i, s = .xl per bb i
  · obtain ⟨per, bb, i, rfl⟩ := hs
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨recv, ok, hk0⟩ := hev0
    obtain ⟨pc, kind⟩ := e
    simp only at hk0
    subst hk0
    simp only [succ] at hn
    obtain ⟨y, rfl, rfl⟩ := word32_inv hn
    obtain ⟨src, j, b1, d1, n1, e1, rfl, hsg, hsw, hj, hσ1, hub1, hev1, hp1, hsh1, hcnt, he1⟩ :=
      pkt_recv hp hX hg hw he hσ hF rfl
    obtain ⟨per1, v1, hs1⟩ := pktSh_xl hp1 hsh1
    obtain ⟨pc', b', c', r', o', rfl⟩ := he1
    refine ⟨j, b1, d1, n1, hsg, hσ1, hub1, (List.getElem?_eq_some_iff.mp hj).1, ⟨per1, v1, hs1⟩,
      ?_, ?_⟩
    · rw [hone rfl]; exact congrArg (· + 1) hcnt
    · obtain ⟨s1, v1', kk1⟩ := d1
      simp only at hs1
      subst hs1
      simp only [Ev] at hev1
      obtain ⟨recv1, ok1, hk1⟩ := hev1
      simp only [Kind.shfl.injEq] at hk1
      obtain ⟨-, hrecv, -⟩ := hk1
      rw [rv_xl] at hrecv
      simp only [Value.bits.injEq, true_and] at hrecv
      exact hrecv
  by_cases hs2 : ∃ per bb i, s = .xh per bb i
  · obtain ⟨per, bb, i, rfl⟩ := hs2
    obtain ⟨j0, b0, d0, n0, hsg0, hσ0, hub0, hjl0, ⟨per0, v0, hs0⟩, hcnt0, hx0⟩ :=
      IH k le_rfl b _ n hσ hub
    have hev0 := hev
    simp only [Ev] at hev0
    obtain ⟨recv, ok, hk0⟩ := hev0
    obtain ⟨pc, kind⟩ := e
    simp only at hk0
    subst hk0
    simp only [succ] at hn
    obtain ⟨y, rfl, rfl⟩ := word32_inv hn
    obtain ⟨src, j, b1, d1, n1, e1, hsrc, hsg, hsw, hj, hσ1, hub1, hev1, hp1, hsh1, hcnt, he1⟩ :=
      pkt_recv hp hX hg hw he hσ hF rfl
    have hsrc' : src = srcOf L g i := hsrc
    subst hsrc'
    obtain ⟨per1, v1, hs1⟩ := pktSh_xh hp1 hsh1
    obtain ⟨pc', b', c', r', o', rfl⟩ := he1
    -- the source's event at `j0` is its low shuffle, and the next one its high shuffle
    obtain ⟨⟨pc0, kind0⟩, he0⟩ : ∃ e0, X.get (srcOf L g i, j0) = some e0 :=
      ⟨_, List.getElem?_eq_getElem hjl0⟩
    have hev00 := (lfired hp hX he0 hσ0).1
    obtain ⟨s0, vv0, kk0⟩ := d0
    simp only at hs0
    subst hs0
    simp only [Ev] at hev00
    obtain ⟨recv0, ok0, hk00⟩ := hev00
    subst hk00
    have hww : Prologue.warpIndex L (srcOf L g i) = 14 ∨
        Prologue.warpIndex L (srcOf L g i) = 15 := by rw [hsw]; exact hw
    have hA0 := addr_ok hp hX hsg hww j0 hjl0.le b0 _ n0 hσ0 hub0
    obtain ⟨yy, hy, h0, h1⟩ := hA0.row rfl
    -- positions
    have hc0 : ((X.tr (srcOf L g i)).take (j0 + 1)).countP Execution.isShfl =
        ((X.tr (srcOf L g i)).take j0).countP Execution.isShfl + 1 := by
      rw [List.take_add_one, show (X.tr (srcOf L g i))[j0]? = _ from he0, List.countP_append]
      simp [Execution.isShfl]
    have hlt : j0 < j := by
      by_contra hcon
      have : ((X.tr (srcOf L g i)).take j).countP Execution.isShfl ≤
          ((X.tr (srcOf L g i)).take j0).countP Execution.isShfl :=
        (List.take_sublist_take_left (by omega)).countP_le
      omega
    have hjl : j < (X.tr (srcOf L g i)).length := (List.getElem?_eq_some_iff.mp hj).1
    have hG := good hp hX hww hsg rfl (j0 + 1)
    have hst := Frame.stateAt_succ (C := thread p L)
      (show (X.tr (srcOf L g i))[j0]? = _ from he0)
    rw [hσ0] at hst
    change _ = (thread p L (srcOf L g i)).next _ _ at hst
    rw [next_linj] at hst
    obtain ⟨z, rfl⟩ : ∃ z, recv0 = .bits 32 z := by
      by_contra hno
      have : (Loader.F p L (srcOf L g i) b0).next ⟨.xl per0 v0 i, vv0, kk0⟩
          ⟨pc0, .shfl .idx (.bits 32 (rv p L (srcOf L g i) (wOf b0) ⟨.xl per0 v0 i, vv0, kk0⟩
            (xSrc (pk per0 v0) i false))) (i.val % 8) 6175 recv0 ok0⟩ = some none := by
        simp only [Loader.F, code, succ]
        unfold word32
        split
        · exact (hno ⟨_, rfl⟩).elim
        · rfl
      rw [this] at hst
      exact hG.1 hst
    have hst' : Frame.stateAt (thread p L) X (srcOf L g i) (j0 + 1) =
        some (some (linj p L (srcOf L g i) b0 ⟨.xh per0 v0 i, { vv0 with x0 := z }, 0⟩
          (Code.bump (Proof.cls L (srcOf L g i)) n0 ⟨pc0, .shfl .idx (.bits 32
            (rv p L (srcOf L g i) (wOf b0) ⟨.xl per0 v0 i, vv0, kk0⟩
            (xSrc (pk per0 v0) i false))) (i.val % 8) 6175 (.bits 32 z) ok0⟩))) := hst
    obtain ⟨⟨pc2, kind2⟩, he2⟩ : ∃ e2, X.get (srcOf L g i, j0 + 1) = some e2 :=
      ⟨_, List.getElem?_eq_getElem (show j0 + 1 < (X.tr (srcOf L g i)).length by omega)⟩
    have hev2 := (lfired hp hX he2 hst').1
    simp only [Ev] at hev2
    obtain ⟨recv2, ok2, hk2⟩ := hev2
    subst hk2
    have hj01 : j0 + 1 = j := nthEv_unique (p := Execution.isShfl) he2
      rfl hj rfl (by omega)
    subst hj01
    rw [hst'] at hσ1
    have hd1 : d1 = ⟨.xh per0 v0 i, { vv0 with x0 := z }, 0⟩ := by
      simp only [Option.some.injEq, linj, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.injEq] at hσ1
      obtain ⟨⟨h, hh⟩, -⟩ := hσ1
      cases h
      exact (eq_of_heq hh).symm
    subst hd1
    simp only [Ev] at hev1
    obtain ⟨recv1, ok1, hk1⟩ := hev1
    simp only [Kind.shfl.injEq] at hk1
    obtain ⟨-, hrecv, -⟩ := hk1
    rw [rv_xh] at hrecv
    simp only [Value.bits.injEq, true_and] at hrecv
    have hx1 : y = vv0.l1 := hrecv
    refine ⟨⟨yy, hy, ?_, ?_⟩, j0, b0, _, n0, hsg0, hσ0, hub0, hjl0, ⟨per0, v0, rfl⟩, ?_, hx0, hx1⟩
    · show v.x0.toNat = _
      rw [show v.x0 = vv0.l0 from hx0]; exact h0
    · show y.toNat = _
      rw [hrecv]; exact h1
    · rw [hone rfl]
      omega
  · -- no other step receives a word
    have hcpc : ∀ {per bb i c}, Ev p L g (wOf b) ⟨.cp per bb i c, v, kk⟩ e →
        ((X.tr g).take (k + 1)).countP Execution.isShfl =
          ((X.tr g).take k).countP Execution.isShfl := by
      intro per bb i c hev
      simp only [Ev] at hev
      rw [List.take_add_one, show (X.tr g)[k]? = some e from he, List.countP_append]
      obtain ⟨pc, kind⟩ := e
      rcases hev with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [Execution.isShfl]
    have hIH := IH k le_rfl b _ n hσ hub
    have hwr : ∀ f, wr s f = false → f.same v d'.v := hm.keep
    rcases hm.edge with h | h
    · have hs' : d'.site = s := h
      unfold RecvOk
      rw [hs']
      cases s <;> try trivial
      · exact (hs2 ⟨_, _, _, rfl⟩).elim
      · have e0 : d'.v.x0 = v.x0 := hwr .x0 rfl
        have e1 : d'.v.x1 = v.x1 := hwr .x1 rfl
        simp only
        rw [e0, e1, hcpc hev]
        exact hIH
    · have hc := xh_edges.ok h
      obtain ⟨s', v', kk'⟩ := d'
      unfold RecvOk
      cases s' <;> try trivial
      · exfalso
        simp only [xhChk] at hc
        cases s <;> simp only [Bool.false_eq_true] at hc
        exact hs ⟨_, _, _, rfl⟩
      · simp only [xhChk] at hc
        cases s <;> simp only [Bool.false_eq_true] at hc
        · exact (hs2 ⟨_, _, _, rfl⟩).elim
        · have e0 : v'.x0 = v.x0 := hwr .x0 rfl
          have e1 : v'.x1 = v.x1 := hwr .x1 rfl
          simp only [decide_eq_true_eq] at hc
          subst hc
          simp only
          rw [e0, e1, hcpc hev]
          exact hIH

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
