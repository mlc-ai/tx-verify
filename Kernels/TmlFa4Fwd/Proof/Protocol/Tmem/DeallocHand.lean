-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Isa.Tc
public import Core.Memory.Order
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.AccBar2
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Lemmas.Kernel.BarUpTo
import Kernels.TmlFa4Fwd.Proof.Mma.Warp
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocBefore
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2Exit
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.MmaDealloc
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Lemmas.Flow.NthEv

@[expose] public section

/-! # The deallocation hand-off through barrier 2's second rendezvous

A deallocation of lane `z` of warp 12 follows its two barrier-2 syncs (`dealloc_bar2`, every
barrier-2 event of warp 12 is a sync: `w12_sync`). A softmax or correction lane `h` of the CTA
with one barrier-2 event before an access at `f` made its barrier-2 arrival of ordinal 1 at some
`i > f` (`NamedBar.Sources.member_arrival_any`, its exit following two barrier-2 events:
`sc_exit_bar2`), and every event of `h` before `i` precedes the deallocation in causality
(`Frame.Handoff.of_bar_upTo_ord` with bound 2, producers the lanes of warps 0 to 11, consumers
those of warp 12): `dealloc_handoff`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

/-- Every barrier-2 event of warp 12 is a sync. -/
theorem w12_sync {h j pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (h, j) = some ⟨pc, .bar 2 cnt mode⟩) (h12 : Prologue.warpIndex L h = 12) :
    mode = .sync := by
  obtain ⟨d, n, hσ⟩ := w12_bar2 hp hX hFw he h12
  have := mma_bar (Mma.mfired hp hX he hσ).1
  simp only [Prod.mk.injEq] at this
  exact this.2.2

set_option maxHeartbeats 8000000 in
/-- **The second barrier-2 arrival of a lane of warps 0 to 11 of a deallocating CTA, and
its events before that arrival precede the deallocation.** -/
theorem dealloc_ord1 {z j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da nn : Nat}
    (hd : X.get (z, j) = some ⟨pc, .tc (.resource grp dst (.dealloc da nn))⟩) {h : Nat}
    (hh : h < L.threads) (hcta : z / L.block = h / L.block)
    (hw : Prologue.warpIndex L h < 12) :
    ∃ i pci mi, X.get (h, i) = some ⟨pci, .bar 2 (some 416) mi⟩ ∧
      ((X.tr h).take i).countP (Execution.isBarId 2) = 1 ∧
      ∀ w, w < i → baseCausality L X (h, w) (z, j) := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hz := Frame.lt_of_get hX hd
  have hjlen : j < (X.tr z).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr z)[j]? = _ from hd)).1
  -- the deallocating lane is of warp 12
  obtain ⟨σ, -, hJ, hi, hev⟩ := ev_at hp hX hT hF hd (by intro f hf; cases hf)
  obtain ⟨d2, n2, rfl⟩ := tev_res hJ hi hev rfl
  have h12z := jr_mma hJ
  have hz2 := dealloc_bar2 hp hX hFw hd
  -- its second barrier-2 event
  obtain ⟨b2, ev, hbget, hbid, hbc⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 2)
    (show 1 + 1 ≤ ((X.tr z).take j).countP (Execution.isBarId 2) by omega)
  have hb2j : b2 < j := by
    have := (List.getElem?_eq_some_iff.mp hbget).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hb2j.le] at hbc
  obtain ⟨pcb, cntb, mb, rfl⟩ := NamedBar.isBarId_form hbid
  have hgb : X.get (z, b2) = some ⟨pcb, .bar 2 cntb mb⟩ := by
    change (X.tr z)[b2]? = _
    rw [← hbget, List.getElem?_take, ite_eq_left hb2j]
  have hmb := w12_sync hp hX hFw hgb h12z
  subst hmb
  -- the lane's arrival of ordinal 1
  obtain ⟨i, pci, mi, hi', hci⟩ := NamedBar.Sources.member_arrival_any hX
    (srcs2 hp hX hT hF) (shape2 hp) (f := (z, b2)) hgb (by simp only; omega) hcta.symm
    (by simp only [Finset.mem_range]; have : h % L.block / 32 < 12 := hw; omega)
    (fun hex => by
      obtain ⟨jx, pcx, hx⟩ := hex
      have h2 := sc_exit_bar2 hp hX hFw hx hw
      obtain ⟨i, ev', hi, hbi, hci⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 2)
        (show 1 + 1 ≤ (X.tr h).countP (Execution.isBarId 2) by omega)
      obtain ⟨pci, cnti, mi, rfl⟩ := NamedBar.isBarId_form hbi
      have hcnti := (srcs2 hp hX hT hF (h, i) pci cnti ⟨mi, hi⟩ hh).2
      subst hcnti
      exact ⟨i, pci, mi, hi, by simp only at hci ⊢; omega⟩)
  simp only at hci
  rw [hbc] at hci
  have H := Frame.Handoff.of_bar_upTo_ord hX (srcs2 hp hX hT hF) (shape2 hp)
    (syncs := fun g => Prologue.warpIndex L g = 12) (prod := fun g => Prologue.warpIndex L g < 12)
    2 (fun h' j' pc' cnt' mode' h12 hget _ => w12_sync hp hX hFw hget h12)
    (fun g' _ _ hw' hex => by
      obtain ⟨jx, pcx, hx⟩ := hex
      exact sc_exit_bar2 hp hX hFw hx hw')
  refine ⟨i, pci, mi, hi', hci, fun w hwi => ?_⟩
  refine H h z w j ⟨⟨hh, hz, hcta.symm⟩, ?_, h12z, hw⟩ hjlen ?_
  · simp only [Finset.mem_range]; have : h % L.block / 32 < 12 := hw; omega
  · have h1 := countP_take_mono (Execution.isBarId 2) (X.tr h) (show w + 1 ≤ i by omega)
    simp only
    omega

set_option maxHeartbeats 8000000 in
/-- **The deallocation hand-off.** -/
theorem dealloc_handoff {z j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {da nn : Nat}
    (hd : X.get (z, j) = some ⟨pc, .tc (.resource grp dst (.dealloc da nn))⟩) {h f pcf : Nat}
    {k : Kind} (he : X.get (h, f) = some ⟨pcf, k⟩) (hk : IsAcc k)
    (hcta : z / L.block = h / L.block) (hw : Prologue.warpIndex L h < 12)
    (hf1 : ((X.tr h).take f).countP (Execution.isBarId 2) = 1) :
    ∃ i pci mi, X.get (h, i) = some ⟨pci, .bar 2 (some 416) mi⟩ ∧
      ((X.tr h).take i).countP (Execution.isBarId 2) = 1 ∧ f < i ∧
      ∀ w, w < i → baseCausality L X (h, w) (z, j) := by
  have hh := Frame.lt_of_get hX he
  obtain ⟨i, pci, mi, hi', hci, hpre⟩ := dealloc_ord1 hp hX hFw hd hh hcta hw
  have hfi : f < i := by
    by_contra hc
    rcases Nat.lt_or_ge i f with hif | hif
    · have h1 := countP_take_mono (Execution.isBarId 2) (X.tr h) (show i + 1 ≤ f by omega)
      rw [List.take_add_one, show (X.tr h)[i]? = _ from hi', Option.toList_some,
        List.countP_append, hci] at h1
      simp [Execution.isBarId] at h1
      omega
    · have : i = f := by omega
      subst this
      rw [hi'] at he
      simp only [Option.some.injEq, Event.mk.injEq] at he
      rw [← he.2] at hk
      exact hk
  exact ⟨i, pci, mi, hi', hci, hfi, hpre⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
