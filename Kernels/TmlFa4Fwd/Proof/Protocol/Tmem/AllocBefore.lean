-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Tmem.AccessClass
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Startup.Machine
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Lemmas.Kernel.BarUpTo
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.AccBar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.AllocPre
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Bar2First
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Entry
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Every Tensor Memory access follows lane 0 of warp 12's allocation (`Life.alloc_before`)

The allocation is handed to every access through barrier 2's first rendezvous
(`Frame.Handoff.of_bar_upTo_ord` with bound 1):

* the producer is lane 0 of warp 12 of the access's CTA, whose allocation has no barrier-2 event
  before or at it (`lane0_alloc`), and which exits only from a state of its code past `bar1`, so
  after a barrier-2 event (`w12_exit`);
* the consumer's first barrier-2 event is a sync (`first_bar2_sync`), and every access has a
  barrier-2 event of its lane before it (`acc_bar2`);
* lane 0 reached a state of its code, from which `lane0_alloc` finds the allocation: the
  consumer's first barrier-2 event completed, so lane 0 made its barrier-2 arrival of ordinal 0
  (`NamedBar.Sources.member_arrival_any`), fired from a state of its code (`w12_bar2`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem start_noexit {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n)) {pc : Nat}
    (hev : Startup.Ev L g s ⟨pc, .exit⟩) : False := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site
  case bar => simp only [Startup.Ev] at hev; cases hev
  case enter r => exact absurd rfl (jr_start_site hJ r)
  case sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk'⟩ := hev <;> cases hk'
  all_goals simp only [Startup.Ev] at hev
  all_goals first
    | (cases hev; done)
    | (rcases hev with ⟨_, _, -, hk'⟩ | ⟨_, hk'⟩ <;> cases hk')
    | (rcases hev with ⟨_, _, hk'⟩ | ⟨_, hk'⟩ <;> cases hk')

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hFw : Follow p L X)
include hp hX hFw

set_option maxHeartbeats 8000000 in
/-- **An event of a lane of warp 12 that the allocation prefix and the startup do not fire is
fired from a state of the role's code.** -/
theorem w12_code {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (h12 : Prologue.warpIndex L g = 12) (hub : ∀ f, e.kind ≠ .ub f)
    (hns : ∀ s n, JR p L g (.inl s, n) → ¬ TEv p L g (.inl s, n) e) (hnp : ¬ Mma.PreEv e) :
    ∃ d n, Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)) := by
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ :=
    ev_at hp hX (table_shape_of hp hFw) (table_followed hp hX hFw) he hub
  rcases σ1 with s | ⟨i, d⟩
  · exact (hns s n hJ hev).elim
  cases i with
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · exact (hnp hev).elim
    · exact ⟨d, n, hσ⟩
  | _ =>
    exfalso
    simp only [JR_eq, h12] at hJ
    unfold RefAll at hJ
    split_ifs at hJ <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]

/-- A barrier-2 event of a lane of warp 12 is fired from a state of the role's code. -/
theorem w12_bar2 {k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 2 cnt mode⟩) (h12 : Prologue.warpIndex L g = 12) :
    ∃ d n, Frame.stateAt (thread p L) X g k = some (some (Mma.minj p L g d n)) := by
  refine w12_code hp hX hFw he h12 (by intro f hf; cases hf)
    (fun s n hJ hev => ?_) ?_
  · have := start_barOps hJ hev
    simp at this
  · rintro (⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩) <;> cases hk

/-- **A lane of warp 12 exits after a barrier-2 event.** -/
theorem w12_exit {j pc : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩)
    (h12 : Prologue.warpIndex L g = 12) : 1 ≤ (X.tr g).countP (Execution.isBarId 2) := by
  obtain ⟨d, n, hσ⟩ := w12_code hp hX hFw he h12 (by intro f hf; cases hf)
    (fun s n hJ hev => start_noexit hJ hev)
    (by rintro (⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩) <;> cases hk)
  have hs : d.site ≠ .bar1 := by
    intro hs
    have hev := (Mma.mfired hp hX he hσ).1
    obtain ⟨s0, v0⟩ := d
    simp only at hs
    subst hs
    simp only [Mma.Ev] at hev
    cases hev
  obtain ⟨j', hj', pc', hget⟩ := mma_bar1_before hp hX he hσ hs
  have h1 := bar2_pos hj' hget
  exact h1.trans (List.take_sublist _ _).countP_le

set_option maxHeartbeats 8000000 in
/-- **Every MMA, load and store follows lane 0 of warp 12's allocation** of its CTA, in
causality, and that lane has an event after the allocation. -/
theorem alloc_before {e : EvId} {a : Nat} {vals : List Value} {sh : TcShape}
    (hk : Tmem.Access.IsMma X e ∨ X.TLd e a vals sh ∨ X.TSt e a vals sh) :
    ∃ j pc grp dst n, X.get ((e.1 / L.block) * L.block + 12 * 32, j) =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ ∧
      j + 1 < (X.tr ((e.1 / L.block) * L.block + 12 * 32)).length ∧
      baseCausality L X ((e.1 / L.block) * L.block + 12 * 32, j) e := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hb := hp.block
  obtain ⟨h, f⟩ := e
  obtain ⟨pc, kd, he, hacc⟩ : ∃ pc kd, X.get (h, f) = some ⟨pc, kd⟩ ∧ IsAcc kd := by
    rcases hk with ⟨_, _, _, _, pc, he⟩ | ⟨pc, he⟩ | ⟨pc, he⟩ <;> exact ⟨pc, _, he, trivial⟩
  have hg := Frame.lt_of_get hX he
  have hflen : f < (X.tr h).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr h)[f]? = _ from he)).1
  have hcnt := acc_bar2 hp hX hFw hacc he
  -- the consumer's first barrier-2 event
  obtain ⟨b, ev, hbget, hbid, hbc⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 2)
    (show 0 + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId 2) by omega)
  have hbf : b < f := by
    have := (List.getElem?_eq_some_iff.mp hbget).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hbf.le] at hbc
  obtain ⟨pcb, cntb, mb, rfl⟩ := NamedBar.isBarId_form hbid
  have hgb : X.get (h, b) = some ⟨pcb, .bar 2 cntb mb⟩ := by
    change (X.tr h)[b]? = _
    rw [← hbget, List.getElem?_take, ite_eq_left hbf]
  have hmb := first_bar2_sync hp hX hFw hgb (by omega)
  subst hmb
  -- lane 0 of warp 12 of the CTA
  set z := (h / L.block) * L.block + 12 * 32 with hzdef
  have hcta : z / L.block = h / L.block := by rw [hzdef, hb]; omega
  have hz : z < L.threads := by
    show (h / L.block) * L.block + 12 * 32 < L.grid * L.block
    have hg' : h < L.grid * L.block := hg
    rw [hb] at hg' ⊢
    omega
  have hzw : z % L.block / 32 = 12 := by rw [hzdef, hb]; omega
  have h12z : Prologue.warpIndex L z = 12 := hzw
  have hl0 : laneOf L z = 0 := by simp only [laneOf]; rw [hzdef, hb]; omega
  -- lane 0's barrier-2 arrival of ordinal 0
  obtain ⟨i, pci, mi, hzi, -⟩ := NamedBar.Sources.member_arrival_any hX (srcs2 hp hX hT hF)
    (shape2 hp) (f := (h, b)) hgb (by simp only; omega) hcta
    (by simp only [Finset.mem_range]; omega)
    (fun hex => by
      obtain ⟨jx, pcx, hx⟩ := hex
      have h1 := w12_exit hp hX hFw hx h12z
      obtain ⟨i, ev', hi, hbi, hci⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId 2)
        (show 0 + 1 ≤ (X.tr z).countP (Execution.isBarId 2) by omega)
      obtain ⟨pci, cnti, mi, rfl⟩ := NamedBar.isBarId_form hbi
      have hcnti := (srcs2 hp hX hT hF (z, i) pci cnti ⟨mi, hi⟩ hz).2
      subst hcnti
      exact ⟨i, pci, mi, hi, by simp only; omega⟩)
  obtain ⟨d, n, hσz⟩ := w12_bar2 hp hX hFw hzi h12z
  have hilen : i ≤ (X.tr z).length :=
    (List.getElem?_eq_some_iff.mp (show (X.tr z)[i]? = _ from hzi)).1.le
  obtain ⟨j, -, hall, hlen, hc0⟩ :=
    lane0_alloc hp hX hFw hz h12z hl0 hilen hσz
  -- the hand-off
  have H := Frame.Handoff.of_bar_upTo_ord hX (srcs2 hp hX hT hF) (shape2 hp)
    (syncs := fun _ => True) (prod := fun g => g % L.block / 32 = 12) 1
    (fun h' j' pc' cnt' mode' _ hget hlt => first_bar2_sync hp hX hFw hget hlt)
    (fun g' _ _ h12' hex => by
      obtain ⟨jx, pcx, hx⟩ := hex
      exact w12_exit hp hX hFw hx h12')
  refine ⟨j, _, _, _, _, hall.1, hlen, H z h j f ⟨⟨hz, hg, hcta⟩, ?_, trivial, hzw⟩ hflen ?_⟩
  · simp only [Finset.mem_range]; omega
  · simp only [hc0]; omega

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
