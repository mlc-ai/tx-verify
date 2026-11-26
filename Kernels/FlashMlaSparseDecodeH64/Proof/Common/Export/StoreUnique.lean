-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Origin
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.TensorOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Out

@[expose] public section

/-! # An output tensor store is issued once per CTA, warp and chunk

Two tensor stores of one CTA, of one warp and of one chunk (the same first box column) are one
event: each follows its lane's election, which names the lane itself (`wg0_outKey`), so the
elected lanes of the warp are one (`ElectOk`); and the store is the second event after its
barrier-9 event of a fixed ordinal, which a lane has once. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The first box column `128 w + col` determines the chunk of the warp. -/
private theorem chunk_eq {w c c' : Nat} (hc : c < 4) (hc' : c' < 4)
    (h : 128 * w + [0, 64, 256, 320].getD c 0 = 128 * w + [0, 64, 256, 320].getD c' 0) :
    c = c' := by
  interval_cases c <;> interval_cases c' <;> simp_all

private theorem pc_inj {c c' : Nat} (hc : c < 4) (hc' : c' < 4)
    (h : [1358, 1516, 1673, 1831].getD c 0 = [1358, 1516, 1673, 1831].getD c' 0) : c = c' := by
  interval_cases c <;> interval_cases c' <;> simp_all

/-- A barrier-9 event of a lane counts once more than the events before it. -/
private theorem count_bar {g j j' pc : Nat} (hj : X.get (g, j) = some ⟨pc, .bar 9 (some 128) .sync⟩)
    (hlt : j < j') :
    ((X.tr g).take j).countP (Execution.isBarId 9) <
      ((X.tr g).take j').countP (Execution.isBarId 9) := by
  have hl : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hj).1
  have hg : (X.tr g)[j] = ⟨pc, .bar 9 (some 128) .sync⟩ := by
    have := hj
    simp only [Execution.get] at this
    exact Option.some.inj (by rw [← this]; exact (List.getElem?_eq_getElem hl).symm)
  have h1 : ((X.tr g).take (j + 1)).countP (Execution.isBarId 9) =
      ((X.tr g).take j).countP (Execution.isBarId 9) + 1 := by
    rw [List.take_add_one, List.getElem?_eq_getElem hl, List.countP_append]
    simp [hg, Execution.isBarId]
  have h2 : ((X.tr g).take (j + 1)).countP (Execution.isBarId 9) ≤
      ((X.tr g).take j').countP (Execution.isBarId 9) :=
    (List.take_sublist_take_left (by omega)).countP_le
  omega

/-- **An output tensor store is one event per CTA, warp and chunk**: two tensor stores of lanes of
one CTA and warp with the same first box column are the same event. -/
theorem store_unique (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k g' k' a a' : Nat} {s s' : TensorStore.Spec}
    (hi : X.TensorStoreIssue (g, k) a s) (hi' : X.TensorStoreIssue (g', k') a' s')
    (hc : g / L.block = g' / L.block) (hw : MbarRow.warp L g = MbarRow.warp L g')
    (hx : s.origin 0 = s'.origin 0) : g = g' ∧ k = k' := by
  obtain ⟨-, -, c, hc4, hg0, ho⟩ := tensor_store_origin hp hX hFw hnu hi
  obtain ⟨-, -, c', hc4', hg0', ho'⟩ := tensor_store_origin hp hX hFw hnu hi'
  have h0 := (boxOrigin_zero ho).symm.trans (hx.trans (boxOrigin_zero ho'))
  have hcc : c = c' := by
    rw [hw] at h0
    exact chunk_eq hc4 hc4' (by exact_mod_cast h0)
  subst hcc
  obtain ⟨-, c1, hc1, -, j, pc, hk, hj, hcnt, hget, pce, inst, hel⟩ :=
    wg0_outKey hp hX hFw hnu hi
  obtain ⟨-, c1', hc1', -, j', pc', hk', hj', hcnt', hget', pce', inst', hel'⟩ :=
    wg0_outKey hp hX hFw hnu hi'
  have e1 : c1 = c := by
    have := (hg0.symm.trans hget)
    simp only [Option.some.injEq, Event.mk.injEq] at this
    exact (pc_inj hc1 hc4 this.1.symm)
  have e1' : c1' = c := by
    have := (hg0'.symm.trans hget')
    simp only [Option.some.injEq, Event.mk.injEq] at this
    exact (pc_inj hc1' hc4 this.1.symm)
  rw [e1] at hcnt
  rw [e1'] at hcnt'
  obtain ⟨_, hge⟩ := hi
  obtain ⟨_, hge'⟩ := hi'
  have hwarp : SameWarp L g g' := by
    refine ⟨⟨Frame.lt_of_get hX hge, Frame.lt_of_get hX hge', hc⟩, ?_⟩
    simp only [MbarRow.warp, tidOf_x_eq hp] at hw
    simpa only [hp.block] using hw
  have hlead := hX.elect.2.2 (g, j + 1) (g', j' + 1) pce pce' (2 ^ 32 - 1) inst inst'
    (PTX.laneOf L g) (PTX.laneOf L g') hel hel' hwarp
  have hgg : g = g' := by
    simp only [PTX.laneOf, hp.block] at hlead hwarp hc
    obtain ⟨-, hw'⟩ := hwarp
    simp only [hp.block] at hw'
    omega
  subst hgg
  refine ⟨rfl, ?_⟩
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact absurd hcnt' (by have := count_bar hj h; omega)
  · omega
  · exact absurd hcnt (by have := count_bar hj' h; omega)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
