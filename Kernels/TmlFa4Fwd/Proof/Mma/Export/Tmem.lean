-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.TmemSite
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Mma.Export.DescOf
import Kernels.TmlFa4Fwd.Proof.Mma.Export.Win
import Std.Tactic.BVDecide.Normalize.Prop

import Kernels.TmlFa4Fwd.Proof.Common.DataSound
import Kernels.TmlFa4Fwd.Proof.Common.SharedSites

@[expose] public section

/-! # The MMA warp's Tensor Memory operations, on its trace

`mma_at`: every MMA of a lane of warp 12 is a QK MMA (`Tm.Qk`) or a PV MMA (`Tm.Pv`) of a stage and
a tile, with the counts of its place. `mma_lane`: one lane of a CTA issues its MMAs. `pv_qk`,
`qk_pv`, `qk_lt`, `pv_lt`: the order of a lane's MMAs by their tiles. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The MMA of a site**, at its state. -/
theorem mma_at_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {k : Nat} {e : Event} {dd : D} {n : Cls → Nat}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (minj p L g dd n)))
    (hJ : RefCounts p L g (dd, rc n)) :
    (∀ b j, dd.site = .qk b j → ∃ u, Tm.Qk L X g k (b.val % 2) u j) ∧
      ∀ b j, dd.site = .pv b j → ∃ u, Tm.Pv L X g k (b.val % 2) u j := by
  have hg := Frame.lt_of_get hX he
  have hD : DOk L dd := mma_desc hp hX hg hw k
    (List.getElem?_eq_some_iff.mp (show (X.tr g)[k]? = _ from he)).1.le _ hσ
  have hW := words hp hX hg hw hσ
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
    strict_fired_site hp hX he hσ rfl
  have hI := issue_at hp hg (d := dd) hat hc hf hD
  exact ⟨fun b j h => qk_site hp hX he hσ h hJ (win_states hX k dd n hσ (by rw [h]; rfl))
      (hI.1 b j h) hW,
    fun b j h => pv_site hp hX he hσ h hJ (win_states hX k dd n hσ (by rw [h]; rfl))
      (hI.2 b j h) hW⟩

/-- **Every MMA of warp 12 is a QK or a PV MMA** of a stage and a tile. -/
theorem mma_at (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hw : Prologue.warpIndex L g = 12) {k d : Nat} {sp : TcMma.OperandSpec}
    {acc : Bool} {mask : List Nat} (hi : X.MmaIssue (g, k) d sp acc mask) :
    ∃ st u j, st < 2 ∧ (Tm.Qk L X g k st u j ∨ Tm.Pv L X g k st u j) := by
  obtain ⟨e, dd, n, he, hσ, hJ, -, hs⟩ := mma_state hp hX hw hi
  obtain ⟨h1, h2⟩ := mma_at_site hp hX hw he hσ hJ
  rcases hs with ⟨b, j, h⟩ | ⟨b, j, h⟩
  · obtain ⟨u, hq⟩ := h1 b j h
    exact ⟨_, u, j, Nat.mod_lt _ (by decide), .inl hq⟩
  · obtain ⟨u, hq⟩ := h2 b j h
    exact ⟨_, u, j, Nat.mod_lt _ (by decide), .inr hq⟩

/-- **One lane of a CTA issues its MMAs.** -/
theorem mma_lane (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {h : Nat} (hwg : Prologue.warpIndex L g = 12)
    (hwh : Prologue.warpIndex L h = 12) (hc : g / L.block = h / L.block) {k k' d d' : Nat}
    {sp sp' : TcMma.OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hi : X.MmaIssue (g, k) d sp acc mask) (hi' : X.MmaIssue (h, k') d' sp' acc' mask') :
    g = h := by
  obtain ⟨e, dd, n, he, hσ, -, -, hs⟩ := mma_state hp hX hwg hi
  obtain ⟨e', dd', n', he', hσ', -, -, hs'⟩ := mma_state hp hX hwh hi'
  refine win_lane hX ⟨⟨Frame.lt_of_get hX he, Frame.lt_of_get hX he', hc⟩, hwg.trans hwh.symm⟩
    hσ hσ' ?_ ?_
  · rcases hs with ⟨b, j, h⟩ | ⟨b, j, h⟩ <;> rw [h] <;> rfl
  · rcases hs' with ⟨b, j, h⟩ | ⟨b, j, h⟩ <;> rw [h] <;> rfl

/-- **The lane that issues a CTA's MMAs makes its commits.** -/
theorem mma_commit_lane (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {h : Nat} (hwg : Prologue.warpIndex L g = 12) (hwh : Prologue.warpIndex L h = 12)
    (hc : g / L.block = h / L.block) {k k' d : Nat} {sp : TcMma.OperandSpec} {acc : Bool}
    {mask : List Nat} {s : TcCommit.Spec} (hi : X.MmaIssue (g, k) d sp acc mask)
    (hi' : X.Commit (h, k') s) : g = h := by
  obtain ⟨e, dd, n, he, hσ, -, -, hs⟩ := mma_state hp hX hwg hi
  obtain ⟨dd', n', he', hσ', hs'⟩ := commit_state hp hX hwh hi'
  refine win_lane hX ⟨⟨Frame.lt_of_get hX he, he', hc⟩, hwg.trans hwh.symm⟩ hσ hσ' ?_ hs'
  rcases hs with ⟨b, j, h⟩ | ⟨b, j, h⟩ <;> rw [h] <;> rfl

/-! ### The order of a lane's MMAs -/

theorem countP_mono {f : Event → Bool} {es : List Event} {i j : Nat} (h : i ≤ j) :
    (es.take i).countP f ≤ (es.take j).countP f :=
  (List.take_prefix_take_left (l := es) h).sublist.countP_le

/-- A QK MMA of an earlier tile is before one of a later tile. -/
theorem qk_lt {k k' st u u' : Nat} {j j' : Fin 8} (h : Tm.Qk L X g k st u j)
    (h' : Tm.Qk L X g k' st u' j') (hu : u < u') : k < k' := by
  by_contra hle
  have := countP_mono (f := commitsTo (Tm.sFull L (g / L.block) st)) (es := X.tr g)
    (Nat.le_of_not_lt hle)
  have h1 := h.com
  have h2 := h'.com
  unfold Tm.sCommits at h1 h2
  omega

/-- A PV MMA of an earlier tile is before one of a later tile. -/
theorem pv_lt {k k' st u u' : Nat} {j j' : Fin 8} (h : Tm.Pv L X g k st u j)
    (h' : Tm.Pv L X g k' st u' j') (hu : u < u') : k < k' := by
  by_contra hle
  have := countP_mono (f := commitsTo (Tm.sFull L (g / L.block) st)) (es := X.tr g)
    (Nat.le_of_not_lt hle)
  have h1 := h.com
  have h2 := h'.com
  unfold Tm.sCommits at h1 h2
  omega

/-- The QK MMAs of a tile are before its PV MMAs and those of later tiles. -/
theorem qk_pv {k k' st u u' : Nat} {j j' : Fin 8} (h : Tm.Qk L X g k st u j)
    (h' : Tm.Pv L X g k' st u' j') (hu : u ≤ u') : k < k' := by
  by_contra hle
  have := countP_mono (f := commitsTo (Tm.sFull L (g / L.block) st)) (es := X.tr g)
    (Nat.le_of_not_lt hle)
  have h1 := h.com
  have h2 := h'.com
  unfold Tm.sCommits at h1 h2
  omega

/-- The PV MMAs of a tile are before the QK MMAs of later tiles. -/
theorem pv_qk {k k' st u u' : Nat} {j j' : Fin 8} (hst : st < 2) (h : Tm.Pv L X g k st u j)
    (h' : Tm.Qk L X g k' st u' j') (hu : u < u') : k < k' := by
  by_contra hle
  have hle := Nat.le_of_not_lt hle
  have hne : k' ≠ k := by
    rintro rfl
    obtain ⟨_, _, e1⟩ := h.issue
    obtain ⟨_, _, _, e2⟩ := h'.issue
    rw [e1] at e2
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.mma.injEq] at e2
    omega
  by_cases h1 : st = 1
  · have := countP_mono (f := isElectEv) (es := X.tr g) hle
    have e1 := h.el h1
    have e2 := h'.el
    unfold elections at e1 e2
    rw [h1, ite_eq_right (by decide)] at e2
    omega
  · have hs0 : st = 0 := by omega
    have k1 := h.kv
    have k2 := h'.kv
    unfold Tm.kvPolls okPolls at k1 k2
    have a1 := countP_mono (f := okPoll (Tm.bar L (g / L.block) 32)) (es := X.tr g) hle
    have a2 := countP_mono (f := okPoll (Tm.bar L (g / L.block) 40)) (es := X.tr g) hle
    have a3 := countP_mono (f := okPoll (Tm.bar L (g / L.block) 48)) (es := X.tr g) hle
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Mma
