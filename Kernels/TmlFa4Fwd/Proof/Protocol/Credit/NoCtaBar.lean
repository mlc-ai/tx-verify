-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Std.Tactic.BVDecide.Normalize.Prop

public section

/-! # ERR-CTA-BARRIER: no named barrier is arrived on twice in one generation

The counts of the arrivals on one barrier agree (`bar_cases`), and the generation of every
`bar.arrive` is done before its thread arrives on that barrier again
(`NamedBar.no_duplicate_arrival`): an arrival on barrier 2 is its thread's last event on it, and
before its next arrival on `statId` a softmax lane polls the credit barrier once more, which
observes its partner's credit arrival, after the partner's passed `bar.sync` of the same ordinal
(`stat_done`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem isBarId_form {id : Nat} {ev : Event} (h : Execution.isBarId id ev = true) :
    ∃ pc cnt md, ev = ⟨pc, .bar id cnt md⟩ := by
  obtain ⟨pc, kd⟩ := ev
  cases kd <;> simp only [Execution.isBarId, beq_iff_eq, Bool.false_eq_true] at h
  subst h
  exact ⟨pc, _, _, rfl⟩

private theorem barOrd_lt {g i j pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (g, i) = some ⟨pc, .bar id cnt md⟩) (hij : i < j) :
    barOrd X g i id + 1 ≤ barOrd X g j id := by
  have hg : (X.tr g)[i]? = some ⟨pc, .bar id cnt md⟩ := he
  have h2 := (List.take_sublist_take_left (l := X.tr g) (by omega : i + 1 ≤ j)).countP_le
    (p := Execution.isBarId id)
  have h1 : ((X.tr g).take (i + 1)).countP (Execution.isBarId id) = barOrd X g i id + 1 := by
    rw [List.take_add_one, hg, Option.toList_some, List.countP_append, List.countP_singleton]
    simp [Execution.isBarId]
  unfold barOrd at *
  omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The generation of a softmax arrival is done before the lane arrives again.** -/
private theorem stat_done {e : EvId} {key pc j st k : Nat} {cnt : Option Nat} {ev : Event}
    (hst : st < 2) (hk4 : k < 4) (hk : CtaBarArrivalK L X e key)
    (he : X.get e = some ⟨pc, .bar (statId st k) cnt .arrive⟩) (hij : e.2 < j)
    (hj : X.get (e.1, j) = some ev) (hjb : Execution.isBarId (statId st k) ev = true) :
    CtaBarDone L X (e.1 / L.block) key := by
  obtain ⟨g, i⟩ := e
  simp only at hij hj ⊢
  have hg := Frame.lt_of_get hX he
  obtain ⟨rfl, hw⟩ := stat_of_bar hp hX hFw hk4 hst he
  have hwg : Prologue.warpIndex L g = k + 4 * st := by
    rcases hw with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · cases h
  obtain ⟨pcj, cntj, mj, rfl⟩ := isBarId_form hjb
  have hlt := barOrd_lt he hij
  -- the lane's credit poll with `ordinal + 1` earlier ones
  have hcr : okPolls (sobj L g 192) ((X.tr g).take j) = barOrd X g j (statId st k) + 1 := by
    rcases soft_bar hp hX hFw (by omega) hj with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, -, h1, -⟩
    · unfold statId at h0; omega
    · unfold statId at h0; omega
    · unfold statId at h0; omega
    · exact h1
  have hob : sobj L g 192 = obj L g (192 + 8 * st) := by
    rw [sobj]; congr 1; rw [hwg]; omega
  rw [hob] at hcr
  obtain ⟨q, pcq, par, acq, sc, -, hpoll, hq⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (m := obj L g (192 + 8 * st)) (h := g) (f := j)
      (c := barOrd X g i (statId st k) + 1) (by omega)
  obtain ⟨y, hy, hcy, hwy⟩ : ∃ y, (∃ a, y = corrLane L (g / L.block) a) ∧
      y / L.block = g / L.block ∧ Prologue.warpIndex L y = 8 + k := by
    obtain ⟨h1, h2⟩ := corrLane_facts (L := L) hp (g / L.block) ⟨32 * k, by omega⟩
    simp only [Nat.mul_div_cancel_left k (by decide : 0 < 32)] at h2
    exact ⟨_, ⟨_, rfl⟩, h1, h2⟩
  obtain ⟨x, hx, rs, ⟨tx, cntx, pcx, hxget⟩, -⟩ := creditHandoff hp hX hFw g ⟨st, hst⟩ g q pcq par
    acq sc _ ⟨hg, rfl, by omega, by simp only; omega⟩ hpoll hq y hy
  simp only at hx hxget
  have hob' : obj L g (192 + 8 * st) = obj L y (192 + 8 * st) := (obj_cta hcy _).symm
  rw [hob'] at hx hxget
  have hcc := corr_credit_arr hp hX hFw (by omega) (by omega) ⟨st, hst⟩ hxget
  simp only at hcc
  rw [hwy, show 8 + k - 5 + 4 * st = statId st k by unfold statId; omega, hx] at hcc
  obtain ⟨z, pcz, cntz, mz, hzx, hzget, hzo⟩ := exists_bar (X := X) (g := y) (x := x)
    (id := statId st k) (c := barOrd X g i (statId st k)) hcc.ge
  obtain ⟨rfl, hmz⟩ := stat_of_bar hp hX hFw hk4 hst hzget
  have hmz' : mz = .sync := by
    rcases hmz with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  subst hmz'
  have hpass : z + 1 < (X.tr y).length := by
    have := len_of_get hxget; simp only at this; omega
  exact (stat_sources hp hX hFw hst hk4).arrive_done_of_partner hX (stat_shape hp hst hk4) hk he
    (f := (y, z)) hcy hzget hpass hzo

/-- **An arrival on barrier 2 is its thread's last event on it.** -/
private theorem bar2_last {h i j pc : Nat} {cnt : Option Nat} {ev : Event}
    (he : X.get (h, i) = some ⟨pc, .bar 2 cnt .arrive⟩) (hij : i < j)
    (hj : X.get (h, j) = some ev) : Execution.isBarId 2 ev = false := by
  rw [Bool.eq_false_iff]
  intro hb
  obtain ⟨pcj, cntj, mj, rfl⟩ := isBarId_form hb
  have hlt := barOrd_lt he hij
  have hw : Prologue.warpIndex L h < 12 := by
    rcases bar_cases hp hX hFw he with ⟨h0, -⟩ | ⟨-, -, h1⟩ | ⟨h0, -⟩ | ⟨st, k, -, -, h0, -⟩
    · omega
    · exact h1 rfl
    · omega
    · unfold statId at h0; omega
  have key : ∀ {i pc : Nat} {cnt : Option Nat} {md : BarMode},
      X.get (h, i) = some ⟨pc, .bar 2 cnt md⟩ →
        md = .sync ∧ barOrd X h i 2 = 0 ∨ md = .arrive ∧ barOrd X h i 2 = 1 := by
    intro i pc cnt md hget
    rcases Nat.lt_or_ge (Prologue.warpIndex L h) 8 with hw8 | hw8
    · rcases soft_bar hp hX hFw hw8 hget with ⟨h0, -⟩ | ⟨-, -, h1⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · omega
      · exact h1
      · omega
      · omega
    · rcases corr_bar hp hX hFw hw8 (by omega) hget with ⟨h0, -⟩ | ⟨-, -, h1⟩ | ⟨q, h0, -⟩
      · omega
      · exact h1
      · omega
  rcases key he with ⟨h1, -⟩ | ⟨-, h1⟩
  · cases h1
  · rcases key hj with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega

/-- **No CTA barrier arrival faults** (ERR-CTA-BARRIER). -/
theorem noCtaBar : ¬ CtaBarFault L X := by
  refine NamedBar.no_duplicate_arrival hX ?_ ?_
  · intro e f id cnt cnt' pc pc' md md' _ he hf
    have h1 := bar_cases hp hX hFw (h := e.1) (i := e.2) he
    have h2 := bar_cases hp hX hFw (h := f.1) (i := f.2) hf
    unfold statId at h1 h2
    rcases h1 with ⟨a, rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨st, k, _, _, a, rfl, -⟩ <;>
      rcases h2 with ⟨b, rfl, -⟩ | ⟨b, rfl, -⟩ | ⟨b, rfl, -⟩ | ⟨st', k', _, _, b, rfl, -⟩ <;>
      first | rfl | omega
  · intro e key pc cnt j ev hk he hij hj hjb
    rcases bar_cases hp hX hFw (h := e.1) (i := e.2) he with ⟨-, -, h0⟩ | ⟨h0, -⟩ | ⟨-, -, h0⟩ |
      ⟨st, k, hst, hk4, h0, -⟩
    · cases h0
    · rw [h0] at he hjb
      rw [bar2_last hp hX hFw (h := e.1) (i := e.2) he hij hj] at hjb
      cases hjb
    · cases h0
    · rw [h0] at he hjb
      exact stat_done hp hX hFw hst hk4 hk he hij hj hjb

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
