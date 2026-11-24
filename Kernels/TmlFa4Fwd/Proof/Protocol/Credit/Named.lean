-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
public import Lemmas.Protocol.NamedBarArrive
import Lemmas.Protocol.PollIndex
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Lemmas.Flow.NthEv
import Lemmas.Protocol.NamedBarMember
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The named barriers of the softmax and correction warps

Named barrier `statId st k` of a CTA has two participant warps (`statPair`): softmax warp
`k + 4 st`, which only arrives, and correction warp `8 + k`, which only waits, each counting 64
(`stat_of_bar`, from the roles' `Export/Count`). A passed wait has every softmax lane's arrival of
its ordinal (`softArrives`): a lane that exited made one more than the tile's rounds (`SoftRounds`,
one more than the correction warps' rescale rounds), and the waits are at most that many. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The number of events of thread `g` on named barrier `id` before its `i`-th event. -/
abbrev barOrd (X : Execution) (g i id : Nat) : Nat :=
  ((X.tr g).take i).countP (Execution.isBarId id)

/-- The named barrier of softmax warp `k + 4 st` with correction warp `8 + k`. -/
def statId (st k : Nat) : Nat := 3 + k + 4 * st

/-- Its two warps. -/
def statPair (st k : Nat) : Finset Nat := {k + 4 * st, 8 + k}

theorem statId_inj {st k st' k' : Nat} (hk : k < 4) (hk' : k' < 4)
    (h : statId st k = statId st' k') : st = st' ∧ k = k' := by
  unfold statId at h
  omega

theorem stat_shape (hp : Pre p L m) {st k : Nat} (hst : st < 2) (hk : k < 4) :
    NamedBar.Shape L (some 64) (statPair st k) (statId st k) where
  pos := by rw [statPair, Finset.card_pair (by omega)]; decide
  target := by
    rw [statPair, Finset.card_pair (by omega)]
    exact NamedBar.target_some_mul (n := 2) (by decide) (by decide)
  bound := by
    intro w hw
    rw [hp.block]
    simp only [statPair, Finset.mem_insert, Finset.mem_singleton] at hw
    omega
  id_lt := by unfold statId; omega

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **Every named-barrier event**: the startup's barrier 0, barrier 2, the softmax warps' stage
barrier (11, 12), or a softmax arrival or correction wait on `statId`. -/
theorem bar_cases {h i pc id : Nat} {cnt : Option Nat} {md : BarMode}
    (he : X.get (h, i) = some ⟨pc, .bar id cnt md⟩) :
    (id = 0 ∧ cnt = none ∧ md = .sync) ∨
      (id = 2 ∧ cnt = some 416 ∧ (md = .arrive → Prologue.warpIndex L h < 12)) ∨
      ((id = 11 ∨ id = 12) ∧ cnt = some 128 ∧ md = .sync) ∨
      ∃ st k, st < 2 ∧ k < 4 ∧ id = statId st k ∧ cnt = some 64 ∧
        ((Prologue.warpIndex L h = k + 4 * st ∧ md = .arrive) ∨
          (Prologue.warpIndex L h = 8 + k ∧ md = .sync)) := by
  have hh := Frame.lt_of_get hX he
  have h16 := Prologue.warpIndex_lt hp h
  rcases show Prologue.warpIndex L h < 8 ∨ (8 ≤ Prologue.warpIndex L h ∧
      Prologue.warpIndex L h ≤ 11) ∨ 12 ≤ Prologue.warpIndex L h by omega with hw | hw | hw
  · rcases soft_bar hp hX hFw hw he with h1 | ⟨h1, h2, -⟩ | h1 | ⟨h1, h2, h3, -⟩
    · exact .inl h1
    · exact .inr (.inl ⟨h1, h2, fun _ => by omega⟩)
    · exact .inr (.inr (.inl h1))
    · refine .inr (.inr (.inr ⟨Prologue.warpIndex L h / 4, Prologue.warpIndex L h % 4, by omega,
        by omega, by unfold statId; omega, h2, .inl ⟨by omega, h3⟩⟩))
  · rcases corr_bar hp hX hFw hw.1 hw.2 he with h1 | ⟨h1, h2, -⟩ | ⟨q, h1, h2, h3, -⟩
    · exact .inl h1
    · exact .inr (.inl ⟨h1, h2, fun _ => by omega⟩)
    · refine .inr (.inr (.inr ⟨q.val, Prologue.warpIndex L h - 8, q.isLt, by omega,
        by unfold statId; omega, h2, .inr ⟨by omega, h3⟩⟩))
  · have hs := bar_sched hp hX hFw hh he
    have h8 : ¬ Prologue.warpIndex L h < 8 := by omega
    have h12 : Prologue.warpIndex L h = 12 ∨ Prologue.warpIndex L h = 13 ∨
        Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15 := by omega
    simp only [schedB, h8, h12, ite_true, ite_false] at hs
    split_ifs at hs
    · simp only [Prod.mk.injEq] at hs
      exact .inl hs
    · simp only [Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      exact .inr (.inl ⟨rfl, rfl, fun h => by cases h⟩)

/-- An event on `statId` is its softmax warp's arrival or its correction warp's wait. -/
theorem stat_of_bar {h i pc st k : Nat} {cnt : Option Nat} {md : BarMode} (hk : k < 4)
    (hst : st < 2) (he : X.get (h, i) = some ⟨pc, .bar (statId st k) cnt md⟩) :
    cnt = some 64 ∧ ((Prologue.warpIndex L h = k + 4 * st ∧ md = .arrive) ∨
      (Prologue.warpIndex L h = 8 + k ∧ md = .sync)) := by
  rcases bar_cases hp hX hFw he with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨st', k', -, hk', hid, hc, hw⟩
  · unfold statId at h0; omega
  · unfold statId at h0; omega
  · unfold statId at h0; omega
  · obtain ⟨rfl, rfl⟩ := statId_inj hk hk' hid
    exact ⟨hc, hw⟩

theorem stat_sources {st k : Nat} (hst : st < 2) (hk : k < 4) :
    NamedBar.Sources L X (some 64) (statPair st k) (statId st k) := by
  intro e pc cnt ⟨md, he⟩ hg
  obtain ⟨hc, hw⟩ := stat_of_bar hp hX hFw hk hst (h := e.1) (i := e.2) he
  refine ⟨?_, hc⟩
  simp only [statPair, Finset.mem_insert, Finset.mem_singleton]
  simp only [Prologue.warpIndex] at hw
  omega

omit hp hX hFw in
/-- The event of a thread with `c` earlier events on barrier `id`, before an event with more. -/
theorem exists_bar {g x c id : Nat} (hc : c + 1 ≤ barOrd X g x id) :
    ∃ y pc cnt md, y < x ∧ X.get (g, y) = some ⟨pc, .bar id cnt md⟩ ∧ barOrd X g y id = c := by
  obtain ⟨y, ⟨pc, kd⟩, hy, hget, hb, hcnt⟩ := exists_nthEv hc
  cases kd <;> simp only [Execution.isBarId, beq_iff_eq,
    Bool.false_eq_true] at hb
  subst hb
  exact ⟨y, pc, _, _, hy, hget, hcnt⟩

/-- A softmax lane that exits with a tile of `R` rescale rounds made `R + 2` arrivals on its barrier
with the correction warps. -/
theorem soft_exit_count {h jx pcx R y : Nat} (hw : Prologue.warpIndex L h < 8)
    (hx : X.get (h, jx) = some ⟨pcx, .exit⟩) (hy : y < L.threads)
    (hc : h / L.block = y / L.block) (hR : CorrRounds p L y R) :
    barOrd X h jx (Prologue.warpIndex L h + 3) = R + 2 := by
  rcases soft_exit hp hX hFw hw hx with hno | ⟨h1, h2⟩
  · exfalso
    obtain ⟨r, bal, hP, -⟩ := hR
    refine hno ⟨r, bal, ?_⟩
    simp only [Epilogue.Picked, hc] at hP ⊢
    exact hP
  · obtain ⟨z, pcz, cntz, mz, hz, hzget, hzo⟩ := exists_bar (X := X) (g := h) (x := jx)
      (c := okPolls (sobj L h 80) ((X.tr h).take jx)) (id := Prologue.warpIndex L h + 3)
      (show _ ≤ barOrd X h jx _ from h1.ge)
    have hm := MbarRing.Poll.okPolls_mono (sobj L h 80) (X.tr h) hz.le
    rcases soft_bar hp hX hFw hw hzget with ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, -, -, -, h4⟩
    · omega
    · omega
    · omega
    · rcases h4 with h4 | ⟨-, hT⟩
      · rw [show ((X.tr h).take z).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) =
          okPolls (sobj L h 80) ((X.tr h).take jx) from hzo] at h4
        omega
      · have hT' := hT.corr hp hy hc hR
        rw [show ((X.tr h).take z).countP (Execution.isBarId (Prologue.warpIndex L h + 3)) =
          okPolls (sobj L h 80) ((X.tr h).take jx) from hzo] at hT'
        show ((X.tr h).take jx).countP _ = _
        omega

/-- **The partner arrivals**: a passed `bar.sync` on `statId st k` has, for every lane of the
softmax warp, its event on the barrier of the same ordinal. -/
theorem softArrives {y j pc st k h : Nat} (hst : st < 2) (hk : k < 4)
    (hb : X.IsBarrier (y, j) (statId st k) (some 64) pc) (hpassed : j + 1 < (X.tr y).length)
    (hcta : h / L.block = y / L.block) (hw : Prologue.warpIndex L h = k + 4 * st) :
    ∃ i pc' cnt md, X.get (h, i) = some ⟨pc', .bar (statId st k) cnt md⟩ ∧
      barOrd X h i (statId st k) = barOrd X y j (statId st k) := by
  have hy : y < L.threads := Frame.lt_of_get hX hb
  have hbg : X.get (y, j) = some ⟨pc, .bar (statId st k) (some 64) .sync⟩ := hb
  obtain ⟨-, hwy⟩ := stat_of_bar hp hX hFw hk hst hbg
  have hwy' : Prologue.warpIndex L y = 8 + k := by
    rcases hwy with ⟨-, h⟩ | ⟨h, -⟩
    · cases h
    · exact h
  obtain ⟨R, hR, hle⟩ : ∃ R, CorrRounds p L y R ∧ barOrd X y j (statId st k) ≤ R + 1 := by
    rcases corr_bar hp hX hFw (by omega) (by omega) hbg with ⟨h0, -⟩ | ⟨h0, -⟩ |
      ⟨q, -, -, -, h1⟩
    · unfold statId at h0; omega
    · unfold statId at h0; omega
    · exact h1
  have hmem : (h % L.block) / 32 ∈ statPair st k := by
    simp only [statPair, Finset.mem_insert, Finset.mem_singleton]
    exact .inl hw
  obtain ⟨i, pc', md, hi, hc⟩ := NamedBar.Sources.member_arrival_any hX
    (stat_sources hp hX hFw hst hk) (stat_shape hp hst hk) hb hpassed hcta hmem
    (fun ⟨jx, pcx, hx⟩ => by
      have hge := soft_exit_count hp hX hFw (by omega) hx hy hcta hR
      rw [show Prologue.warpIndex L h + 3 = statId st k by unfold statId; omega] at hge
      obtain ⟨y', pcy, cnt, my, -, hy', hyo⟩ := exists_bar (X := X) (g := h) (x := jx)
        (c := barOrd X y j (statId st k)) (id := statId st k) (by omega)
      obtain ⟨hcnt, -⟩ := stat_of_bar hp hX hFw hk hst hy'
      rw [hcnt] at hy'
      exact ⟨y', pcy, my, hy', hyo⟩)
  exact ⟨i, pc', some 64, md, hi, hc⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
