-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Elect.Mma
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Export.PreElect
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Export.Wait
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Export.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Lemmas.Kernel.ElectSource
import Lemmas.Flow.ElectActor

@[expose] public section

/-! # The producer lane of warp 4 and of warp 5

The MMA and TMA channels have one producer lane per CTA, chosen by the election at pc 1853
(warp 4) and 2165 (warp 5). An event of a lane at that pc is the election with the full mask
(`mma_atElect`, `tma_atElect`). From it, per CTA `c`, one lane `y` of the warp
(`mma_producer`, `tma_producer`; the lane's facts `MmaProd`, `TmaProd`):

* every lane of the CTA with an event of the role's code after the election (`MmaOn`, `TmaOn`)
  is `y`, so `y` makes all the role's channel events of the CTA;
* EITHER `y` has no `exit` event and its time is at most `electSlot` (no lane of the warp has
  elected and `y` is the warp's first lane, or `y` is the leader that has not reached its
  election yet: `mma_preElect`, `tma_preElect`; for warp 4 also the winner whose election is its
  last event: `mma_wonOn`), so it is short of every channel event of the lag rows;
* OR `y` has the hypothesis of the role's producer facts: for warp 5 its won election
  (`tma_*Early/Exit`), for warp 4 an event of the MMA code after the election
  (`mma_*Early/Exit`, `mma_qUtEarly`).

Proof: the leader of any election of the warp (`elect_leader`, one mask) is the lane `y`; a lane
with a role event won its election (`tma_won_on`, `mma_won`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An event of warp 5's election pc is the election** with the full mask. -/
theorem tma_atElect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 2165) :
    MbarRow.warp L g = 5 ∧ ∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld := by
  obtain ⟨pc, kd⟩ := e
  simp only at hpc
  subst hpc
  have hub : ∀ f, kd ≠ .ub f := fun f h => hnu ⟨(g, k), 2165, f, by rw [he, h]⟩
  obtain ⟨d, -, -, ⟨h, hk⟩, hl, hw⟩ :=
    tma_at hp hX hFw he hub ⟨show 2162 ≤ 2165 by decide, show 2165 < 2332 by decide⟩
  simp only at h
  have hs : d.site = .elect := by
    cases hs : d.site with
    | elect => rfl
    | leave i => exact absurd hs (hl i)
    | coord0 i | coord1 i | coord2 i | coord3 i | gather i =>
      have := i.isLt
      simp only [hs, Tma.Site.pc, Tma.coordPc] at h
      split_ifs at h <;> omega
    | _ => simp [hs, Tma.Site.pc] at h
  simp only [Tma.EvK, hs] at hk
  rcases hk with hk | ⟨f, hf⟩
  · exact ⟨hw, hk⟩
  · exact absurd hf (hub f)

/-- **An event of warp 4's election pc is the election** with the full mask. -/
theorem mma_atElect (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {g k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 1853) :
    MbarRow.warp L g = 4 ∧ ∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld := by
  obtain ⟨pc, kd⟩ := e
  simp only at hpc
  subst hpc
  have hub : ∀ f, kd ≠ .ub f := fun f h => hnu ⟨(g, k), 1853, f, by rw [he, h]⟩
  obtain ⟨d, -, ⟨h, hk⟩, hl, hw⟩ :=
    mma_at hp hX hFw he hub ⟨show 1850 ≤ 1853 by decide, show 1853 < 2162 by decide⟩
  simp only at h
  have hs : d.site = .elect := by
    cases hs : d.site with
    | elect => rfl
    | leave i => exact absurd hs (hl i)
    | qLoad i =>
      simp only [hs, Mma.Site.pc] at h
      omega
    | qCopy i | qk i | pv i =>
      simp only [hs, Mma.Site.pc] at h
      split_ifs at h <;> omega
    | _ => simp [hs, Mma.Site.pc] at h
  simp only [Mma.EvK, hs] at hk
  rcases hk with hk | ⟨f, hf⟩
  · exact ⟨hw, hk⟩
  · exact absurd hf (hub f)

/-- The leader of warp `w`'s elections at `pe` in CTA `c`: the lane every lane with a role event
(`On`) is, which has no event at `pe` or has its won election there. -/
private theorem leader_core (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    {w pe : Nat} (hw : w < 12) {On : Nat → Nat → Prop}
    (hat : ∀ g k e, X.get (g, k) = some e → e.pc = pe →
      MbarRow.warp L g = w ∧ ∃ inst ld, e.kind = .elect (2 ^ 32 - 1) inst ld)
    (hwon : ∀ g k e, X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) → On g e.pc →
      MbarRow.warp L g = w ∧
        ∃ k0 inst, X.get (g, k0) = some ⟨pe, .elect (2 ^ 32 - 1) inst (PTX.laneOf L g)⟩)
    {c : Nat} (hc : c * L.block < L.threads) :
    ∃ y, y / L.block = c ∧ y < L.threads ∧ MbarRow.warp L y = w ∧
      (∀ g k e, g / L.block = c → X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
        On g e.pc → g = y) ∧
      ((∀ k e, X.get (y, k) = some e → e.pc ≠ pe) ∨
        ∃ k inst, X.get (y, k) = some ⟨pe, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩) := by
  have hb : L.block = 384 := hp.block
  have hcg : c + 1 ≤ L.grid := by
    simp only [Launch.threads] at hc
    exact Nat.lt_of_mul_lt_mul_right hc
  have hT : (c + 1) * L.block ≤ L.threads := Nat.mul_le_mul_right _ hcg
  rw [hb] at hT hc
  have hcb : c * L.block = c * 384 := by rw [hb]
  have hwp : ∀ g, MbarRow.warp L g = g % 384 / 32 := fun g => by
    simp only [MbarRow.warp, tidOf_x_eq hp]
  have sw : ∀ g h, g < L.threads → h < L.threads → g / L.block = c → h / L.block = c →
      MbarRow.warp L g = w → MbarRow.warp L h = w → SameWarp L g h :=
    fun g h hg hh hgc hhc hgw hhw =>
    ⟨⟨hg, hh, hgc.trans hhc.symm⟩, by rw [hwp] at hgw hhw; rw [hb]; omega⟩
  by_cases hE : ∃ g k e, g / L.block = c ∧ X.get (g, k) = some e ∧ e.pc = pe
  · obtain ⟨g0, k0, e0, hg0c, he0, hpc0⟩ := hE
    obtain ⟨hw0, inst0, ld, hk0⟩ := hat g0 k0 e0 he0 hpc0
    have he0' : X.get (g0, k0) = some ⟨pe, .elect (2 ^ 32 - 1) inst0 ld⟩ := by
      rw [he0, ← hpc0, ← hk0]
    have hld : ld < 32 := (hX.elect.1 _ _ _ _ _ he0').2.2.1
    have hg0 := Frame.lt_of_get hX he0
    have hyc : (c * L.block + 32 * w + ld) / L.block = c := by rw [hb]; omega
    have hyt : c * L.block + 32 * w + ld < L.threads := by omega
    have hyw : MbarRow.warp L (c * L.block + 32 * w + ld) = w := by rw [hwp, hb]; omega
    have hyl : PTX.laneOf L (c * L.block + 32 * w + ld) = ld := by
      simp only [PTX.laneOf, hb]
      omega
    refine ⟨_, hyc, hyt, hyw, fun g k e hgc he hub hon => ?_, ?_⟩
    · obtain ⟨hgw, k1, inst1, hk1⟩ := hwon g k e he hub hon
      have hg := Frame.lt_of_get hX he
      have hl : PTX.laneOf L g = ld :=
        elect_leader hX (e := (g, k1)) (f := (g0, k0)) hk1 he0' (sw g g0 hg hg0 hgc hg0c hgw hw0)
      exact sameWarp_eq_of_lane_eq (sw _ _ hg hyt hgc hyc hgw hyw) (hl.trans hyl.symm)
    · by_cases hy : ∃ k e, X.get (c * L.block + 32 * w + ld, k) = some e ∧ e.pc = pe
      · obtain ⟨k, e, he, hpc⟩ := hy
        obtain ⟨-, inst, ld', hk⟩ := hat _ k e he hpc
        have he' : X.get (c * L.block + 32 * w + ld, k) =
            some ⟨pe, .elect (2 ^ 32 - 1) inst ld'⟩ := by
          rw [he, ← hpc, ← hk]
        have hl : ld' = ld := elect_leader hX (e := (_, k)) (f := (g0, k0)) he' he0'
          (sw _ g0 hyt hg0 hyc hg0c hyw hw0)
        exact .inr ⟨k, inst, by rw [he', hl, hyl]⟩
      · exact .inl fun k e he hpc => hy ⟨k, e, he, hpc⟩
  · have hyc : (c * L.block + 32 * w) / L.block = c := by rw [hb]; omega
    refine ⟨c * L.block + 32 * w, hyc, by omega, by rw [hwp, hb]; omega,
      fun g k e hgc he hub hon => ?_, .inl fun k e he hpc => hE ⟨_, k, e, hyc, he, hpc⟩⟩
    obtain ⟨-, k0, inst, hk0⟩ := hwon g k e he hub hon
    exact (hE ⟨g, k0, _, hgc, hk0, rfl⟩).elim

/-- A producer lane short of every channel event: no `exit` event, time at most `electSlot`. -/
def PreProd (P : Params) (L : Launch) (X : Execution) (y : Nat) : Prop :=
  (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧ Sched.threadTime (timed P L) X y ≤ electSlot

/-- **The TMA producer of CTA `c`**: a lane of warp 5 of the CTA, short of every channel event
(`PreProd`) or with its won election at pc 2165 (the hypothesis of `tma_*Early`, `tma_*Exit`). -/
def TmaProd (P : Params) (L : Launch) (X : Execution) (c y : Nat) : Prop :=
  y / L.block = c ∧ MbarRow.warp L y = 5 ∧ (PreProd P L X y ∨
    ∃ k inst, X.get (y, k) = some ⟨2165, .elect (2 ^ 32 - 1) inst (PTX.laneOf L y)⟩)

/-- **The MMA producer of CTA `c`**: a lane of warp 4 of the CTA, short of every channel event
(`PreProd`) or with an event of the MMA code after the election (the hypothesis of
`mma_*Early`, `mma_*Exit`). -/
def MmaProd (P : Params) (L : Launch) (X : Execution) (c y : Nat) : Prop :=
  y / L.block = c ∧ MbarRow.warp L y = 4 ∧ (PreProd P L X y ∨
    ∃ k e, X.get (y, k) = some e ∧ (∀ f, e.kind ≠ .ub f) ∧ MmaOn L y e.pc)

/-- **The TMA producer of CTA `c`**: a lane `y` with `TmaProd` that every lane of the CTA with a
`TmaOn` event is. -/
theorem tma_producer (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {c : Nat} (hc : c * L.block < L.threads) :
    ∃ y, y < L.threads ∧ TmaProd P L X c y ∧
      ∀ g k e, g / L.block = c → X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
        TmaOn L g e.pc → g = y := by
  obtain ⟨y, hyc, hyt, hyw, hone, hst⟩ := leader_core hp hX (w := 5) (pe := 2165) (On := TmaOn L)
    (by decide) (fun g k e he hpc => tma_atElect hp hX hFw hnu he hpc)
    (fun g k e he hub hon =>
      let ⟨k0, _, inst, h⟩ := tma_won_on hp hX hFw he hub hon
      ⟨hon.1.1, k0, inst, h⟩) hc
  refine ⟨y, hyt, ⟨hyc, hyw, ?_⟩, hone⟩
  rcases hst with hno | hwin
  · exact .inl (tma_preElect hp hX hFw hnu hyt hyw hno)
  · exact .inr hwin

/-- **The MMA producer of CTA `c`**: a lane `y` with `MmaProd` that every lane of the CTA with an
`MmaOn` event is. -/
theorem mma_producer (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hnu : ¬ HasUb X) {c : Nat} (hc : c * L.block < L.threads) :
    ∃ y, y < L.threads ∧ MmaProd P L X c y ∧
      ∀ g k e, g / L.block = c → X.get (g, k) = some e → (∀ f, e.kind ≠ .ub f) →
        MmaOn L g e.pc → g = y := by
  obtain ⟨y, hyc, hyt, hyw, hone, hst⟩ := leader_core hp hX (w := 4) (pe := 1853) (On := MmaOn L)
    (by decide) (fun g k e he hpc => mma_atElect hp hX hFw hnu he hpc)
    (fun g k e he hub hon =>
      let ⟨k0, _, inst, h⟩ := mma_won hp hX hFw he hub ⟨hon.2, hon.1.2.2⟩
      ⟨hon.1.1, k0, inst, h⟩) hc
  refine ⟨y, hyt, ⟨hyc, hyw, ?_⟩, hone⟩
  rcases hst with hno | ⟨k, inst, hk⟩
  · exact .inl (mma_preElect hp hX hFw hnu hyt hyw hno)
  · rcases mma_wonOn hp hX hFw hnu hk with hon | hpre
    · exact .inr hon
    · exact .inl hpre

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
