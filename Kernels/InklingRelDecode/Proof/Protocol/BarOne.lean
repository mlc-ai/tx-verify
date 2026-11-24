-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.BarStatic
public import Kernels.InklingRelDecode.Proof.Protocol.BaseWord
public import Lemmas.Protocol.NamedBarSources
public import Lemmas.Protocol.NamedBarMember

@[expose] public section

/-!
# Named barrier 1: one group in every use

Barrier 1 is `barrier.sync 1` of all 8 warps without a thread count at each of its 16 sites
(`Interface.bar_one_static`), so the library's single-group generation lemmas
(`NamedBar.Sources`, `Shape`) apply to it as they stand:

* `bar1_sources`, `bar1_shape`: the premises;
* `bar1_baseCausality`: two arrivals of one source ordinal in one CTA, one of them passed,
  synchronize (`Sources.same_ordinal_baseCausality`);
* `bar1_member`: every thread of the CTA has the arrival of a passed ordinal, a thread that exits
  from `hexited` (the kernel's statement that an exiting thread has made all the arrivals that
  its CTA's other threads passed).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Every arrival on barrier 1 is a lane of a warp of the CTA passing no count.** -/
theorem bar1_sources (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) :
    NamedBar.Sources L X none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  intro e pc cnt ⟨mode, he⟩ hg
  have hb : L.block = 256 := hpre.block
  refine ⟨?_, (bar_one_static hX (by omega) he).1⟩
  have : e.1 % L.block < 256 := by
    have := Nat.mod_lt e.1 (show L.block > 0 by omega)
    omega
  simp only [Finset.mem_range, CtaBarrier.warps, hb]
  omega

/-- **The group of barrier 1**: 8 warps without a thread count. -/
theorem bar1_shape (hpre : Pre Q L mem0) :
    NamedBar.Shape L none (Finset.range (CtaBarrier.warps L.block)) 1 := by
  obtain ⟨hpos, hcount, hcard, hbound⟩ := bar0_group hpre
  exact ⟨by rw [hcard]; exact hpos, by rw [hcard]; exact hcount, hbound, by decide⟩

/-- **Two threads of one CTA synchronize through barrier-1 arrivals of one source ordinal.** -/
theorem bar1_baseCausality (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    {g h i j before after pc pc' : Nat} (hsame : SameCta L g h)
    (he : X.IsBarrier (g, i) 1 none pc) (hf : X.IsBarrier (h, j) 1 none pc')
    (hpassed : j + 1 < (X.tr h).length)
    (hordinal : ((X.tr g).take i).countP (Execution.isBarId 1) =
      ((X.tr h).take j).countP (Execution.isBarId 1))
    (hbefore : before < i) (hafter : j < after) (hlen : after < (X.tr h).length) :
    baseCausality L X (g, before) (h, after) :=
  (bar1_sources hpre hX).same_ordinal_baseCausality hX (bar1_shape hpre) hsame he hf hpassed
    hordinal hbefore hafter hlen

/-- **Every thread of the CTA has the barrier-1 arrival that a passed thread passed**, an exiting
thread from `hexited`. -/
theorem bar1_member (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    {f : EvId} {pc : Nat} (hf : X.IsBarrier f 1 none pc) (hpassed : f.2 + 1 < (X.tr f.1).length)
    {g : Nat} (hcta : g / L.block = f.1 / L.block)
    (hexited : (∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧ ((X.tr g).take i).countP (Execution.isBarId 1) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId 1)) :
    ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 1) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId 1) := by
  have hb : L.block = 256 := hpre.block
  refine (bar1_sources hpre hX).member_arrival hX (bar1_shape hpre) hf hpassed hcta ?_ hexited
  have := Nat.mod_lt g (show L.block > 0 by omega)
  simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
  omega

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
