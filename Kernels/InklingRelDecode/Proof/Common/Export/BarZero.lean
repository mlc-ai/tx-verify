-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Spec
public import Lemmas.Protocol.NamedBarPhaseKeys
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.Where

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Export
open PTX PTX.Flow PTX.Proof

private theorem halfRange : BarRow.halfZeroSites.all (fun p =>
    (27<p && p<574) || (574<p && p<2331)) = true := by decide

/-- Every counted arrival on barrier zero is from one of the four data warps,
after its two startup rendezvous. Uncounted arrivals can come from all warps. -/
theorem barZeroSources {Q L m X} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    NamedBar.PhSources L X (Finset.range 4) (some 128) 2 0 := by
  rintro ⟨g,k⟩ pc cnt ⟨mode,event⟩ hg
  obtain ⟨_,one|full|half⟩ := Lib.recorded_bar hX hp.block event
  · cases one.1
  · exact .inl full.2.1
  obtain ⟨_,rfl,site⟩ := half
  have halfCnt : BarRow.recCnt L.block 128 = some 128 := by rw [hp.block]; decide
  rw [halfCnt] at event ⊢
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp event).1.le
  have ord : 2 ≤ c0 X g k := by
    by_contra! early
    have clear (f : Fault) : (⟨pc,.bar 0 (some 128) mode⟩ : Event).kind ≠ .ub f := by simp
    obtain ⟨_,_,_,sites,_,shape⟩ := early_at hp hX event clear (by omega)
    obtain ⟨_,eq⟩ := (early_bar sites shape).1 rfl
    cases eq
  obtain ⟨s,hs,_⟩ := Frame.good_stateU (J := fun _ _ => True) (fun g hg => thread_sound hp hg)
    hX event (by simp) ⟨control_tracked hp hX g k hg,fun _ _ => trivial⟩
  have p := Frame.event_pcU (fun g hg => thread_sound hp hg) hX event hs (by simp)
  change pc = _ at p
  have range := List.all_eq_true.mp halfRange pc site
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at range
  have low : g%L.block<128 := by
    rcases range with pro|soft
    · obtain ⟨_,_,_,rfl⟩ := (p ▸ state_role s).prologue pro.1 pro.2
      exact data_warp hp hX hk hs
    · obtain ⟨_,_,_,_,rfl⟩ := (p ▸ state_role s).softmax soft.1 soft.2
      exact data_warp hp hX hk hs
  exact .inr ⟨rfl,Finset.mem_range.mpr (by dsimp; omega),ord⟩

end PTX.Kernels.InklingRelDecode.Proof.Export
