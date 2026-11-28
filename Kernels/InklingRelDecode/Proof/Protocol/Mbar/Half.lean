-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
import Kernels.InklingRelDecode.Proof.Common.Export.FinalSync
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Kernel.Safety.HandoffPhased
import Kernels.InklingRelDecode.Proof.Lib.NoBarArrive
import Lemmas.Flow.NthEv

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
open PTX PTX.Frame

private theorem exits {Q L m X g k pc} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (he : X.get (g,k)=some ⟨pc,.exit⟩) :
    3≤((X.tr g).take k).countP (Execution.isBarId 0) := by
  obtain ⟨u,p,uk,get,ord⟩ := Export.exit_final_bar hp hX he
  have mono := Flow.countP_take_mono (Execution.isBarId 0) (X.tr g) uk
  rw [List.take_add_one,show (X.tr g)[u]? = _ from get,List.countP_append] at mono
  change _+1≤_ at mono
  omega

private theorem subgroup {Q L m} (hp : Pre Q L m) :
    Finset.range 4 ⊆ Finset.range (CtaBarrier.warps L.block) := by
  simp [CtaBarrier.warps,hp.block]

theorem half_handoff {Q L m X g h i k} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X)
    (same : SameCta L g h) (present : k<(X.tr h).length) (lg : g%L.block<128) (lh : h%L.block<128)
    (before : ((X.tr g).take (i+1)).countP (Execution.isBarId 0)=2)
    (after : 3≤((X.tr h).take k).countP (Execution.isBarId 0)) : baseCausality L X (g,i) (h,k) := by
  have member (x n : Nat) (low : x%L.block<128) :
      x%L.block/32 ∈ NamedBar.PhGroup L (Finset.range 4) 2 n := by
    unfold NamedBar.PhGroup
    split <;> simp [CtaBarrier.warps,hp.block] at * <;> omega
  apply Handoff.of_barPhased hX (Export.barZeroSources hp hX) (subgroup hp) (Finset.card_range _)
    (by simp [CtaBarrier.warps,hp.block]) (by simp [CtaBarrier.target]) (by simp [hp.block])
    (by decide) (N := 2) (fun _ _ _ _ he => exits hp hX he) same present
    (by omega) before.le (member _ _ lg) (member _ _ lh)

/-- A passed third arrival by a data warp also records the elected initializer's third arrival. -/
theorem half_member {Q L m X g h k pc cnt} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (he : X.get (g,k)=some ⟨pc,.bar 0 cnt .sync⟩)
    (ord : ((X.tr g).take k).countP (Execution.isBarId 0)=2) (pass : k+1<(X.tr g).length)
    (cta : h/L.block=g/L.block) (lg : g%L.block<128) (lh : h%L.block<128) :
    ∃ i p c, X.get (h,i)=some ⟨p,.bar 0 c .sync⟩ ∧
      ((X.tr h).take i).countP (Execution.isBarId 0)=2 := by
  obtain ⟨i,p,c,bar,eq⟩ := NamedBar.D_member_arrival (f := (g,k)) hX (Export.barZeroSources hp hX)
    (subgroup hp) (Finset.card_range _) (by simp [CtaBarrier.warps,hp.block])
    (by simp [CtaBarrier.target]) he pass (Finset.mem_range.mpr (by dsimp; omega)) cta
    (Finset.mem_range.mpr (by omega)) (by
      rintro ⟨j,px,exit⟩
      obtain ⟨i,p,c,mode,_,ev,eq⟩ := nth_bar (q := 2) (exits hp hX exit)
      obtain ⟨rfl,_⟩ := Lib.recorded_bar hX hp.block ev
      exact ⟨i,p,c,ev,eq.trans ord.symm⟩)
  exact ⟨i,p,c,bar,eq.trans ord⟩

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Mbar
