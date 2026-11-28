-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Time

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open Control

def beforeArrival (r : Nat) (d : D) := d.i≤r ∧ d.site≠.epilogue

theorem arrival_clock {r d} (h : beforeArrival r d) : time d≤Lib.Slots.probArrival r ∧
    (time d=Lib.Slots.probArrival r → d.site=.arrive ∧ d.i=r) := by
  obtain ⟨s,i,v⟩ := d
  obtain ⟨le,live⟩ := h
  change i≤r at le
  change s≠.epilogue at live
  have last (s : Site) : s.position=90 → s=.arrive := by
    cases s <;> first | decide | (rename_i j; revert j; decide +kernel)
  have bound := position_bound s
  unfold time Lib.Slots.probArrival
  split
  · simp only [Lib.Slots.enter,Lib.Slots.softmax,Lib.Slots.frame]; omega
  · simp only [Lib.Slots.reuse,Lib.Slots.softmax,Lib.Slots.frame]; omega
  · rename_i j _
    have := j.isLt
    simp only [Lib.Slots.softmax,Lib.Slots.frame]; omega
  · contradiction
  · simp only [Lib.Slots.softmax,Lib.Slots.frame,Lib.Slots.stride]
    exact ⟨by omega,fun eq => ⟨last s (by omega),by omega⟩⟩

set_option maxRecDepth 4096 in
theorem before_arrival_step {r g d ev dn} {ent : Entry} {L : Launch}
    (lane : g%L.block=0) (hi : r<ent.limit)
    (h : beforeArrival r d) (absent : d.site=.arrive → d.i≠r)
    (step : Control.next ent L g d ev=some (some dn)) : beforeArrival r dn := by
  obtain ⟨s,i,v⟩ := d
  obtain ⟨le,live⟩ := h
  change i≤r at le
  change s=.arrive → i≠r at absent
  have loop (j : Nat) (small : j≤r) : loopSite ent 0 j ≠ .epilogue := by
    simp [loopSite,show j≠ent.limit by omega]
    split <;> decide
  cases s <;> simp only [Control.next,lane,Nat.zero_mod,ite_true] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp only [beforeArrival,advance]
  all_goals try solve | constructor <;> first | exact le | (intro eq; cases eq)
  all_goals try exact ⟨le,loop i le⟩
  have lt := absent rfl
  exact ⟨by omega,loop _ (by omega)⟩

end PTX.Kernels.InklingRelDecode.Proof.Softmax
