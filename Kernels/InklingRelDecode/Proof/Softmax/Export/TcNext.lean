-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Time
public import Kernels.InklingRelDecode.Proof.Lib.TcVec
public import Kernels.InklingRelDecode.Proof.Lib.BarClock

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

set_option maxRecDepth 100000

private theorem time_loop (s : Site) (i : Nat) (v : Carry) (h1 : s ≠ .setMaxReg) (h2 : s ≠ .bar0)
    (h3 : ∀ j, s ≠ .pre j) (h4 : s ≠ .epilogue) :
    time ⟨s, i, v⟩ = Lib.Slots.softmax i + s.position := by
  unfold time
  split <;> simp_all

private theorem time_pre (j : Fin 64) (i : Nat) (v : Carry) :
    time ⟨.pre j, i, v⟩ = 293 + 4 * j.val := rfl
private theorem time_bar0 (i : Nat) (v : Carry) : time ⟨.bar0, i, v⟩ = Lib.Slots.reuse := rfl
private theorem time_set (i : Nat) (v : Carry) : time ⟨.setMaxReg, i, v⟩ = Lib.Slots.enter := rfl

private theorem loop_ge (e : Entry) (t i : Nat) (v : Carry) (h : i < 2^31) :
    Lib.Slots.softmax i ≤ time ⟨loopSite e t i, i, v⟩ := by
  unfold loopSite
  split_ifs <;> simp only [time, Site.position, Lib.Slots.softmax, Lib.Slots.frame,
    Lib.Slots.stride, Lib.Slots.finish] <;> omega

private theorem round_lt {e t} {d : D} (hi : Inv e t d) (h : d.site ≠ .epilogue)
    (a : d.site ≠ .setMaxReg) (b : d.site ≠ .bar0) (c : ∀ j, d.site ≠ .pre j) : d.i < 2^31 := by
  have := hi.loop h a b c
  have lim := hi.entry.limitEq
  split at lim <;> omega

/-- **A step of the Softmax control never lowers the clock, and raises it at every collective
`tcgen05` site and half-CTA rendezvous.** -/
public theorem time_next {e L g d dn ev} (hi : Inv e (g % L.block) d)
    (h : Control.next e L g d ev = some (some dn)) :
    time d ≤ time dn ∧ (d.site.pc ∈ Lib.loopTcPcs ∨ d.site.pc ∈ Lib.loopBarPcs →
      time d < time dn) := by
  obtain ⟨s, i, v⟩ := d
  have lim := hi.entry.limitEq
  have bnd := hi.bound
  have pre := hi.pre
  have init := hi.init
  have loop := hi.loop
  simp only at lim bnd pre init loop
  have small : e.limit < 2^31 := by split at lim <;> omega
  cases s <;> simp only [Control.next, advance] at h
  all_goals repeat' split at h
  all_goals try contradiction
  all_goals cases h
  all_goals refine ⟨?_, fun hm => ?_⟩
  all_goals try simp (config := {decide := true}) only [
    reduceCtorEq,
    true_implies, ne_eq, not_false_eq_true, implies_true, time_pre, time_bar0, time_set,
    time_loop, Site.pc, Lib.loopTcPcs, Lib.loopBarPcs,
    List.mem_cons, List.not_mem_nil, or_false, Flow.tmemLoad_0, Flow.tmemWait_1,
    Flow.tmemLoad_1, Flow.tmemWait_2, Flow.tmemStore_1, Flow.tmemWait_3, Flow.tmemStore_0,
    Flow.tmemWait_0] at *
  all_goals try simp only [Site.position] at *
  all_goals first
    | omega
    | (refine Nat.le_trans ?_ (loop_ge _ _ _ _ (by omega))
       simp only [Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride]
       omega)
    | (refine Nat.lt_of_lt_of_le ?_ (loop_ge _ _ _ _ (by omega))
       simp only [Lib.Slots.softmax, Lib.Slots.frame, Lib.Slots.stride]
       omega)

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
