-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.BarOne
public import Kernels.InklingRelDecode.Proof.Safety.Registers

@[expose] public section

/-!
# `regAgree` and `regSync` from the register-request ledger

`SetMaxNReg.UnsafeAt` asks, of the four warps of a warpgroup, that the request of each ordinal is
the same (direction and count: `RegAgree`) and that every request but the exempt loop-head one
follows the previous requests of the whole warpgroup in base causality (`RegSync`). In the kernel
the previous requests are separated from the next by `barrier.sync 1`, and barrier 1 has one group
(`BarOne.lean`), so two arrivals of one source ordinal synchronize.

What the thread layer has to say is the ledger `RegLedger`, a statement of two kinds of event in
one thread, the register requests and the barrier-1 arrivals, by their counts before:

* `shape`: the request of ordinal `r` in warpgroup `w` is `inc 256`, except in the workers'
  warpgroup (1) at ordinals `r % 3 = 1` (the role's `dec 24`): the workers' loop iteration is
  `inc` (the loop head), `dec`, `inc` (the role's end), and the default partition's three
  requests are `inc`;
* `b1`: a request that is no loop head and has a predecessor (ordinal `r > 0`) has `n` barrier-1
  arrivals before it, `0 < n ≤ 3`, and in every thread of its warpgroup the arrival of ordinal
  `n - 1` has at least `r` requests before it (the dispatch loop's iteration: head `inc`, barrier,
  `dec`, barrier, barrier, `inc`: ordinals 0, 1, 2 and 3 of the requests of a thread meet the
  barrier ordinals 0, 1, 2 so that request `r` has `r` requests before barrier arrival `n - 1`);
* `exit`: an exiting thread has made at least 3 barrier-1 arrivals (the dispatch bound: the role
  table is read twice, so a worker exits after the head barrier of its second iteration, and the
  default partition after the epilogue's two barriers).

`regAgree_of_ledger` and `regSync_of_ledger` are the two fields. The ledger is a thread-layer
statement over the abstract states (the development notes, "thread-layer gaps").
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Bar
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Safety

noncomputable section

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number of register requests of thread `g` before its event `k`. -/
def rqBefore (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP SetMaxNReg.isRequest

/-- The number of barrier-1 events of thread `g` before its event `k`. -/
def b1Before (X : Execution) (g k : Nat) : Nat :=
  ((X.tr g).take k).countP (Execution.isBarId 1)

/-- The request of ordinal `r` in warpgroup `w`: `inc 256`, except the workers' `dec 24` at
ordinals `r % 3 = 1`. -/
def regSched (w r : Nat) : Bool × Nat :=
  if w = 1 ∧ r % 3 = 1 then (false, 24) else (true, 256)

/-- **The register-request ledger** (see the module comment). -/
structure RegLedger (L : Launch) (X : Execution) : Prop where
  shape : ∀ {g k pc : Nat} {inc : Bool} {n inst : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
    (inc, n) = regSched ((g % L.block) / 128) (rqBefore X g k)
  b1 : ∀ {g k pc : Nat} {inc : Bool} {n inst : Nat}, g < L.threads →
    X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
    asms.all (fun a => !a.regSyncExempt pc) = true → 0 < rqBefore X g k →
    0 < b1Before X g k ∧ b1Before X g k ≤ 3 ∧
      ∀ h i pc' cnt m, SetMaxNReg.SameGroup L g h → X.get (h, i) = some ⟨pc', .bar 1 cnt m⟩ →
        b1Before X h i + 1 = b1Before X g k → rqBefore X g k ≤ rqBefore X h i
  exit : ∀ {h j pc : Nat}, h < L.threads → X.get (h, j) = some ⟨pc, .exit⟩ →
    3 ≤ b1Before X h j

/-- **A thread with more than `r` barrier-1 events before its event `k` has its arrival of
ordinal `r` before it.** -/
theorem arrival1_before (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    {h k r : Nat} (hr : r < ((X.tr h).take k).countP (Execution.isBarId 1)) :
    ∃ j pc, j < k ∧ X.IsBarrier (h, j) 1 none pc ∧
      ((X.tr h).take j).countP (Execution.isBarId 1) = r := by
  obtain ⟨j, e, hj, hq, hcnt⟩ := NamedBar.exists_ordinal (Execution.isBarId 1) _ hr
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjk
    obtain ⟨pc, cnt, m, rfl⟩ := NamedBar.isBarId_form hq
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
    have hget : X.get (h, j) = some ⟨pc, .bar 1 cnt m⟩ := hj
    obtain ⟨hn, hm⟩ := bar_one_static hX (by have := hpre.block; omega) hget
    subst hn hm
    exact ⟨j, pc, hjk, hget, hcnt⟩
  · cases hj

/-- **`regAgree`**: the four warps of a warpgroup request the same direction and count at each
ordinal. -/
theorem regAgree_of_ledger (hX : Consistent L kernel asms mem0 X) (hl : RegLedger L X) :
    RegAgree L X := by
  intro e f pc pc' n n' inst inst' inc inc' hsg he hf hord
  have h1 := hl.shape (Frame.lt_of_get hX he) he
  have h2 := hl.shape (Frame.lt_of_get hX hf) hf
  have hg : (e.1 % L.block) / 128 = (f.1 % L.block) / 128 := hsg.2
  have hr : rqBefore X e.1 e.2 = rqBefore X f.1 f.2 := hord
  rw [hg, hr] at h1
  have h3 := h1.trans h2.symm
  simp only [Prod.mk.injEq] at h3
  exact h3

/-- **`regSync`**: a later request follows the previous requests of the whole warpgroup in base
causality. -/
theorem regSync_of_ledger (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hl : RegLedger L X) : RegSync L X := by
  intro e pc n inst inc hreq hna hpos h hh hgrp
  obtain ⟨g, k⟩ := e
  have hgt : g < L.threads := Frame.lt_of_get hX hreq
  have hpos' : 0 < rqBefore X g k := hpos
  obtain ⟨hn0, hn3, hpair⟩ := hl.b1 hgt hreq hna hpos'
  have hkl : k < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp hreq).1
    simpa using this
  have eb : b1Before X g k = ((X.tr g).take k).countP (Execution.isBarId 1) := rfl
  -- the arrival of ordinal `a = b1Before - 1` of `e`'s thread, before `e`
  obtain ⟨j, pcj, hjk, hfj, hcj⟩ := arrival1_before hpre hX (h := g) (k := k)
    (r := b1Before X g k - 1) (by omega)
  have hpassed : j + 1 < (X.tr g).length := by omega
  have hcta : h / L.block = g / L.block := hgrp.1.2.2.symm
  obtain ⟨i, pci, hfi, hord⟩ := bar1_member hpre hX hfj hpassed (g := h) hcta (by
    rintro ⟨j', pcx, hex⟩
    have h3 := hl.exit hh hex
    have e3 : b1Before X h j' = ((X.tr h).take j').countP (Execution.isBarId 1) := rfl
    obtain ⟨i, pci, -, hb, hc⟩ := arrival1_before hpre hX (h := h) (k := j')
      (r := b1Before X g k - 1) (by omega)
    exact ⟨i, pci, hb, by rw [hc]; exact hcj.symm⟩)
  have hb1 : b1Before X h i + 1 = b1Before X g k := by
    have e4 : b1Before X h i = ((X.tr h).take i).countP (Execution.isBarId 1) := rfl
    simp only at hord
    omega
  have hrq := hpair h i pci none .sync hgrp hfi hb1
  have er : rqBefore X g k = ((X.tr g).take k).countP SetMaxNReg.isRequest := rfl
  have er' : rqBefore X h i = ((X.tr h).take i).countP SetMaxNReg.isRequest := rfl
  -- the previous request of `h`: ordinal `r - 1`, before its arrival `i`
  obtain ⟨j', e', hj', hq, hcnt⟩ := NamedBar.exists_ordinal SetMaxNReg.isRequest
    ((X.tr h).take i) (r := rqBefore X g k - 1) (by omega)
  rw [List.getElem?_take] at hj'
  split at hj'
  · rename_i hji
    rw [List.take_take, Nat.min_eq_left (by omega)] at hcnt
    obtain ⟨pcr, kd⟩ := e'
    cases kd with
    | setMaxReg inc' n' inst' =>
      refine ⟨j', pcr, inc', n', inst', hj', ?_, ?_⟩
      · show ((X.tr h).take j').countP SetMaxNReg.isRequest + 1 =
          ((X.tr g).take k).countP SetMaxNReg.isRequest
        omega
      · have hsame : SameCta L h g := ⟨hh, hgt, hcta⟩
        exact bar1_baseCausality hpre hX hsame hfi hfj hpassed
          (by simp only at hord ⊢; exact hord) hji hjk hkl
    | _ => simp [SetMaxNReg.isRequest] at hq
  · cases hj'

end
end PTX.Kernels.InklingRelDecode.Proof.Bar
