-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5MTrace
public import Kernels.InklingRelDecode.Proof.Interface.BarStatic
public import Kernels.InklingRelDecode.Proof.Protocol.BarLaneLoop
public import Kernels.InklingRelDecode.Proof.Protocol.IpBarMember

@[expose] public section

/-!
# The scratch words: the statements about barrier 0 and the members of a loop generation

Two statements the memory argument takes, besides those of `Interface/Lk5Defs.lean`:

* `StoreWord c i`: `StoreUniform` with the stored word the value (`erealValue .f32 w`) of a number
  `w` that is not `+inf` (the form `minE` gives a minimum of numbers, `Sm.minE_readsAs`), so that
  the word is a scalar of four bytes that the load rebuilds unchanged (`storeUniform_of_word`);
* `B0Pos c i`: where a default thread of CTA `c` is when it has made as many barrier-0 events as a
  thread at `bar23` of iteration `i`: (1) a barrier-0 event of that count is its own `bar23` of
  iteration `i`; (2) a barrier-0 event of the next count has the loop count 128; (3) a thread that
  exits has made at least two more. All three are consequences of the count of barrier-0 events of
  a default thread as a function of its site, its iteration and the lazy-rescale decisions of the
  iterations before `i` (`DecAgree` of iterations `< i`).

From `B0Pos`: `member23`, every default thread of the CTA has its `bar23` of iteration `i`, of the
same count, when one thread passed its own (`NamedBar.D_member_arrival`); `member_next`, the
arrival of the next count likewise.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The number of barrier-0 events of thread `g` before its event `k`. -/
abbrev cnt0 (X : Execution) (g k : Nat) : Nat := cnt (Execution.isBarId 0) X g k

/-- **The lanes of each default warp of CTA `c` store at `store10` of iteration `i` the value of
one number that is not `+inf`.** -/
def StoreWord (Q : Params) (L : Launch) (X : Execution) (c i : Nat) : Prop :=
  ∀ r < 4, ∃ w : EReal, w ≠ ⊤ ∧
    ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c → g % L.block / 32 = r →
      St Q L X g k = some (some (.d (.sm d))) → d.site = .store10 → d.i = i →
      d.stg.cm4 = erealValue .f32 w

/-- **Where a default thread is at the barrier-0 count of `bar23` of iteration `i`.** -/
def B0Pos (Q : Params) (L : Launch) (X : Execution) (c i : Nat) : Prop :=
  ∀ {g k : Nat} {d : Sm.D}, g < L.threads → g / L.block = c →
    St Q L X g k = some (some (.d (.sm d))) → d.site = .bar23 → d.i = i →
    ∀ {g' : Nat}, g' < L.threads → g' / L.block = c → g' % L.block < 128 →
      (∀ {k' pc : Nat} {cn : Option Nat}, X.IsBarrier (g', k') 0 cn pc →
        cnt0 X g' k' = cnt0 X g k → ∃ d' : Sm.D,
          St Q L X g' k' = some (some (.d (.sm d'))) ∧ d'.site = .bar23 ∧ d'.i = i) ∧
      (∀ {k' pc : Nat} {cn : Option Nat}, X.IsBarrier (g', k') 0 cn pc →
        cnt0 X g' k' = cnt0 X g k + 1 → cn = some 128) ∧
      (∀ {j pcx : Nat}, X.get (g', j) = some ⟨pcx, .exit⟩ → cnt0 X g k + 2 ≤ cnt0 X g' j)

/-- **A thread with more than `φ` barrier-0 events before `j` has its event of count `φ`.** -/
theorem nth_bar0 (hX : Consistent L kernel asms mem0 X) (hb : L.block ≠ 128) {g j φ : Nat}
    (h : φ < cnt0 X g j) : ∃ i pc cn, i < j ∧ X.IsBarrier (g, i) 0 cn pc ∧ cnt0 X g i = φ := by
  obtain ⟨i, y, hi, hy, hord⟩ := CtaBarrier.countP_index
    (xs := (X.tr g).take j) (p := Execution.isBarId 0) h
  have hij : i < j := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hij] at hi
  obtain ⟨pcy, cy, my, rfl⟩ := NamedBar.isBarId_form hy
  have hget : X.get (g, i) = some ⟨pcy, .bar 0 cy my⟩ := hi
  obtain ⟨hm, -⟩ := bar_event_static hX hb hget
  subst hm
  rw [List.take_take, Nat.min_eq_left hij.le] at hord
  exact ⟨i, pcy, cy, hij, hget, hord⟩

theorem loop_mem {t : Nat} (h : t % L.block < 128) : (t % L.block) / 32 ∈ Bar.loopGroup := by
  simp only [Bar.loopGroup, Finset.mem_range]
  omega

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **Every default thread of the CTA has the arrival of a count another default thread passed**,
given that a thread that exits has made more barrier-0 events. -/
theorem member_of {f : EvId} {pc : Nat} {cn : Option Nat} (hfb : X.IsBarrier f 0 cn pc)
    (hpass : f.2 + 1 < (X.tr f.1).length) (hfd : f.1 % L.block < 128) {t : Nat}
    (htc : t / L.block = f.1 / L.block) (htd : t % L.block < 128)
    (hex : ∀ {j pcx : Nat}, X.get (t, j) = some ⟨pcx, .exit⟩ → cnt0 X f.1 f.2 < cnt0 X t j) :
    ∃ i pc' cn', X.IsBarrier (t, i) 0 cn' pc' ∧ cnt0 X t i = cnt0 X f.1 f.2 := by
  have hb : L.block ≠ 128 := by have := hpre.block; omega
  have hexited : (∃ j pcx, X.get (t, j) = some ⟨pcx, .exit⟩) →
      ∃ i pc' cn', X.IsBarrier (t, i) 0 cn' pc' ∧
        ((X.tr t).take i).countP (Execution.isBarId 0) =
          ((X.tr f.1).take f.2).countP (Execution.isBarId 0) := by
    rintro ⟨j, pcx, hj⟩
    obtain ⟨i, pc', cn', -, hbar, hord⟩ := nth_bar0 hX hb (hex hj)
    exact ⟨i, pc', cn', hbar, hord⟩
  exact NamedBar.D_member_arrival hX (Bar.bar0_sources hpre hX hf.sound hf.tracked)
    (Bar.loopGroup_sub hpre) Bar.loopGroup_card (Bar.loopGroup_ne hpre) Bar.loopGroup_target
    hfb hpass (loop_mem hfd) htc (loop_mem htd) hexited

/-- **Every default thread of the CTA has its `bar23` of iteration `j` at the count of a thread
that passed its own.** -/
theorem member23 {c j : Nat} (hP : B0Pos Q L X c j) {g k : Nat} {d : Sm.D} (hg : g < L.threads)
    (hgc : g / L.block = c) (hσ : St Q L X g k = some (some (.d (.sm d)))) (hs : d.site = .bar23)
    (hj : d.i = j) (hpass : k + 1 < (X.tr g).length) {t : Nat} (ht : t < L.threads)
    (htc : t / L.block = c) (htd : t % L.block < 128) :
    ∃ a dt, St Q L X t a = some (some (.d (.sm dt))) ∧ dt.site = .bar23 ∧ dt.i = j ∧
      cnt0 X t a = cnt0 X g k ∧
      X.get (t, a) = some ⟨Sm.Site.bar23.pc, .bar 0 (some 128) .sync⟩ := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hev := bar_event hpre hX hf hg he hσ (by rw [hs]; trivial)
  rw [hs] at hev
  have hgd : g % L.block < 128 := sm_default (by omega) hσ
  have hIs : X.IsBarrier (g, k) 0 (some 128) Sm.Site.bar23.pc := by
    show X.get (g, k) = _
    rw [show X.get (g, k) = some e from he, hev]
  obtain ⟨h1, -, h3⟩ := hP hg hgc hσ hs hj ht htc htd
  obtain ⟨a, pc', cn', hbar, hord⟩ := member_of hpre hX hf hIs (by simpa using hpass) hgd
    (htc.trans hgc.symm) htd (fun hx => by have := h3 hx; simp only at this ⊢; omega)
  obtain ⟨dt, hσt, hst, hit⟩ := h1 hbar hord
  have hbar' : X.get (t, a) = some ⟨pc', .bar 0 cn' .sync⟩ := hbar
  have hev' := bar_event hpre hX hf ht hbar' hσt (by rw [hst]; trivial)
  rw [hst] at hev'
  exact ⟨a, dt, hσt, hst, hit, hord, by rw [hbar', hev']⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Interface.Lk
