-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.BarEarlyMember
public import Lemmas.Kernel.Safety.Handoff

@[expose] public section

/-! # The hand-off of a barrier's first instances

A proof tool, generic over the kernel (kernel-local until lane L's request L-m lands; recorded
for promotion next to `Handoff.of_bar` in `Lemmas/Kernel/Safety/Handoff.lean`).

`Frame.Handoff.of_bar` orders a named barrier's participants by their arrival counts, from one
`(count, p)` for every arrival on the barrier id (`NamedBar.Sources`) and the barrier's arrival
counts over each whole trace (`hN`, `hexit`). A barrier id that several groups use in turn
(Inkling's barrier 0: all eight warps at the startup, the four default warps with count 128
later), or a kernel inside its own following induction, knows only each thread's first arrivals.
`Handoff.of_barEarly` gives the same order for producer uses up to `N`, from:

* `NamedBar.EarlySources … N`: the arrivals of source ordinal at most `N` are the group's;
* `hexit`: a participant that exits has made its first `N + 1` arrivals before its exit.

Both speak only of each thread's events up to its `(N + 1)`-th arrival. The proof is
`of_bar`'s, with `NamedBar.early_member_arrival` and `NamedBar.early_same_ordinal_baseCausality`
(`Proof2/Lib/BarEarly*.lean`, generic as well) in place of the whole-trace generation lemmas. -/

namespace PTX.Frame

open PTX PTX.Flow

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [Fact K.NoBarArrive]

/-- **The first `N + 1` instances of a barrier hand off from its participants to its `bar.sync`
participants** of one CTA: an event of `g` whose producer use (the barrier's arrivals up to and
including it) is at most `N` and below the consumer use of an event of `h` (the arrivals before
it) happens before that event. -/
theorem Handoff.of_barEarly (hX : Consistent L K A mem0 X) {n : Nat} (hn : 0 < n)
    {count : Option Nat} (hcount : CtaBarrier.target L.block count = .ok n) {p : Finset Nat}
    (hcard : p.card = n) (hbound : ∀ w ∈ p, w < L.block / 32) {id N : Nat} (hid : id < 16)
    (hS : NamedBar.EarlySources L X count p id N)
    (hexit : ∀ g, g < L.threads → (g % L.block) / 32 ∈ p → ∀ j pc,
      X.get (g, j) = some ⟨pc, .exit⟩ → N + 1 ≤ ((X.tr g).take j).countP (Execution.isBarId id))
    {g h e f : Nat} (hsame : SameCta L g h) (hpg : (g % L.block) / 32 ∈ p)
    (hf : f < (X.tr h).length)
    (hlt : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) <
      ((X.tr h).take f).countP (Execution.isBarId id))
    (hle : ((X.tr g).take (e + 1)).countP (Execution.isBarId id) ≤ N) :
    baseCausality L X (g, e) (h, f) := by
  set q := ((X.tr g).take (e + 1)).countP (Execution.isBarId id) with hq
  have hgt : g < L.threads := hsame.1
  have hht : h < L.threads := hsame.2.1
  -- the consumer's barrier of ordinal `q`
  obtain ⟨j, ev, hj, hbj, hcj⟩ := MbarRing.Slot.exists_nth_countP (Execution.isBarId id)
    (show q + 1 ≤ ((X.tr h).take f).countP (Execution.isBarId id) by omega)
  have hjf : j < f := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.take_take, Nat.min_eq_left hjf.le] at hcj
  have hgetj : X.get (h, j) = some ev := by
    change (X.tr h)[j]? = some ev
    rw [← hj, List.getElem?_take, ite_eq_left hjf]
  obtain ⟨pcj, kj⟩ := ev
  cases kj with
  | bar idj cntj modej =>
    simp only [Execution.isBarId, beq_iff_eq] at hbj
    subst hbj
    have hsrc := hS (h, j) pcj cntj ⟨modej, hgetj⟩ hht (by dsimp only; omega)
    obtain ⟨-, hcnt⟩ := hsrc
    rw [hcnt] at hgetj
    have hmode : modej = .sync := by
      cases modej with
      | sync => rfl
      | arrive => exact absurd hgetj (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
    subst hmode
    have hfb : X.IsBarrier (h, j) idj count pcj := hgetj
    obtain ⟨i, pci, hbi, hci⟩ := NamedBar.early_member_arrival (f := (h, j)) hX hn hcount hcard
      hbound hid hS hfb (by dsimp only; omega) (by dsimp only; omega)
      (show g / L.block = h / L.block from hsame.2.2) hpg (by
        rintro ⟨jx, pcx, hex⟩
        have hge : q + 1 ≤ ((X.tr g).take jx).countP (Execution.isBarId idj) := by
          have := hexit g hgt hpg jx pcx hex
          omega
        obtain ⟨i, ev', hi, hbi, hci⟩ :=
          MbarRing.Slot.exists_nth_countP (Execution.isBarId idj) hge
        have hix : i < jx := by
          have := (List.getElem?_eq_some_iff.mp hi).1
          simp only [List.length_take] at this
          omega
        rw [List.take_take, Nat.min_eq_left hix.le] at hci
        have hgeti : X.get (g, i) = some ev' := by
          change (X.tr g)[i]? = some ev'
          rw [← hi, List.getElem?_take, ite_eq_left hix]
        obtain ⟨pci, ki⟩ := ev'
        cases ki with
        | bar idi cnti modei =>
          simp only [Execution.isBarId, beq_iff_eq] at hbi
          subst hbi
          have hcnti := (hS (g, i) pci cnti ⟨modei, hgeti⟩ hgt (by dsimp only; omega)).2
          rw [hcnti] at hgeti
          have hmi : modei = .sync := by
            cases modei with
            | sync => rfl
            | arrive => exact absurd hgeti (Consistent.noBarArrive (Fact.out) hX _ _ _ _)
          subst hmi
          exact ⟨i, pci, hgeti, by dsimp only; omega⟩
        | _ => simp [Execution.isBarId] at hbi)
    simp only at hci
    have hiq : ((X.tr g).take i).countP (Execution.isBarId idj) = q := hci.trans hcj
    have hei : e < i := by
      by_contra hle'
      have h1 := Handoff.countP_take_succ_ge (P := Execution.isBarId idj) (es := X.tr g) (e := e)
        hbi (by simp [Execution.isBarId]) (by omega)
      rw [hiq, ← hq] at h1
      omega
    exact NamedBar.early_same_ordinal_baseCausality hX hn hcount hcard hbound hid hS hsame hbi hfb
      (by omega) (hiq.trans hcj.symm) (by omega) hei hjf hf
  | _ => simp [Execution.isBarId] at hbj

end PTX.Frame
