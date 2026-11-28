-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS

@[expose] public section

/-! # The first window's inputs do not depend on the words the round's events bring

`w1V` reads the facts of a canonical wait of the score load (`canon`: the words and counter the
first window reads, no broadcast words). At the wait itself it agrees with the facts of the state
on the registers the window reads: the control facts differ only in the registers of the
broadcast words (`held`), which the window does not read. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow Control

noncomputable section
variable {e : Entry} {L : Launch} {g : Nat}

theorem lookup_append_eq {X Y : List (Nat × Value)} {r : Nat} :
    (X ++ Y).lookup r = (X.lookup r).or (Y.lookup r) := by
  induction X with
  | nil => simp [List.lookup]
  | cons q X ih =>
    by_cases h : (r == q.1) = true
    · simp [List.lookup, h]
    · simp only [List.cons_append, List.lookup, h]
      exact ih

theorem lookup_factsFrom {K : List Nat} {V : Nat → Value} {r : Nat} :
    (factsFrom K V).lookup r = if r ∈ K then some (V r) else none := by
  induction K with
  | nil => simp [factsFrom]
  | cons k K ih =>
    by_cases h : r = k
    · subst h; simp [factsFrom]
    · have hb : (r == k) = false := by simpa using h
      simp only [factsFrom, List.map_cons, List.lookup, hb] at ih ⊢
      simpa [h] using ih

theorem kW1_held : ∀ r ∈ kW1, r ≠ 506 ∧ r ≠ 944 ∧ r ≠ 945 ∧ r ≠ 1542 ∧ r ≠ 1543 ∧ r ≠ 1544 ∧
    r ≠ 1534 ∧ r ≠ 1536 ∧ r ≠ 1538 ∧ r ≠ 1540 ∧ r ≠ 1611 ∧ r ≠ 1676 := by decide +kernel

theorem valueOf_i {c c' : Control.D} (h : c.i = c'.i) {r : Nat} (hr : r ∈ kW1) :
    valueOf e L g c r = valueOf e L g c' r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := kW1_held r hr
  simp only [valueOf, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ite_false, h]

/-- **At the wait of the score load** the canonical facts and the state's agree on the registers
the first window reads. -/
theorem w1V_eq {d : D} (hs : d.c.site = .waitLd) {r : Nat} (hr : r ∈ kW1) :
    w1V e L g d r = lookupD (baseF e L g d) r := by
  have hm : m0 d = d.v.m := by simp [m0, hs]
  have hd : (⟨{(canon d).c with site := .waitLd}, (canon d).v⟩ : D) =
      ⟨{ site := .waitLd, i := d.c.i },
        { m := d.v.m, cur := d.v.cur, ld := d.v.ld, s := d.v.s }⟩ := by
    simp [canon, hm]
  unfold w1V baseF lookupD
  rw [hd]
  simp only [lookup_append_eq, Control.facts, hs, lookup_factsFrom]
  rw [valueOf_i (e := e) (L := L) (g := g) (c := ⟨.waitLd, d.c.i, {}⟩) (c' := d.c) rfl hr]
  simp [dF, dFS, pF, wF, wFS, hs, inRound]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
