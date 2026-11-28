-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.CodeS
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Kinds
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Step
public import Kernels.InklingRelDecode.Proof.Softmax.Data.Constants

@[expose] public section

/-! # What the first window reads, from the words of the value state

A value state is *typed* (`VTyp`) when the bias words it holds are `bf16` payloads or the default
zero and the scores the load returned are numbers. Then at the wait of the score load the facts the
first window reads (`w1V`) are numbers: the packs have `bf16` halves, the pairs of scores are pairs
of numbers, and register 1960 is the pair of `1 / scale` (`W1In`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control PTX.Assumption

noncomputable section

/-- A bias word: a `bf16` payload, or the 16-bit zero of a block with no bias. -/
def Bw (x : Value) : Prop := (∃ r : ℝ, x = .float .bf16 r) ∨ x = dflt

/-- **A typed value state**: its bias words are `Bw`, its scores numbers. -/
structure VTyp (v : Vals) : Prop where
  cur : ∀ j, Bw (v.cur j)
  ld : ∀ j, Bw (v.ld j)
  s : ∀ x ∈ v.s, SK.fl.Has x

theorem bw_bf16 {x : Value} (h : Bw x) : Bf16 x := by
  rcases h with ⟨r, rfl⟩ | rfl
  · exact ⟨r, by simp [readEReal, pure, Except.pure]⟩
  · have hz := classify_bits (fmt := .bf16) (n := 0) (x := .zero false) (by decide) (by decide)
    change classify .bf16 (.bits 16 (BitVec.ofNat 64 0)) = .ok (.zero false) at hz
    exact ⟨0, by
      change readEReal.ofDatum (classify .bf16 (.bits 16 (BitVec.ofNat 64 0))) = _
      rw [hz]; rfl⟩

theorem bw_bytes {x : Value} (h : Bw x) : x.bytes = 2 := by
  rcases h with ⟨r, rfl⟩ | rfl <;> rfl

/-- **The pack of two bias words splits back into them.** -/
theorem packV_split {x y : Value} (hx : Bw x) (hy : Bw y) : splitValue 32 (packV x y) = (x, y) := by
  have e : packV x y = joinValue x y := by
    simp [packV, pack32E, bw_bytes hx, bw_bytes hy, okVal]
  rw [e]
  rcases hx with ⟨r, rfl⟩ | rfl <;> rcases hy with ⟨s, rfl⟩ | rfl
  · rfl
  · rfl
  · rfl
  · decide

theorem packV_bf16 {x y : Value} (hx : Bw x) (hy : Bw y) : Bf16Pair (packV x y) := by
  unfold Bf16Pair
  rw [packV_split hx hy]
  exact ⟨bw_bf16 hx, bw_bf16 hy⟩

theorem getD_has {P : Value → Prop} {l : List Value} {d : Value} (h : ∀ x ∈ l, P x) (hd : P d)
    (i : Nat) : P (l.getD i d) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact hd

theorem lookup_of_mem {F : List (Nat × Value)} {r : Nat} {v : Value}
    (hn : (F.map Prod.fst).count r = 1) (h : (r, v) ∈ F) : F.lookup r = some v := by
  induction F with
  | nil => simp at h
  | cons p F ih =>
    by_cases hr : p.1 = r
    · have h0 : (F.map Prod.fst).count r = 0 := by
        rw [List.map_cons, List.count_cons] at hn; simp [hr] at hn; omega
      rcases List.mem_cons.mp h with h | h'
      · subst h; simp [List.lookup]
      · have hm : r ∈ F.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) h'
        exact absurd (List.count_pos_iff.mpr hm) (by omega)
    · have hb : (r == p.1) = false := beq_false_of_ne (fun h => hr h.symm)
      have hn' : (F.map Prod.fst).count r = 1 := by
        rw [List.map_cons, List.count_cons, show (p.1 == r) = false by simpa using hr] at hn
        simpa using hn
      rcases List.mem_cons.mp h with h | h'
      · exact absurd (congrArg Prod.fst h).symm hr
      · simp only [List.lookup, hb]
        exact ih hn' h'

theorem lookupD_mem {F : List (Nat × Value)} {r : Nat} {v : Value}
    (hn : (F.map Prod.fst).count r = 1) (h : (r, v) ∈ F) : lookupD F r = v := by
  simp [lookupD, lookup_of_mem hn h]

variable {e : Entry} {L : Launch} {g : Nat}

theorem kBase_once : (List.range' 1916 32 ++ List.range' 2447 32 ++ [1960]).all
    (fun r => kBase.count r == 1) = true := by decide +kernel

/-- The facts of the wait of the score load, as a state of it. -/
abbrev atWait (d : D) : D := ⟨{d.c with site := .waitLd}, d.v⟩

theorem base_once (d : D) {r : Nat} (h : r ∈ List.range' 1916 32 ++ List.range' 2447 32 ++ [1960]) :
    ((baseF e L g (atWait d)).map Prod.fst).count r = 1 := by
  rw [w1_keys (e := e) (L := L) (g := g) (d := atWait d) rfl]
  simpa using List.all_eq_true.mp kBase_once r h

theorem pack_mem (d : D) {r : Nat} (h1 : 1916 ≤ r) (h2 : r < 1948) :
    (r, packV (d.v.cur (2 * (r - 1916))) (d.v.cur (2 * (r - 1916) + 1))) ∈
      baseF e L g (atWait d) := by
  have : r = 1916 + (r - 1916) := by omega
  have hm : (r, packV (d.v.cur (2 * (r - 1916))) (d.v.cur (2 * (r - 1916) + 1))) ∈
      packF d.v.cur := by
    simp only [packF, List.mem_map, List.mem_range]
    exact ⟨r - 1916, by omega, by rw [← this]⟩
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_append_left _ (show _ ∈ packF d.v.cur from hm)))))

theorem score_mem (d : D) {r : Nat} (h1 : 2447 ≤ r) (h2 : r < 2479) :
    (r, joinValue (d.v.s.getD (2 * (r - 2447)) (b32 0)) (d.v.s.getD (2 * (r - 2447) + 1) (b32 0))) ∈
      baseF e L g (atWait d) := by
  have : r = 2447 + (r - 2447) := by omega
  have hm : (r, joinValue (d.v.s.getD (2 * (r - 2447)) (b32 0))
      (d.v.s.getD (2 * (r - 2447) + 1) (b32 0))) ∈ pF (atWait d) := by
    simp only [pF, spF, ite_true, List.mem_map, List.mem_range]
    exact ⟨r - 2447, by omega, by rw [← this]⟩
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ hm)))

theorem step_mem (d : D) :
    (1960, derV e L g 1960) ∈ baseF e L g (atWait d) := by
  have hm : (1960, derV e L g 1960) ∈ derF e L g (atWait d).c.site := by
    simp only [derF, factsFrom, keysC, List.mem_map, List.mem_append]
    exact ⟨1960, by simp, rfl⟩
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hm))

/-- **The facts the first window reads are numbers**, for a typed value state. -/
theorem w1_in {Q : Params} {m : Mem0} (hp : Pre Q L m) {d : D} (hv : VTyp d.v) :
    W1In (w1V e L g d) := by
  refine ⟨fun r h1 h2 => ?_, fun r h1 h2 => ?_, ?_⟩
  · rw [w1V, lookupD_mem (base_once (canon d) (by simp; omega)) (pack_mem (canon d) h1 h2)]
    exact packV_bf16 (hv.cur _) (hv.cur _)
  · rw [w1V, lookupD_mem (base_once (canon d) (by simp; omega)) (score_mem (canon d) h1 h2)]
    exact join_fl_has (getD_has hv.s zero_has _) (getD_has hv.s zero_has _)
  · have hs := scaleVal_float (L := L) hp
    have h0 : Q.scale ≠ 0 := hp.scalePos.ne'
    rw [w1V, lookupD_mem (base_once (canon d) (by simp)) (step_mem (canon d)), derV_1960 hs h0]
    exact join_fl_has (has_float_fl _) (has_float_fl _)

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
