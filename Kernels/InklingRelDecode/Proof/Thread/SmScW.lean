-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSc

@[expose] public section

/-! # The bias widening of the score stage (pcs 1303-1430), wired

From the facts of the table at pc 1303 to the table's facts and the 32 widened pairs, for the
state `d` whose 64 bias words are all `bf16` numbers or the zero half-word (`BfOk`): after group
`j` (pcs `1303 + 4 j` to `1306 + 4 j`) the register `%rd(327 + j)` (id `2276 + j`) holds the pair
of the `f32` numbers of the bias words `2 (31 - j)` and `2 (31 - j) + 1`. The checkpoints' facts
are the registers live there, each valued by the overlay `wex d j` (the pairs written so far) in
front of the table of `d`. The temporaries of a group are dead after it. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat}

/-- The pair the widening group `j` writes: the bias numbers `2 (31 - j)` and `2 (31 - j) + 1`. -/
def wpair (d : D) (j : Nat) : Value :=
  joinValue (.float .f32 (d.bR (2 * (31 - j)))) (.float .f32 (d.bR (2 * (31 - j) + 1)))

/-- The overlay after `j` groups. -/
def wex (d : D) : Nat → List (Nat × Value)
  | 0 => []
  | j + 1 => (2275 + j, wpair d j) :: wex d j

theorem valueEx_wex_off (B : Nat → Value) (d : D) (j : Nat) {r : Nat}
    (h : ¬ (2275 ≤ r ∧ r < 2275 + j)) : valueEx B (wex d j) r = B r := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [wex, valueEx_cons_ne _ _ (by omega)]
    exact ih (by omega)

theorem valueEx_wex_in (B : Nat → Value) (d : D) {j j' : Nat} (h : j' < j) :
    valueEx B (wex d j) (2275 + j') = wpair d j' := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [wex]
    by_cases hj : j' = j
    · subst hj
      exact valueEx_cons_self _ _ _ _
    · rw [valueEx_cons_ne _ _ (by omega)]
      exact ih (by omega)

/-- A pack of two bias words has four bytes. -/
theorem joinValue_bytes {a b : Value} (ha : BfOk a) (hb : BfOk b) : (joinValue a b).bytes = 4 := by
  rcases ha with ⟨x, rfl⟩ | rfl <;> rcases hb with ⟨y, rfl⟩ | rfl <;> rfl

/-! ### The code and the liveness of one group -/

theorem live_w1 : ∀ j < 32, (1947 - j) ∈ Flow.live (1303 + 4 * j) := by decide +kernel

theorem live_w1' : ∀ j < 32, subX (Flow.live (1303 + 4 * j + 1)) (Flow.live (1303 + 4 * j))
    [397 + 2 * j, 398 + 2 * j] = true := by decide +kernel

theorem live_w2 : ∀ j < 32, (398 + 2 * j) ∈ Flow.live (1303 + 4 * j + 1) := by decide +kernel

theorem live_w2' : ∀ j < 32, subX (Flow.live (1303 + 4 * j + 1 + 1))
    (Flow.live (1303 + 4 * j + 1)) [946 + 2 * j] = true := by decide +kernel

theorem live_w3 : ∀ j < 32, (397 + 2 * j) ∈ Flow.live (1303 + 4 * j + 1 + 1) := by decide +kernel

theorem live_w3' : ∀ j < 32, subX (Flow.live (1303 + 4 * j + 1 + 1 + 1))
    (Flow.live (1303 + 4 * j + 1 + 1)) [947 + 2 * j] = true := by decide +kernel

theorem live_w4 : ∀ j < 32, (947 + 2 * j) ∈ Flow.live (1303 + 4 * j + 1 + 1 + 1) ∧
    (946 + 2 * j) ∈ Flow.live (1303 + 4 * j + 1 + 1 + 1) := by decide +kernel

theorem live_w4' : ∀ j < 32, subX (Flow.live (1303 + 4 * j + 1 + 1 + 1 + 1))
    (Flow.live (1303 + 4 * j + 1 + 1 + 1)) [2275 + j] = true := by decide +kernel

theorem live_wend : ∀ j < 32, disj (Flow.live (1303 + 4 * j + 4))
    [397 + 2 * j, 398 + 2 * j, 946 + 2 * j, 947 + 2 * j] = true := by decide +kernel

/-- **One group of the widening**: the packed word of the bias words `2 (31 - j)` and
`2 (31 - j) + 1` becomes the pair of their `f32` numbers in `%rd(327 + j)`. -/
theorem seg_widenG (d : D) {j : Nat} (hj : j < 32) (hb : ∀ k < 64, BfOk (d.wd k)) :
    Seg kernel asms L g 4 (1303 + 4 * j)
      (factsFrom (Flow.live (1303 + 4 * j)) (valueEx (valueOf L g d) (wex d j)))
      (1303 + 4 * j + 4)
      (factsFrom (Flow.live (1303 + 4 * j + 4)) (valueEx (valueOf L g d) (wex d (j + 1)))) := by
  obtain ⟨c1, c2, c3, c4⟩ := widen_code j hj
  have hno := emu_widen j hj
  have hq : 31 - j < 32 := by omega
  have hb0 := hb (2 * (31 - j)) (by omega)
  have hb1 := hb (2 * (31 - j) + 1) (by omega)
  -- the packed word and its halves
  have hsrc : valueEx (valueOf L g d) (wex d j) (1947 - j) =
      joinValue (d.wd (2 * (31 - j))) (d.wd (2 * (31 - j) + 1)) := by
    rw [valueEx_wex_off _ d j (by omega)]
    have := valueOf_packed (L := L) (g := g) d hq
    rw [show 1916 + (31 - j) = 1947 - j by omega] at this
    exact this
  -- step 1: the unpack
  have s1 : Seg kernel asms L g 1 (1303 + 4 * j)
      (factsFrom (Flow.live (1303 + 4 * j)) (valueEx (valueOf L g d) (wex d j)))
      (1303 + 4 * j + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1)) (valueEx (valueOf L g d)
        ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
          wex d j))) := by
    refine Seg.set2 (unpack32At_spec c1) rfl (by omega) (fun t h => ?_)
      (subX_cov2 (live_w1' j hj))
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (hno 0 (by omega))
    have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g d) (wex d j))
      (live_w1 j hj))
    rw [hsrc] at hr
    exact exec_unpackV hS hr (joinValue_bytes hb0 hb1) (split32_join hb0 hb1) (bfOk_bytes hb0)
      (bfOk_bytes hb1)
  -- step 2: the conversion of the high half
  have s2 : Seg kernel asms L g 1 (1303 + 4 * j + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1)) (valueEx (valueOf L g d)
        ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
          wex d j)))
      (1303 + 4 * j + 1 + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1 + 1)) (valueEx (valueOf L g d)
        ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
          ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
            wex d j)))) := by
    have hc : kernel.code[1303 + 4 * j + 1]? =
        some ⟨none, .cvt (cvtW (946 + 2 * j) (398 + 2 * j))⟩ := by
      rw [show 1303 + 4 * j + 1 = 1304 + 4 * j by omega]
      exact cvtWidenAt_spec c2
    refine Seg.set1 hc rfl (fun t h => ?_) (subX_sound (live_w2' j hj))
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (hno 1 (by omega))
    have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g d)
      ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) :: wex d j))
      (live_w2 j hj))
    rw [valueEx_cons_self] at hr
    rw [exec_cvtWidenE hS hr (readEReal_bfOk hb1), erealValue_f32_coe]
    rfl
  -- step 3: the conversion of the low half
  have s3 : Seg kernel asms L g 1 (1303 + 4 * j + 1 + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1 + 1)) (valueEx (valueOf L g d)
        ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
          ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
            wex d j))))
      (1303 + 4 * j + 1 + 1 + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1 + 1 + 1)) (valueEx (valueOf L g d)
        ([(947 + 2 * j, .float .f32 (d.bR (2 * (31 - j))))] ++
          ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
            ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
              wex d j))))) := by
    have hc : kernel.code[1303 + 4 * j + 1 + 1]? =
        some ⟨none, .cvt (cvtW (947 + 2 * j) (397 + 2 * j))⟩ := by
      rw [show 1303 + 4 * j + 1 + 1 = 1305 + 4 * j by omega]
      exact cvtWidenAt_spec c3
    refine Seg.set1 hc rfl (fun t h => ?_) (subX_sound (live_w3' j hj))
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (hno 2 (by omega))
    have hr := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g d)
      ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
        ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
          wex d j))) (live_w3 j hj))
    rw [List.singleton_append, valueEx_cons_ne _ _ (by omega), valueEx_cons_ne _ _ (by omega),
      valueEx_cons_self] at hr
    rw [exec_cvtWidenE hS hr (readEReal_bfOk hb0), erealValue_f32_coe]
    rfl
  -- step 4: the pack
  have s4 : Seg kernel asms L g 1 (1303 + 4 * j + 1 + 1 + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1 + 1 + 1)) (valueEx (valueOf L g d)
        ([(947 + 2 * j, .float .f32 (d.bR (2 * (31 - j))))] ++
          ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
            ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
              wex d j)))))
      (1303 + 4 * j + 1 + 1 + 1 + 1)
      (factsFrom (Flow.live (1303 + 4 * j + 1 + 1 + 1 + 1)) (valueEx (valueOf L g d)
        ([(2275 + j, wpair d j)] ++
          ([(947 + 2 * j, .float .f32 (d.bR (2 * (31 - j))))] ++
            ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
              ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
                wex d j)))))) := by
    have hc : kernel.code[1303 + 4 * j + 1 + 1 + 1]? = some ⟨none, .move
        ⟨.pack, .int .b 64, [some (2275 + j)], [.reg (947 + 2 * j), .reg (946 + 2 * j)]⟩⟩ := by
      rw [show 1303 + 4 * j + 1 + 1 + 1 = 1306 + 4 * j by omega]
      exact packAt_spec c4
    refine Seg.set1 hc rfl (fun t h => ?_) (subX_sound (live_w4' j hj))
    have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree (hno 3 (by omega))
    have hA := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g d)
      ([(947 + 2 * j, .float .f32 (d.bR (2 * (31 - j))))] ++
        ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
          ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
            wex d j)))) (live_w4 j hj).1)
    have hB := holds_mem h.2.2.2.2 (mem_factsFrom (val := valueEx (valueOf L g d)
      ([(947 + 2 * j, .float .f32 (d.bR (2 * (31 - j))))] ++
        ([(946 + 2 * j, .float .f32 (d.bR (2 * (31 - j) + 1)))] ++
          ((398 + 2 * j, d.wd (2 * (31 - j) + 1)) :: (397 + 2 * j, d.wd (2 * (31 - j))) ::
            wex d j)))) (live_w4 j hj).2)
    rw [List.singleton_append, valueEx_cons_self] at hA
    rw [List.singleton_append, valueEx_cons_ne _ _ (by omega), List.singleton_append,
      valueEx_cons_self] at hB
    exact exec_pack hS (Or.inr rfl) hA hB rfl rfl
  -- the temporaries are dead
  have s := ((s1.comp s2).comp s3).comp s4
  refine Seg.of_len (Seg.overlay_end s fun r hr => ?_) rfl
  have hn := disj_sound (live_wend j hj) r (by simpa using hr)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨n1, n2, n3, n4⟩ := hn
  simp only [wex, List.singleton_append]
  by_cases h0 : r = 2275 + j
  · subst h0
    rw [valueEx_cons_self, valueEx_cons_self]
  · simp only [valueEx_cons_ne _ _ h0, valueEx_cons_ne _ _ n1, valueEx_cons_ne _ _ n2,
      valueEx_cons_ne _ _ n3, valueEx_cons_ne _ _ n4]

/-- **The first `m` groups of the widening** (pcs 1303 to `1303 + 4 m`). -/
theorem seg_widens (d : D) (hb : ∀ k < 64, BfOk (d.wd k)) : ∀ m, m ≤ 32 →
    Seg kernel asms L g (4 * m) 1303 (factsAt L g 1303 d) (1303 + 4 * m)
      (factsFrom (Flow.live (1303 + 4 * m)) (valueEx (valueOf L g d) (wex d m))) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih =>
    exact fun hm => Seg.of_len ((ih (by omega)).comp
      (seg_widenG d (j := m) (by omega) hb)) (by omega)

/-- **The bias widening** (pcs 1303 to 1430): the 32 pairs of `f32` bias numbers. -/
theorem seg_widen32 (d : D) (hb : ∀ k < 64, BfOk (d.wd k)) :
    Seg kernel asms L g 128 1303 (factsAt L g 1303 d) 1431
      (factsFrom (Flow.live 1431) (valueEx (valueOf L g d) (wex d 32))) :=
  seg_widens d hb 32 (le_refl 32)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
