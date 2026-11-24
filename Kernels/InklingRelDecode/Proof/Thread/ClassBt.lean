-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ShapeWordsKeep
public import Kernels.InklingRelDecode.Proof.Thread.ShapeProCopy
public import Kernels.InklingRelDecode.Proof.Thread.ProBSpec

@[expose] public section

/-!
# The prologue's block-table words: where they are kept and which blocks exist

The prologue's three block-table loads of a block `j` (sites `lbA_j`, `lbB_j`, loads `2 j` and
`2 j + 1`) set the words `b_{2 j}` and `b_{2 j + 1}` of `Dat`, and no other site changes them.
The copies of block `j` (`ptc_j_*`) are in the sites after the load of their slab's word
(`lbAfter`), and a block's sites are entered only through the branch that tests the number of
blocks (`v_p53`, `v_p63`, `v_p72`: the number `%r31` of blocks to preload is not 0, not 1, not
below 3).

* `btW_next`: a step from a site that is not a block-table load keeps every word;
* `lbAfter_next`: a step into a site after the load of word `k` is a step from a site after the
  load or from the load itself;
* `next_lb`: the step at the load of word `k` stores the loaded word in word `k` and moves to a
  site after it;
* `gate_next`: the invariant `Gate` (a block's sites are entered only where the block is
  preloaded) is kept by every step.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-! ### The sites of a block -/

/-- The sites of block `j`: from the barrier wait to the last copy. -/
def blkSites : Nat → List Site
  | 0 => [.pbA0, .arr0, .lbA0, .pbB0, .psh0, .pel0_0, .ptc0_0, .pbC0, .pel0_1, .ptc0_1, .lbB0,
      .pbD0, .pel0_2, .ptc0_2, .pbE0, .pel0_3, .ptc0_3]
  | 1 => [.pbA1, .arr1, .lbA1, .pbB1, .psh1, .pel1_0, .ptc1_0, .pbC1, .pel1_1, .ptc1_1, .lbB1,
      .pbD1, .pel1_2, .ptc1_2, .pbE1, .pel1_3, .ptc1_3]
  | 2 => [.pbA2, .arr2, .lbA2, .pbB2, .psh2, .pel2_0, .ptc2_0, .pbC2, .pel2_1, .ptc2_1, .lbB2,
      .pbD2, .pel2_2, .ptc2_2, .pbE2, .pel2_3, .ptc2_3]
  | _ => []

/-- The sites of block `k / 2` after the load of block-table word `k`. -/
def lbAfter : Nat → List Site
  | 0 => [.pbB0, .psh0, .pel0_0, .ptc0_0, .pbC0, .pel0_1, .ptc0_1, .lbB0, .pbD0, .pel0_2,
      .ptc0_2, .pbE0, .pel0_3, .ptc0_3]
  | 1 => [.pbD0, .pel0_2, .ptc0_2, .pbE0, .pel0_3, .ptc0_3]
  | 2 => [.pbB1, .psh1, .pel1_0, .ptc1_0, .pbC1, .pel1_1, .ptc1_1, .lbB1, .pbD1, .pel1_2,
      .ptc1_2, .pbE1, .pel1_3, .ptc1_3]
  | 3 => [.pbD1, .pel1_2, .ptc1_2, .pbE1, .pel1_3, .ptc1_3]
  | 4 => [.pbB2, .psh2, .pel2_0, .ptc2_0, .pbC2, .pel2_1, .ptc2_1, .lbB2, .pbD2, .pel2_2,
      .ptc2_2, .pbE2, .pel2_3, .ptc2_3]
  | 5 => [.pbD2, .pel2_2, .ptc2_2, .pbE2, .pel2_3, .ptc2_3]
  | _ => []

/-- A step from a site that is not a block-table load keeps the six words. -/
theorem btW_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hs : s ∉ lbSites) (k : Nat) :
    btW d'.dt k = btW dt k := by
  cases s <;> first
    | exact absurd (by decide) hs
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h; simp_all [btW, elDt, qUpd]))

/-- The first site of the query loads is none of the block sites. -/
theorem qSite_not_lbAfter {L : Launch} {g : Nat} (dt : Dat) (G k : Nat) :
    qSite L g dt G ∉ lbAfter k := by
  have h : ∀ G, qSite L g dt G = .ldq0 ∨ qSite L g dt G = .ldq16 ∨ qSite L g dt G = .ldq32 ∨
      qSite L g dt G = .ldq48 ∨ qSite L g dt G = .stq0_0 := by
    intro G
    unfold qSite
    split <;> (repeat' split) <;> simp
  rcases h G with h | h | h | h | h <;> rw [h] <;> (match k with
    | 0 | 1 | 2 | 3 | 4 | 5 => decide
    | k + 6 => simp [lbAfter])

/-- **A step into a site after the load of word `k` is from a site after it, or from the load.** -/
theorem lbAfter_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) :
    ∀ k < 6, d'.site ∈ lbAfter k → s ∈ lbAfter k ∨ s = lbSite k := by
  cases s <;> first
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h
            dsimp only
            first
              | decide
              | (intro k _ hm; exact absurd hm (qSite_not_lbAfter _ _ _))))

/-! ### The step at a block-table load -/

/-- **The step at the load of word `k`**: the loaded word is word `k`, the others are kept, and the
machine moves to a site after the load. -/
theorem next_lb {L : Launch} {g : Nat} {k : Nat} (hk : k < 6) {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨lbSite k, dt⟩ e = some (some d')) :
    ∃ a bs v x, e.kind = .rd a bs ∧ rebuild 3 bs = .ok v ∧ word32 v = some x ∧
      btW d'.dt k = x ∧ d'.site ∈ lbAfter k ∧ ∀ j < 6, j ≠ k → btW d'.dt j = btW dt j := by
  interval_cases k
  all_goals
    simp only [lbSite, lbSites, List.getD_cons_zero, List.getD_cons_succ] at h
    simp only [next] at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq] at h; subst h
         refine ⟨_, _, _, _, ‹_›, ‹_›, ‹_›, rfl, by dsimp only; decide, ?_⟩
         intro j hj hne
         interval_cases j <;> first | rfl | exact absurd rfl hne)

/-! ### The blocks that exist -/

/-- **The gate of a state**: a block's sites are entered only where the block is preloaded, that
is, where the number `%r31` of blocks is not 0 (block 0), neither 0 nor 1 (block 1), and not
below 3 (block 2). -/
def Gate (L : Launch) (g : Nat) (s : Site) (dt : Dat) : Prop :=
  (s ∈ blkSites 0 → v_p53 L g dt = true) ∧
  (s ∈ blkSites 1 → v_p53 L g dt = true ∧ v_p63 L g dt = false) ∧
  (s ∈ blkSites 2 → v_p53 L g dt = true ∧ v_p63 L g dt = false ∧ v_p72 L g dt = false)

section gp
variable (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) (x : Nat)

theorem gp_elDt : v_p53 L g (elDt dt a b) = v_p53 L g dt ∧ v_p63 L g (elDt dt a b) = v_p63 L g dt ∧
    v_p72 L g (elDt dt a b) = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b0 : v_p53 L g { dt with b0 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b0 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b0 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b1 : v_p53 L g { dt with b1 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b1 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b1 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b2 : v_p53 L g { dt with b2 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b2 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b2 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b3 : v_p53 L g { dt with b3 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b3 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b3 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b4 : v_p53 L g { dt with b4 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b4 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b4 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_b5 : v_p53 L g { dt with b5 := x } = v_p53 L g dt ∧
    v_p63 L g { dt with b5 := x } = v_p63 L g dt ∧
    v_p72 L g { dt with b5 := x } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_q (k : Nat) (v : Value) : v_p53 L g (qUpd dt k v) = v_p53 L g dt ∧
    v_p63 L g (qUpd dt k v) = v_p63 L g dt ∧ v_p72 L g (qUpd dt k v) = v_p72 L g dt :=
  ⟨rfl, rfl, rfl⟩
theorem gp_sh0 (v : Value) : v_p53 L g { dt with sh0 := v } = v_p53 L g dt ∧
    v_p63 L g { dt with sh0 := v } = v_p63 L g dt ∧
    v_p72 L g { dt with sh0 := v } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_sh1 (v : Value) : v_p53 L g { dt with sh1 := v } = v_p53 L g dt ∧
    v_p63 L g { dt with sh1 := v } = v_p63 L g dt ∧
    v_p72 L g { dt with sh1 := v } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
theorem gp_sh2 (v : Value) : v_p53 L g { dt with sh2 := v } = v_p53 L g dt ∧
    v_p63 L g { dt with sh2 := v } = v_p63 L g dt ∧
    v_p72 L g { dt with sh2 := v } = v_p72 L g dt := ⟨rfl, rfl, rfl⟩
end gp

/-- The three predicates, as one value. -/
def gp (L : Launch) (g : Nat) (dt : Dat) : Bool × Bool × Bool :=
  (v_p53 L g dt, v_p63 L g dt, v_p72 L g dt)

/-- **The three predicates are kept by every step from a site after the loads.** -/
theorem gp_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hk : s.afterSk = true) :
    gp L g d'.dt = gp L g dt := by
  cases s <;> first
    | exact absurd hk (by decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h
            simp only [gp, gp_elDt, gp_b0, gp_b1, gp_b2, gp_b3, gp_b4, gp_b5, gp_q, gp_sh0,
              gp_sh1, gp_sh2]))

/-- The first site of the query loads is none of the sites of a block. -/
theorem qSite_not_blk {L : Launch} {g : Nat} (dt : Dat) (G j : Nat) :
    qSite L g dt G ∉ blkSites j := by
  have h : ∀ G, qSite L g dt G = .ldq0 ∨ qSite L g dt G = .ldq16 ∨ qSite L g dt G = .ldq32 ∨
      qSite L g dt G = .ldq48 ∨ qSite L g dt G = .stq0_0 := by
    intro G
    unfold qSite
    split <;> (repeat' split) <;> simp
  rcases h G with h | h | h | h | h <;> rw [h] <;> (match j with
    | 0 | 1 | 2 => decide
    | j + 3 => simp [blkSites])

/-- The sites through which a block is entered from outside. -/
def entrySites : Nat → List Site
  | 0 => [.bar2]
  | 1 => [.pel0_3, .ptc0_3]
  | 2 => [.pel1_3, .ptc1_3]
  | _ => []

/-- **A step into a block's site is from the block or from its entry.** -/
theorem blk_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) :
    ∀ j < 3, d'.site ∈ blkSites j → s ∈ blkSites j ∨ s ∈ entrySites j := by
  cases s <;> first
    | (simp only [next] at h
       repeat' split at h
       all_goals first
         | (cases h; done)
         | (simp only [Option.some.injEq] at h; subst h
            dsimp only
            first
              | decide
              | (intro j _ hm; exact absurd hm (qSite_not_blk _ _ _))))

set_option hygiene false in
/-- Tactic for the leaves of the entry lemmas. -/
macro "entry_leaf" : tactic =>
  `(tactic| (first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h; subst h; dsimp only at hm ⊢
       first
         | (exfalso; revert hm; decide)
         | exact absurd hm (qSite_not_blk _ _ _)
         | simp_all [gp_elDt])))

theorem entry_bar2 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.bar2, dt⟩ e = some (some d')) (hm : d'.site ∈ blkSites 0) :
    v_p53 L g dt = true := by
  simp only [next] at h
  repeat' split at h
  all_goals entry_leaf

theorem entry_pel0_3 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.pel0_3, dt⟩ e = some (some d')) (hm : d'.site ∈ blkSites 1) :
    v_p63 L g dt = false := by
  simp only [next] at h
  repeat' split at h
  all_goals entry_leaf

theorem entry_ptc0_3 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.ptc0_3, dt⟩ e = some (some d')) (hm : d'.site ∈ blkSites 1) :
    v_p63 L g dt = false := by
  simp only [next] at h
  repeat' split at h
  all_goals entry_leaf

theorem entry_pel1_3 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.pel1_3, dt⟩ e = some (some d')) (hm : d'.site ∈ blkSites 2) :
    v_p72 L g dt = false := by
  simp only [next] at h
  repeat' split at h
  all_goals entry_leaf

theorem entry_ptc1_3 {L : Launch} {g : Nat} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨.ptc1_3, dt⟩ e = some (some d')) (hm : d'.site ∈ blkSites 2) :
    v_p72 L g dt = false := by
  simp only [next] at h
  repeat' split at h
  all_goals entry_leaf

/-- **A step from a site after the loads keeps the gate.** -/
theorem gate_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hI : Gate L g s dt) (hk : s.afterSk = true) :
    Gate L g d'.site d'.dt := by
  have hp := gp_next h hk
  simp only [gp, Prod.mk.injEq] at hp
  obtain ⟨p1, p2, p3⟩ := hp
  have hb := blk_next h
  obtain ⟨g0, g1, g2⟩ := hI
  refine ⟨fun hm => ?_, fun hm => ?_, fun hm => ?_⟩
  · rw [p1]
    rcases hb 0 (by omega) hm with h0 | h0
    · exact g0 h0
    · simp only [entrySites, List.mem_singleton] at h0
      subst h0
      exact entry_bar2 h hm
  · rw [p1, p2]
    rcases hb 1 (by omega) hm with h0 | h0
    · exact g1 h0
    · simp only [entrySites, List.mem_cons, List.not_mem_nil, or_false] at h0
      rcases h0 with rfl | rfl
      · have := g0 (by decide)
        exact ⟨this, entry_pel0_3 h hm⟩
      · have := g0 (by decide)
        exact ⟨this, entry_ptc0_3 h hm⟩
  · rw [p1, p2, p3]
    rcases hb 2 (by omega) hm with h0 | h0
    · exact g2 h0
    · simp only [entrySites, List.mem_cons, List.not_mem_nil, or_false] at h0
      rcases h0 with rfl | rfl
      · have := g1 (by decide)
        exact ⟨this.1, this.2, entry_pel1_3 h hm⟩
      · have := g1 (by decide)
        exact ⟨this.1, this.2, entry_ptc1_3 h hm⟩

theorem nfI (k : Nat) : BitVec.ofInt 64 (k : Int) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega
theorem pNe0 (m : Nat) (hm : m < 2 ^ 31) :
    pNeB32 (BitVec.ofNat 64 m) (BitVec.ofInt 64 0) = decide (m ≠ 0) := by
  have l0 : BitVec.ofInt 64 0 = BitVec.ofNat 64 0 := nfI 0
  simp only [pNeB32, l0, PTX.compare, truncBits_ofNat _ _ (by omega : 32 ≤ 64), Option.getD_some,
    BitVec.toNat_ofNat]
  have h1 : m % 2 ^ 32 % 2 ^ 64 = m := by omega
  have h2 : 0 % 2 ^ 32 % 2 ^ 64 = 0 := by omega
  rw [h1, h2, decide_eq_decide]
  omega
theorem pEq1 (m : Nat) (hm : m < 2 ^ 31) :
    pEqB32 (BitVec.ofNat 64 m) (BitVec.ofInt 64 1) = decide (m = 1) := by
  have l0 : BitVec.ofInt 64 1 = BitVec.ofNat 64 1 := nfI 1
  simp only [pEqB32, l0, PTX.compare, truncBits_ofNat _ _ (by omega : 32 ≤ 64), Option.getD_some,
    BitVec.toNat_ofNat]
  have h1 : m % 2 ^ 32 % 2 ^ 64 = m := by omega
  have h2 : 1 % 2 ^ 32 % 2 ^ 64 = 1 := by omega
  rw [h1, h2, decide_eq_decide]
  omega
theorem pLt3 (m : Nat) (hm : m < 2 ^ 31) :
    pLtU32 (BitVec.ofNat 64 m) (BitVec.ofInt 64 3) = decide (m < 3) := by
  have l0 : BitVec.ofInt 64 3 = BitVec.ofNat 64 3 := nfI 3
  simp only [pLtU32, l0, PTX.compare, truncBits_ofNat _ _ (by omega : 32 ≤ 64), Option.getD_some,
    BitVec.toNat_ofNat]
  have h1 : m % 2 ^ 32 % 2 ^ 64 = m := by omega
  have h2 : 3 % 2 ^ 32 % 2 ^ 64 = 3 := by omega
  rw [h1, h2, decide_eq_decide]
  omega

/-! ### The blocks that are preloaded exist -/

/-- **A gate that is passed means the block exists**: the predicates `v_p53`, `v_p63`, `v_p72` of
`Gate` say that the number of blocks to preload is above 0, 1, 2, and it is at most
`num_iters`. -/
theorem gate_iters {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) {dt : Dat} (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    (v_p53 L g dt = true → 0 < P.numIters (cta L g .z) (cta L g .x)) ∧
    (v_p53 L g dt = true → v_p63 L g dt = false → 1 < P.numIters (cta L g .z) (cta L g .x)) ∧
    (v_p53 L g dt = true → v_p63 L g dt = false → v_p72 L g dt = false →
      2 < P.numIters (cta L g .z) (cta L g .x)) := by
  have hw := wordsOk_of_pre hpre hg ha hs hm
  have hx := (cta_lt hpre hg).1
  have h31 := v_r31_val L g dt ha hw
  have hit := itersN_eq hs hx hm
  have hl1 := itersN_lt L g dt ha hw
  have hl2 := oldN_lt L g dt ha hw
  have hmin : min (oldN L g dt) (itersN L g dt) < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) hl1
  have hle : min (oldN L g dt) (itersN L g dt) ≤ P.numIters (cta L g .z) (cta L g .x) := by
    rw [← hit]; exact Nat.min_le_right _ _
  simp only [v_p53, v_p63, v_p72, h31, pNe0 _ hmin, pEq1 _ hmin, pLt3 _ hmin]
  refine ⟨fun h => ?_, fun h h' => ?_, fun h h' h'' => ?_⟩
  · simp only [decide_eq_true_eq] at h
    omega
  · simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h h'
    omega
  · simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h h' h''
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
