-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassBt

@[expose] public section

/-!
# The prologue's shuffles, counted by site

The prologue has three shuffles, one in each preloaded block (`psh0`, `psh1`, `psh2`). Block `j`
is entered only when the number `%r31` of blocks to preload is above `j` (`Gate`), and the sites
after the blocks are reached with `npOf` blocks passed: 0, 1, 2 or 3, as the three guards
`v_p53`, `v_p63`, `v_p72` say.

* `proW`: the number of the prologue's shuffles before a state: at a site of the block region
  (up to `ptc2_3`) the number of `psh` sites before it (`pshB`), after it `npOf` of the data;
* `proW_next`: a step adds one exactly at a `psh` site (`proShfl`), given the gate.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- The site is in the region of the blocks (up to the last copy of block 2). -/
def inBlk (s : Site) : Bool := decide (s.ctorIdx ≤ Site.ptc2_3.ctorIdx)

/-- The number of `psh` sites before a site of the block region. -/
def pshB (s : Site) : Nat :=
  (if Site.psh0.ctorIdx < s.ctorIdx then 1 else 0) +
    (if Site.psh1.ctorIdx < s.ctorIdx then 1 else 0) +
      (if Site.psh2.ctorIdx < s.ctorIdx then 1 else 0)

/-- The number of blocks the prologue preloads, from the three guards. -/
def npOf (L : Launch) (g : Nat) (dt : Dat) : Nat :=
  if v_p53 L g dt then (if v_p63 L g dt then 1 else if v_p72 L g dt then 2 else 3) else 0

/-- The site's instruction is a shuffle. -/
def proShfl (s : Site) : Bool := decide (s = .psh0) || decide (s = .psh1) || decide (s = .psh2)

/-- **The prologue's shuffles before a state.** -/
def proW (L : Launch) (g : Nat) (d : D) : Nat :=
  if inBlk d.site then pshB d.site else npOf L g d.dt

theorem proW_lit {L : Launch} {g : Nat} {s : Site} (dt : Dat) (h : inBlk s = true) :
    proW L g ⟨s, dt⟩ = pshB s := by
  simp [proW, h]

theorem proW_q {L : Launch} {g : Nat} {s : Site} (dt : Dat) (h : inBlk s = false) :
    proW L g ⟨s, dt⟩ = npOf L g dt := by
  simp [proW, h]

theorem inBlk_qSite (L : Launch) (g : Nat) (dt : Dat) (n : Nat) :
    inBlk (qSite L g dt n) = false := by
  unfold qSite
  split <;> (repeat' split) <;> decide

theorem p53_el (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) :
    v_p53 L g (elDt dt a b) = v_p53 L g dt := rfl

theorem p63_el (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) :
    v_p63 L g (elDt dt a b) = v_p63 L g dt := rfl

theorem p72_el (L : Launch) (g : Nat) (dt : Dat) (a : Nat) (b : Bool) :
    v_p72 L g (elDt dt a b) = v_p72 L g dt := rfl

set_option hygiene false in
/-- The leaves of `proW_next`. -/
macro "cnt_leaf" : tactic =>
  `(tactic| (first
    | (cases h; done)
    | (simp only [Option.some.injEq] at h
       subst h
       first
         | rfl
         | (split <;>
            first
              | rfl
              | (simp only [proW, inBlk_qSite, Bool.false_eq_true, ite_false]
                 simp (config := { decide := true }) only [inBlk, pshB, proShfl, ite_true,
                   ite_false, Nat.add_zero, Nat.zero_add]
                 simp only [npOf]
                 simp_all (config := { decide := true }) [Gate, blkSites, p53_el, p63_el,
                   p72_el])))))

/-- Every successor of the prologue is a later site (as `Bound.ProA.next_lt`). -/
theorem next_ctor_lt {L : Launch} {g : Nat} {d d' : D} {e : Event}
    (h : next L g d e = some (some d')) : d.site.ctorIdx < d'.site.ctorIdx := by
  obtain ⟨s, dt⟩ := d
  cases s <;> simp only [next] at h <;> (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [Option.some.injEq] at h; subst h; (try simp only [qSite])
       (repeat' split) <;> decide)

theorem proShfl_blk (s : Site) (h : proShfl s = true) : inBlk s = true := by
  cases s <;> first | rfl | (exfalso; revert h; decide)

/-- **A step in the block region.** -/
theorem proW_next_blk {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hG : Gate L g s dt) (hb : inBlk s = true) :
    proW L g d' = proW L g ⟨s, dt⟩ + (if proShfl s then 1 else 0) := by
  cases s <;> first
    | (exfalso; revert hb; decide)
    | (simp only [next] at h
       repeat' split at h
       all_goals cnt_leaf)

/-- **A step after the block region** keeps the count: the guards are kept. -/
theorem proW_next_q {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hb : inBlk s = false) :
    proW L g d' = proW L g ⟨s, dt⟩ + (if proShfl s then 1 else 0) := by
  have hs : proShfl s = false := by
    cases hp : proShfl s
    · rfl
    · rw [proShfl_blk s hp] at hb; cases hb
  have hlt := next_ctor_lt h
  have hk : s.afterSk = true := by
    cases s <;> first | rfl | (exfalso; revert hb; decide)
  have hb' : inBlk d'.site = false := by
    simp only [inBlk, decide_eq_false_iff_not, Nat.not_le] at hb ⊢
    simp only at hlt
    omega
  have hp := gp_next h hk
  simp only [gp, Prod.mk.injEq] at hp
  obtain ⟨site', dt'⟩ := d'
  rw [proW_q _ hb, proW_q _ hb', hs]
  simp only [npOf, hp.1, hp.2.1, hp.2.2, Bool.false_eq_true, ite_false, Nat.add_zero]

/-- **A prologue step adds one shuffle exactly at a `psh` site.** -/
theorem proW_next {L : Launch} {g : Nat} {s : Site} {dt : Dat} {d' : D} {e : Event}
    (h : next L g ⟨s, dt⟩ e = some (some d')) (hG : Gate L g s dt) :
    proW L g d' = proW L g ⟨s, dt⟩ + (if proShfl s then 1 else 0) := by
  cases hb : inBlk s
  · exact proW_next_q h hb
  · exact proW_next_blk h hG hb

/-- **The number of blocks the guards say is `num_pre`**, for the request's words. -/
theorem npOf_eq {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) {g : Nat}
    (hg : g < L.threads) {dt : Dat} (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    npOf L g dt = numPre P (cta L g .z) (cta L g .x) := by
  have hw := wordsOk_of_pre hpre hg ha hs hm
  have hx := (cta_lt hpre hg).1
  have h31 := v_r31_val L g dt ha hw
  have hl1 := itersN_lt L g dt ha hw
  have hl2 := oldN_lt L g dt ha hw
  have hmin : min (oldN L g dt) (itersN L g dt) < 2 ^ 31 :=
    lt_of_le_of_lt (Nat.min_le_right _ _) hl1
  have e1 := itersN_eq hs hx hm
  have e2 := oldN_eq hs hx hm
  simp only [npOf, v_p53, v_p63, v_p72, h31, pNe0 _ hmin, pEq1 _ hmin, pLt3 _ hmin]
  unfold numPre
  rw [← e1, ← e2]
  generalize min (oldN L g dt) (itersN L g dt) = m
  by_cases h0 : m = 0
  · simp [h0]
  by_cases h1 : m = 1
  · simp [h1]
  by_cases h2 : m < 3
  · have : m = 2 := by omega
    simp [this]
  · simp [h0, h1, h2]
    omega

/-- **A block's site under the gate**: the block is below the number of blocks. -/
theorem lt_npOf {L : Launch} {g : Nat} {s : Site} {dt : Dat} (hG : Gate L g s dt) {j : Nat}
    (hj : s ∈ blkSites j) : j < npOf L g dt := by
  obtain ⟨g0, g1, g2⟩ := hG
  match j, hj with
  | 0, hj => simp [npOf, g0 hj]; split <;> (try split) <;> omega
  | 1, hj => obtain ⟨a, b⟩ := g1 hj; simp [npOf, a, b]; split <;> omega
  | 2, hj => obtain ⟨a, b, c⟩ := g2 hj; simp [npOf, a, b, c]
  | j + 3, hj => simp [blkSites] at hj

/-- The `psh` sites are in the block of their index. -/
theorem psh_blk (s : Site) (h : proShfl s = true) : s ∈ blkSites (pshB s) := by
  cases s <;> first | decide | (exfalso; revert h; decide)

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
