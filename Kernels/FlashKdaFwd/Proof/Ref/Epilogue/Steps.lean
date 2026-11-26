-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Arith

@[expose] public section

/-! # Epilogue phase: the invariant is kept, one lemma per shape of transition

`nxt g pos` is the position after `pos` in the sequence of the role of thread `g`. Every lemma
here says: from the reference invariant at a position (`RefAt`), the state that the generated
transition function gives is a state (the thread is not dead: the pointer runs of the stores
continue), and it satisfies the reference invariant at `nxt g pos`.

* `st_bar7`: the first barrier. A compute thread computes its base pointer (instructions 3115
  to 3127: the entry index `carryBase`, `cvta.shared.u64` of `shared_mem`, the sum) and the
  address of store 0; every other thread computes the two flags of the later branch.
* `st_next`: store `j` to store `j'= j + 1`, generic in the pointer run of the site: the
  generated lemma `r<pc>_ptr` of the thread layer (`Thread/RunPtr.lean`) gives the run's
  condition and the new address register from the base pointer; `Sites.lean` instantiates it
  for the 127 sites.
* `st_last`: the last store, to the proxy fence (the flags).
* `st_fence`, `st_bar8` (the branch: only the store leader goes on to the tensor stores, and
  computes the plane `H * seq + head` there), `ts_next` (tensor store `i` to `i + 1`, generic in
  the two registers the code between them writes), `ts_last`, `st_commit`, `st_bwait`,
  `st_bar9`.

`ord_nxt`, `onPath_nxt`, `bars_nxt`, `ord_inj`: the successor position is the next of the
role's sequence, and the ordinal names a position of the role. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### The successor position -/

/-- The position after `pos` in the sequence of the role of thread `g` (`exit` is the last). -/
def nxt (g : Nat) : Pos → Pos
  | .bar7 => if tid g < 128 then .st 0 else .fence
  | .st j => if h : j.val + 1 < 128 then .st ⟨j.val + 1, h⟩ else .fence
  | .fence => .bar8
  | .bar8 => if tid g = 160 then .ts 0 else .bar9
  | .ts i => if h : i.val + 1 < 16 then .ts ⟨i.val + 1, h⟩ else .commit
  | .commit => .bwait
  | .bwait => .bar9
  | .bar9 => .exit
  | .exit => .exit

theorem nxt_st {g : Nat} {j j' : Fin 128} (h : j'.val = j.val + 1) : nxt g (.st j) = .st j' := by
  have hlt : j.val + 1 < 128 := by have := j'.isLt; omega
  rw [nxt, dite_eq_left hlt]
  congr 1
  exact Fin.ext h.symm

theorem nxt_st_last {g : Nat} : nxt g (.st 127) = .fence := rfl

theorem nxt_ts {g : Nat} {i i' : Fin 16} (h : i'.val = i.val + 1) : nxt g (.ts i) = .ts i' := by
  have hlt : i.val + 1 < 16 := by have := i'.isLt; omega
  rw [nxt, dite_eq_left hlt]
  congr 1
  exact Fin.ext h.symm

theorem nxt_ts_last {g : Nat} : nxt g (.ts 15) = .commit := rfl

/-- Whether a position is one of the three barriers. -/
def Pos.isBar : Pos → Bool
  | .bar7 | .bar8 | .bar9 => true
  | _ => false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {site : Site}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

theorem onPath_nxt {pos : Pos} (h : OnPath g pos) : OnPath g (nxt g pos) := by
  cases pos with
  | bar7 =>
    by_cases hc : tid g < 128
    · rw [nxt, ite_eq_left hc]; exact hc
    · rw [nxt, ite_eq_right hc]; trivial
  | st j =>
    by_cases hj : j.val + 1 < 128
    · rw [nxt, dite_eq_left hj]; exact h
    · rw [nxt, dite_eq_right hj]; trivial
  | fence => trivial
  | bar8 =>
    by_cases hc : tid g = 160
    · rw [nxt, ite_eq_left hc]; exact hc
    · rw [nxt, ite_eq_right hc]; trivial
  | ts i =>
    by_cases hi : i.val + 1 < 16
    · rw [nxt, dite_eq_left hi]; exact h
    · rw [nxt, dite_eq_right hi]; exact h
  | commit => exact h
  | bwait => trivial
  | bar9 => trivial
  | exit => trivial

theorem ord_nxt {pos : Pos} (h : OnPath g pos) (he : pos ≠ .exit) :
    ord g (nxt g pos) = ord g pos + 1 := by
  cases pos with
  | bar7 =>
    by_cases hc : tid g < 128
    · rw [nxt, ite_eq_left hc]; rfl
    · rw [nxt, ite_eq_right hc]; simp only [ord, ite_eq_right hc]
  | st j =>
    have hc : tid g < 128 := h
    have hlt := j.isLt
    by_cases hj : j.val + 1 < 128
    · rw [nxt, dite_eq_left hj]
      show 1 + (j.val + 1) = 1 + j.val + 1
      omega
    · rw [nxt, dite_eq_right hj]
      simp only [ord, ite_eq_left hc]
      omega
  | fence =>
    by_cases hc : tid g < 128
    · simp only [nxt, ord, ite_eq_left hc]
    · simp only [nxt, ord, ite_eq_right hc]
  | bar8 =>
    by_cases hc : tid g = 160
    · rw [nxt, ite_eq_left hc]
      simp only [ord, ite_eq_right (show ¬ tid g < 128 by omega), Fin.val_zero]
    · rw [nxt, ite_eq_right hc]
      by_cases h1 : tid g < 128
      · simp only [ord, ite_eq_left h1]
      · simp only [ord, ite_eq_right h1, ite_eq_right hc]
  | ts i =>
    have hc : tid g = 160 := h
    have hlt := i.isLt
    by_cases hi : i.val + 1 < 16
    · rw [nxt, dite_eq_left hi]
      show 3 + (i.val + 1) = 3 + i.val + 1
      omega
    · rw [nxt, dite_eq_right hi]
      simp only [ord]
      omega
  | commit => rfl
  | bwait =>
    have hc : tid g = 160 := h
    simp only [nxt, ord, ite_eq_right (show ¬ tid g < 128 by omega), ite_eq_left hc]
  | bar9 =>
    by_cases h1 : tid g < 128
    · simp only [nxt, ord, ite_eq_left h1]
    · by_cases hc : tid g = 160
      · simp only [nxt, ord, ite_eq_right h1, ite_eq_left hc]
      · simp only [nxt, ord, ite_eq_right h1, ite_eq_right hc]
  | exit => exact absurd rfl he

theorem bars_nxt (pos : Pos) (he : pos ≠ .exit) :
    bars (nxt g pos) = bars pos + if pos.isBar then 1 else 0 := by
  cases pos with
  | bar7 =>
    by_cases hc : tid g < 128
    · rw [nxt, ite_eq_left hc]; rfl
    · rw [nxt, ite_eq_right hc]; rfl
  | st j =>
    by_cases hj : j.val + 1 < 128
    · rw [nxt, dite_eq_left hj]; rfl
    · rw [nxt, dite_eq_right hj]; rfl
  | fence => rfl
  | bar8 =>
    by_cases hc : tid g = 160
    · rw [nxt, ite_eq_left hc]; rfl
    · rw [nxt, ite_eq_right hc]; rfl
  | ts i =>
    by_cases hi : i.val + 1 < 16
    · rw [nxt, dite_eq_left hi]; rfl
    · rw [nxt, dite_eq_right hi]; rfl
  | commit => rfl
  | bwait => rfl
  | bar9 => rfl
  | exit => exact absurd rfl he

/-- The position with a given ordinal in the sequence of the role of thread `g`. -/
def posAt (g n : Nat) : Pos :=
  if tid g < 128 then
    if n = 0 then .bar7 else if h : n - 1 < 128 then .st ⟨n - 1, h⟩ else if n = 129 then .fence
    else if n = 130 then .bar8 else if n = 131 then .bar9 else .exit
  else if tid g = 160 then
    if n = 0 then .bar7 else if n = 1 then .fence else if n = 2 then .bar8
    else if h : n - 3 < 16 then .ts ⟨n - 3, h⟩ else if n = 19 then .commit
    else if n = 20 then .bwait else if n = 21 then .bar9 else .exit
  else
    if n = 0 then .bar7 else if n = 1 then .fence else if n = 2 then .bar8
    else if n = 3 then .bar9 else .exit

theorem posAt_ord {pos : Pos} (h : OnPath g pos) : posAt g (ord g pos) = pos := by
  by_cases h1 : tid g < 128
  · have h2 : tid g ≠ 160 := by omega
    cases pos with
    | st j =>
      have hlt := j.isLt
      simp only [posAt, ord, ite_eq_left h1, show ¬ 1 + j.val = 0 by omega,
        show 1 + j.val - 1 = j.val by omega, hlt, ↓reduceIte, ↓reduceDIte, Fin.eta]
    | ts i => exact absurd (show tid g = 160 from h) h2
    | commit => exact absurd (show tid g = 160 from h) h2
    | bwait => exact absurd (show tid g = 160 from h) h2
    | _ => simp [posAt, ord, h1]
  · by_cases h2 : tid g = 160
    · cases pos with
      | st j => exact absurd (show tid g < 128 from h) h1
      | ts i =>
        have hlt := i.isLt
        simp only [posAt, ord, ite_eq_right h1, ite_eq_left h2, show ¬ 3 + i.val = 0 by omega,
          show ¬ 3 + i.val = 1 by omega, show ¬ 3 + i.val = 2 by omega,
          show 3 + i.val - 3 = i.val by omega, hlt, ↓reduceIte, ↓reduceDIte, Fin.eta]
      | _ => simp [posAt, ord, h1, h2]
    · cases pos with
      | st j => exact absurd (show tid g < 128 from h) h1
      | ts i => exact absurd (show tid g = 160 from h) h2
      | commit => exact absurd (show tid g = 160 from h) h2
      | bwait => exact absurd (show tid g = 160 from h) h2
      | _ => simp [posAt, ord, h1, h2]

/-- The ordinal names a position of the role. -/
theorem ord_inj {q pos : Pos} (hq : OnPath g q) (hp : OnPath g pos)
    (h : ord g q = ord g pos) : q = pos := by
  rw [← posAt_ord hq, ← posAt_ord hp, h]

/-! ### Reads of rewritten files -/

theorem valueEx_one_self (x : Nat → Value) (r : Nat) (v : Value) :
    valueEx x [(r, v)] r = v := by
  simp [valueEx]

theorem valueEx_one_other (x : Nat → Value) {r r' : Nat} (v : Value) (h : r' ≠ r) :
    valueEx x [(r, v)] r' = x r' := by
  simp [valueEx, List.lookup, beq_eq_false_iff_ne.mpr h]

theorem setW_two_fst (w : Nat → BitVec 64) (a b : Nat) (va vb : BitVec 64) :
    setW [(a, va), (b, vb)] w a = va := by
  simp [setW]

theorem setW_two_snd (w : Nat → BitVec 64) {a b : Nat} (va vb : BitVec 64) (h : b ≠ a) :
    setW [(a, va), (b, vb)] w b = vb := by
  simp [setW, List.lookup, beq_eq_false_iff_ne.mpr h]

theorem setW_two_other (w : Nat → BitVec 64) {a b r : Nat} (va vb : BitVec 64) (ha : r ≠ a)
    (hb : r ≠ b) : setW [(a, va), (b, vb)] w r = w r := by
  simp [setW, List.lookup, beq_eq_false_iff_ne.mpr ha, beq_eq_false_iff_ne.mpr hb]

/-! ### The flags after the stores (instructions 3768 to 3773) -/

/-- The two flags that instructions 3768 to 3773 compute from `%r180` and `%r1736`. -/
theorem flags_of (h2042 : w 2042 = W (tid g))
    (h486 : 160 ≤ tid g → w 486 = W (if lane g = 0 then 1 else 0)) :
    Flags g ⟨site, w, setP [(78, scmpi .eq .b (w 486) 0),
      (81, scmpi .ne .b (sel (scmpi .lt .u (w 2042) 128) (i32 0)
        (sel (scmpi .lt .u (w 2042) 160) (i32 1) (i32 2))) 2)] p, x⟩ := by
  refine ⟨?_, fun h => ?_⟩
  · simp only [setP_apply, lookupLit, Option.getD_some, h2042]
    exact role_ne2 g
  · simp only [setP_apply, lookupLit, Option.getD_some, h486 h]
    exact elected_eq0 g

/-! ### The first barrier -/

/-- **After the first barrier**: a compute thread is at store 0 with its base pointer and the
address of the store; every other thread is at the proxy fence with the flags. -/
theorem st_bar7 (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g .bar7 ⟨.bar 7, w, p, x⟩) :
    ∃ d', after_bar_7 L g ⟨.bar 7, w, p, x⟩ = some (some d') ∧ RefAt P g (nxt g .bar7) d' := by
  obtain ⟨-, h2042, h77, h486⟩ := h
  dsimp only at h2042 h77 h486
  have ht := tid_lt g
  have hs := shared_lt hpre
  by_cases hc : tid g < 128
  · -- a compute thread: the base pointer and the address of store 0
    have h77' : p 77 = false := by rw [h77]; exact decide_eq_false (by omega)
    have hblk : g / L.block < L.grid := by
      rw [block_div hpre, hpre.grid]
      exact cta_lt hpre hg
    have hcb := carryBase_lt hc
    have hcw := carry_word ⟨tid g, ht⟩
    simp only at hcw
    -- the file after the control code 3115 to 3125
    generalize hw' : setW [(2894, mulWide .u (or32 (or32 (andi (shl (w 2042) 4) 48)
      (shru (andi (w 2042) 31) 2)) (andi (shl (w 2042) 3) 7936)) 4),
      (2895, zext (sreg L.sharedBase))] w = w'
    have e2894 : w' 2894 = W (carryBase (tid g)) := by
      rw [← hw', setW_two_fst, h2042, hcw]
    have e2895 : w' 2895 = W P.sharedBase := by
      rw [← hw', setW_two_snd _ _ _ (by decide), sharedWord hpre, zext_W (by omega)]
    have e2042 : w' 2042 = W (tid g) := by
      rw [← hw', setW_two_other _ _ _ (by decide) (by decide), h2042]
    -- the conversion at 3126
    have hcv := Rules.cvta_eval (L := L) (g := g) (V := valueOf ⟨.bar 7, w', p, x⟩) (a := 2895)
      (w := 64) (x := W P.sharedBase) (by
        show Value.bits 64 (w' 2895) = _
        rw [e2895]) hg hblk (by
        rw [Rules.truncBits_64, toNat_W (by omega)]
        omega)
    rw [Rules.truncBits_64, toNat_W (show P.sharedBase < 2 ^ 64 by omega)] at hcv
    generalize hx' : valueEx x [(2896, Rules.cvtaVal L g (valueOf ⟨.bar 7, w', p, x⟩) 2895)] = x'
    have e2896 : x' 2896 = .ptr 64 true (.shared (g / L.block) (g / L.block))
        (W P.sharedBase) := by
      rw [← hx', valueEx_one_self, hcv.2]
    -- the run 3127 to 3131
    have hmv := movedBy_W (B := P.sharedBase) (c := carryBase (tid g)) (by omega)
    have hst := ptr_step (B := P.sharedBase + carryBase (tid g)) (k := 32768) (K := 32768) rfl
      (by omega)
    have hrun := r3127_ptr (V := valueOf ⟨.bar 7, w', p, x'⟩) (o := g / L.block)
      (c := g / L.block) (off := W P.sharedBase) (delta := W (carryBase (tid g))) (n := 64) (by
        rw [valueOf_opaque (by decide)]
        exact e2896) (by
        show Value.bits 64 (w' 2894) = _
        rw [e2894]) hmv.1 (by rw [hmv.2]; exact hst.1)
    rw [hmv.2, hst.2] at hrun
    refine ⟨⟨.store 18, w', p, valueEx x' (Run.r3127_facts1 (valueOf ⟨.bar 7, w', p, x'⟩))⟩,
      ?_, ?_⟩
    · simp only [after_bar_7, h77', Bool.false_eq_true, ↓reduceIte, tail_3126, tail_3127]
      rw [hw', under_pos hcv.1, hx', across_pos hrun.1]
    · rw [nxt, ite_eq_left hc]
      refine ⟨rfl, hc, e2042, ?_, ?_⟩
      · dsimp only
        rw [hrun.2, block_div hpre]
        simp only [valueEx, lookupLit, Option.getD_some]
      · dsimp only
        rw [hrun.2, block_div hpre]
        simp only [valueEx, stPtr, Fin.val_zero, getLit, lookupLit, Option.getD_some]
        rfl
  · -- the load warp and the store warp: the flags
    have h77' : p 77 = true := by rw [h77]; exact decide_eq_true (by omega)
    refine ⟨⟨.fenceProxy 3, w, setP [(78, scmpi .eq .b (w 486) 0),
      (81, scmpi .ne .b (sel (scmpi .lt .u (w 2042) 128) (i32 0)
        (sel (scmpi .lt .u (w 2042) 160) (i32 1) (i32 2))) 2)] p, x⟩, ?_, ?_⟩
    · simp only [after_bar_7, h77', ↓reduceIte]
    · rw [nxt, ite_eq_right hc]
      exact ⟨rfl, flags_of h2042 h486⟩

/-! ### The stores -/

/-- **From store `j` to store `j' = j + 1`**, generic in the pointer run between them: `hptr`
is the thread layer's lemma `r<pc>_ptr` of the run (its condition `cond` holds and its end
facts are the new address register `r` with the swizzled pointer, when the base pointer
`%rd651` holds a generic shared pointer and the move by the constant `K` stays in the
window). -/
theorem st_next (hpre : Pre P L mem0) {j j' : Fin 128} {site' : Site} {cond : Prop}
    {facts : List (Nat × Value)} {r k : Nat} {K : Int}
    (hs' : site' = (Pos.st j').site) (er : stPtr j'.val = r) (ek : stOff j'.val = k)
    (hK : K = (k : Int))
    (hptr : ∀ off, valueOf ⟨site, w, p, x⟩ 2897 = .ptr 64 true (.shared (cta g) (cta g)) off →
      Rules.MoveOk off K → cond ∧ facts = [(r, .ptr 64 true (.shared (cta g) (cta g))
        (Rules.swz (Rules.movedOff off K)))])
    (h : RefAt P g (.st j) ⟨site, w, p, x⟩) :
    ∃ d', across cond ⟨site', w, p, valueEx x facts⟩ = some (some d') ∧
      RefAt P g (.st j') d' := by
  obtain ⟨-, ht, h2042, hbase, -⟩ := h
  dsimp only at h2042 hbase
  subst er ek
  have hlt := stBase_lt hpre ht j'
  have hst := ptr_step (B := P.sharedBase + carryBase (tid g)) (k := stOff j'.val) hK hlt
  obtain ⟨hcond, hfacts⟩ := hptr _ (by rw [valueOf_opaque (by decide)]; exact hbase) hst.1
  refine ⟨_, across_pos hcond, hs', ht, h2042, ?_, ?_⟩
  · show valueEx x facts 2897 = _
    rw [hfacts, valueEx_one_other _ _ (stPtr_ne j').symm, hbase]
  · show valueEx x facts (stPtr j'.val) = _
    rw [hfacts, valueEx_one_self, hst.2]
    rfl

/-- **After the last store**: the proxy fence, with the flags. -/
theorem st_last (h : RefAt P g (.st 127) ⟨.store 145, w, p, x⟩) :
    RefAt P g .fence (after_store_145 L g ⟨.store 145, w, p, x⟩) := by
  obtain ⟨-, ht, h2042, -, -⟩ := h
  dsimp only at h2042
  exact ⟨rfl, flags_of h2042 (fun h => by omega)⟩

/-! ### The fence and the second barrier -/

theorem st_fence (h : RefAt P g .fence ⟨.fenceProxy 3, w, p, x⟩) :
    RefAt P g .bar8 (after_fenceProxy_3 L g ⟨.fenceProxy 3, w, p, x⟩) :=
  ⟨rfl, h.pos⟩

/-- **After the second barrier**: the store leader is at the first tensor store, with the
plane `H * seq + head` and the first source address; every other thread is at the third
barrier. -/
theorem st_bar8 (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g .bar8 ⟨.bar 8, w, p, x⟩) :
    RefAt P g (nxt g .bar8) (after_bar_8 L g ⟨.bar 8, w, p, x⟩) := by
  obtain ⟨-, h81, h78⟩ := h
  dsimp only at h81 h78
  have hs := shared_lt hpre
  by_cases hl : tid g = 160
  · have h81' : p 81 = false := by rw [h81]; exact decide_eq_false (by omega)
    have h78' : p 78 = false := by
      rw [h78 (by omega)]
      exact decide_eq_false (by simp [((leader_iff g).mp hl).2])
    rw [nxt, ite_eq_left hl]
    refine ⟨?_, hl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [after_bar_8, h81', h78', Bool.or_self, Bool.false_eq_true, ↓reduceIte, tail_3778]
      rfl
    all_goals
      simp only [after_bar_8, h81', h78', Bool.or_self, Bool.false_eq_true, ↓reduceIte,
        tail_3778, setW_apply, lookupLit, Option.getD_some, Option.getD_none, tsSrc, tsCoord,
        Fin.val_zero, getLit, planeWord hpre hg, sharedWord hpre]
    · rfl
    · exact addi_W (n := 32768) (by omega) (by omega)
    · rfl
  · have hor : (p 81 || p 78) = true := by
      by_cases h160 : tid g < 160
      · rw [h81, decide_eq_true h160, Bool.true_or]
      · have hne : lane g ≠ 0 := fun h0 => hl ((leader_iff g).mpr ⟨by omega, h0⟩)
        rw [h78 (by omega), decide_eq_true hne, Bool.or_true]
    rw [nxt, ite_eq_right hl]
    refine ⟨?_, trivial⟩
    simp only [after_bar_8, hor, ↓reduceIte]
    rfl

/-! ### The tensor stores -/

/-- The registers that the code between two tensor stores writes are neither `%r1783` nor the
two shared coordinate registers, and differ. -/
theorem ts_regs : ∀ i : Fin 16, 0 < i.val → tsSrc i.val ≠ 2089 ∧ tsSrc i.val ≠ 2055 ∧
    tsSrc i.val ≠ 2056 ∧ tsCoord i.val ≠ 2089 ∧ tsCoord i.val ≠ 2055 ∧ tsCoord i.val ≠ 2056 ∧
    tsCoord i.val ≠ tsSrc i.val := by
  decide

/-- **From tensor store `i` to tensor store `i' = i + 1`**, generic in the two registers that
the code between them writes: the source address `shared_mem + off` and the coordinate `c`. -/
theorem ts_next (hpre : Pre P L mem0) {i i' : Fin 16} {site' : Site} {rs rc : Nat}
    {off c : Int} (hi : 0 < i'.val) (hs' : site' = (Pos.ts i').site)
    (ers : tsSrc i'.val = rs) (erc : tsCoord i'.val = rc)
    (hoff : off = ((32768 + 4096 * i'.val : Nat) : Int)) (hc : c = ((8 * i'.val : Nat) : Int))
    (h : RefAt P g (.ts i) ⟨site, w, p, x⟩) :
    RefAt P g (.ts i') ⟨site', setW [(rs, addi (w 2089) off), (rc, i32 c)] w, p, x⟩ := by
  obtain ⟨-, hl, h2089, h2055, h2056, -, -⟩ := h
  dsimp only at h2089 h2055 h2056
  subst ers erc hoff hc
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := ts_regs i' hi
  have hs := shared_lt hpre
  have hi' := i'.isLt
  refine ⟨hs', hl, ?_, ?_, ?_, ?_, ?_⟩
  · show setW _ w 2089 = _
    rw [setW_two_other _ _ _ n1.symm n4.symm, h2089]
  · show setW _ w 2055 = _
    rw [setW_two_other _ _ _ n2.symm n5.symm, h2055]
  · show setW _ w 2056 = _
    rw [setW_two_other _ _ _ n3.symm n6.symm, h2056]
  · show setW _ w (tsSrc i'.val) = _
    rw [setW_two_fst, h2089]
    exact addi_W (by omega) (by omega)
  · show setW _ w (tsCoord i'.val) = _
    rw [setW_two_snd _ _ _ n7]
    exact i32_W (by omega)

/-- **After the last tensor store**: the group commit. -/
theorem ts_last (h : RefAt P g (.ts 15) ⟨.tensorCopy 257, w, p, x⟩) :
    RefAt P g .commit (after_tensorCopy_257 L g ⟨.tensorCopy 257, w, p, x⟩) :=
  ⟨rfl, h.pos.1⟩

theorem st_commit (h : RefAt P g .commit ⟨.bulkCommit 1, w, p, x⟩) :
    RefAt P g .bwait (after_bulkCommit_1 L g ⟨.bulkCommit 1, w, p, x⟩) :=
  ⟨rfl, h.pos⟩

theorem st_bwait (h : RefAt P g .bwait ⟨.bulkWait 1, w, p, x⟩) :
    RefAt P g .bar9 (after_bulkWait_1 L g ⟨.bulkWait 1, w, p, x⟩) :=
  ⟨rfl, trivial⟩

theorem st_bar9 (h : RefAt P g .bar9 ⟨.bar 9, w, p, x⟩) :
    RefAt P g .exit (after_bar_9 L g ⟨.bar 9, w, p, x⟩) :=
  ⟨rfl, trivial⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
