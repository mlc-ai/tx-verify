-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ref
public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefCount
public import Lemmas.Flow.Arith32WordW

@[expose] public section

/-! # The MMA warp's reference invariant across one step: the tools

`RefCore` at a prologue site and at a loop site (`core_pro`, `core_loop`); the objects of the
event table as the launch's objects (`qTma_eq`, `ready_eq`, …); the counts after a step from a
prologue or loop place (`pro_bump`, `loop_bump`), and an event of a state with a successor is at a
pc of the role (`inRole_of_next`). -/

/-! # The MMA warp's block words

The block count of a total of at least 64 (`rounds_pos`) and the words of the block loop's
entry (`entry_words`) and end (`end_words`): the block counter, phase, parity word and negative
counter of block `r + 1` are the end's terms on block `r`'s, and the loop goes on exactly when
`r + 1` is below the block count. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- A 32-bit word whose signed value is at least 64 is a word below `2 ^ 31`. -/
theorem r27_range {x : BitVec 64} (hx : x.toNat < 2 ^ 32) (h : scmpi .lt .s x 64 = false) :
    64 ≤ x.toNat ∧ x.toNat < 2 ^ 31 := by
  simp only [scmpi, PTX.compare, r32, truncBits, i32, toSigned, BitVec.toNat_ofNat,
    BitVec.toNat_ofInt, decide_eq_false_iff_not] at h
  split_ifs at h <;> omega

theorem W_toNat {x : BitVec 64} : W x.toNat = x := by simp [W]

/-- **The block count**: a total of at least 64 gives between 1 and `2 ^ 25` blocks, and the
negative counter's first word. -/
theorem rounds_pos {l0 l1 : BitVec 64} (h : scmpi .lt .s (r27 l0 l1) 64 = false) :
    1 ≤ rounds l0 l1 ∧ rounds l0 l1 < 2 ^ 26 ∧
      neg32 (nblk l0 l1) = W ((2 ^ 32 - rounds l0 l1) % 2 ^ 32) := by
  have hx : (r27 l0 l1).toNat < 2 ^ 32 := by
    simp only [r27, add32, truncBits, BitVec.toNat_ofNat]; omega
  obtain ⟨h1, h2⟩ := r27_range hx h
  have hw : r27 l0 l1 = W (r27 l0 l1).toNat := W_toNat.symm
  have hn : nblk l0 l1 = W ((r27 l0 l1).toNat / 64) := by
    unfold nblk
    rw [hw]
    w32_norm
  simp only [rounds, h, Bool.false_eq_true, ↓reduceIte, hn]
  rw [toNat_W (by omega)]
  refine ⟨by omega, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [neg32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_neg]
  omega

/-- The phase and parity words after a block, on the words of `0` and `1`. -/
theorem phase_next (h q : Nat) (hh : h < 2) (hq : q < 2) :
    andi (not32 (W h)) 1 = W (1 - h) ∧
      sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 (W q) 255))
        (truncBits 16 (andi16 (truncBits 16 (r32 (W h))) 255))) (i16 1) (i16 0) =
        W (if q = h then 0 else 1) := by
  interval_cases h <;> interval_cases q <;> decide

/-- **The words after block `r`**: those of block `r + 1`, and the loop goes on exactly when
`r + 1` is below the block count `R`. -/
theorem end_words {r R : Nat} (hr : r < R) (hR : R < 2 ^ 26) :
    addi (W r) 1 = W (r + 1) ∧ andi (not32 (W (r % 2))) 1 = W ((r + 1) % 2) ∧
      sel (PTX.compare .ne .b 16 (truncBits 16 (andi16 (W (r / 2 % 2)) 255))
        (truncBits 16 (andi16 (truncBits 16 (r32 (W (r % 2)))) 255))) (i16 1) (i16 0) =
        W ((r + 1) / 2 % 2) ∧
      addi (W ((2 ^ 32 - R + r) % 2 ^ 32)) 1 = W ((2 ^ 32 - R + (r + 1)) % 2 ^ 32) ∧
      scmpi .ne .b (addi (W ((2 ^ 32 - R + r) % 2 ^ 32)) 1) 0 = decide (r + 1 ≠ R) := by
  obtain ⟨hp1, hp2⟩ := phase_next (r % 2) (r / 2 % 2) (by omega) (by omega)
  have ha : addi (W ((2 ^ 32 - R + r) % 2 ^ 32)) 1 = W ((2 ^ 32 - R + (r + 1)) % 2 ^ 32) := by
    rw [addi_Wm (by omega) (by omega)]
    congr 1
    simp only [Int.toNat_one]
    omega
  refine ⟨?_, ?_, ?_, ha, ?_⟩
  · rw [show ((1 : Int)) = ((1 : Nat) : Int) from rfl, addi_W (by omega) (by omega)]
  · rw [hp1]; congr 1; omega
  · rw [hp2]; congr 1
    have h4 := Nat.mod_lt r (show 4 > 0 by omega)
    have h5 := Nat.div_add_mod r 4
    split_ifs <;> interval_cases hr4 : r % 4 <;> omega
  · rw [ha, scmpi_ne_b_W (by omega) (by omega) (by omega)]
    simp only [Int.toNat_zero, decide_eq_decide]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- A prologue site: neither in the loop nor the barrier or the exit. -/
def ProSite (s : Site) : Prop := s.inLoop = false ∧ s ≠ .exit ∧ s ≠ .outBar

theorem core_pro {d : D} {n : Cnt → Nat} (h : ProSite d.site) :
    RefCore L g d n ↔ ∀ c, c ≠ .ub → n c = cntAt (objs L g) d.site.pro 0 0 false c := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold RefCore
  split
  · contradiction
  · contradiction
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]

theorem core_loop {d : D} {n : Cnt → Nat} (h : d.site.inLoop = true) :
    RefCore L g d n ↔
      LoopOk d ∧ ∀ c, c ≠ .ub → n c = cntAt (objs L g) 31 d.cnt.toNat d.site.idx false c := by
  unfold RefCore
  split
  · rename_i hs; rw [hs] at h; cases h
  · rename_i hs; rw [hs] at h; cases h
  · simp only [h, ↓reduceIte]

/-! ### The objects -/

theorem qTma_eq : (objs L g).qTma = smLoc L g (qTmaW L) 0 := by unfold objs qTmaL; rfl
theorem qUt_eq : (objs L g).qUt = smLoc L g (qUtccpW L) 0 := by unfold objs qUtL; rfl
theorem ready_eq (b : Nat) : (objs L g).ready b = smLoc L g (readyW L (W b)) 0 := by
  unfold objs readyL; rfl
theorem qk_eq (b : Nat) : (objs L g).qk b = smLoc L g (qkW L (W b)) 0 := by unfold objs qkL; rfl
theorem so_eq (b : Nat) : (objs L g).so b = smLoc L g (soW L (W b)) 0 := by unfold objs soL; rfl
theorem sv_eq (b : Nat) : (objs L g).sv b = smLoc L g (svW L (W b)) 0 := by unfold objs svL; rfl

/-! ### The counts after a step -/

theorem pro_bump {d : D} {n B : Cnt → Nat} {e : Event} {X : Option Cnt} (hpc : inRole e = true)
    (hk : kindOf e = X) (hd : ProSite d.site) (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) d.site.pro 0 0 false) X c = B c) :
    ∀ c, c ≠ .ub → Code.bump cls n e c = B c :=
  core_bump hpc ((core_pro hd).1 hJ) fun c _ => hk ▸ hc c

theorem loop_bump {d : D} {n B : Cnt → Nat} {e : Event} {X : Option Cnt} (hpc : inRole e = true)
    (hk : kindOf e = X) (hd : d.site.inLoop = true) (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) 31 d.cnt.toNat d.site.idx false) X c = B c) :
    LoopOk d ∧ ∀ c, c ≠ .ub → Code.bump cls n e c = B c :=
  ⟨((core_loop hd).1 hJ).1, core_bump hpc ((core_loop hd).1 hJ).2 fun c _ => hk ▸ hc c⟩

/-- A prologue step to a prologue site. -/
theorem pro_next {d d' : D} {n : Cnt → Nat} {e : Event} {X : Option Cnt}
    (hpc : inRole e = true) (hk : kindOf e = X) (hd : ProSite d.site) (hd' : ProSite d'.site)
    (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) d.site.pro 0 0 false) X c =
      cntAt (objs L g) d'.site.pro 0 0 false c) :
    RefCore L g d' (Code.bump cls n e) :=
  (core_pro hd').2 (pro_bump hpc hk hd hJ hc)

/-- A step inside a block, keeping the loop registers. -/
theorem loop_next {d d' : D} {n : Cnt → Nat} {e : Event} {X : Option Cnt}
    (hpc : inRole e = true) (hk : kindOf e = X) (hd : d.site.inLoop = true)
    (hd' : d'.site.inLoop = true) (hw : LoopOk d → LoopOk d') (hcnt : d'.cnt = d.cnt)
    (hJ : RefCore L g d n)
    (hc : ∀ c, plus (cntAt (objs L g) 31 d.cnt.toNat d.site.idx false) X c =
      cntAt (objs L g) 31 d.cnt.toNat d'.site.idx false c) :
    RefCore L g d' (Code.bump cls n e) := by
  obtain ⟨hL, hb⟩ := loop_bump hpc hk hd hJ hc
  refine (core_loop hd').2 ⟨hw hL, ?_⟩
  rw [hcnt]
  exact hb

/-- The class of a successful poll, and a failed poll in none. -/
theorem kindOf_wait {e : Event} {l : Loc} {q : Nat} {ok : Bool} {sc : MbarScope}
    (h : e.kind = .wait l q ok true sc) : kindOf e = if ok then some (.acq l) else none := by
  cases ok <;> simp [kindOf, h]

/-- The successor of a site with one. -/
theorem inRole_of_next {d d' : D} {e : Event} (hpc : e.pc = d.site.pc)
    (hn : succ P L g d e = some (some d')) : inRole e = true := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only [inRole, hpc, decide_eq_true_eq]
  cases s with
  | trap => simp [succ] at hn
  | exit => simp [succ] at hn
  | leave => simp [succ] at hn
  | qLoad k => have := k.isLt; simp only [Site.pc]; omega
  | qCopy k => have := k.isLt; simp only [Site.pc]; split_ifs <;> omega
  | qk k => have := k.isLt; simp only [Site.pc]; split_ifs <;> omega
  | pv k => have := k.isLt; simp only [Site.pc]; split_ifs <;> omega
  | _ => simp only [Site.pc]; omega

/-- A state after the election's place: the exit, or a prologue site of place `1`. -/
theorem core_one {d : D} {m : Cnt → Nat}
    (hs : d.site = .exit ∨ ProSite d.site ∧ d.site.pro = 1)
    (hB : ∀ c, c ≠ .ub → m c = cntAt (objs L g) 1 0 0 false c) : RefCore L g d m := by
  rcases hs with hs | ⟨hs, h1⟩
  · unfold RefCore
    rw [hs]
    exact Or.inl hB
  · exact (core_pro hs).2 (h1 ▸ hB)

/-- A length load's successor is the transition at the word it read. -/
theorem ncWord_some {e : Event} {f : BitVec 64 → D} {d' : D} (h : ncWord e f = some (some d')) :
    ∃ x, d' = f x := by
  unfold ncWord at h
  split at h
  · split at h
    · split at h
      · exact ⟨_, (Option.some.inj (Option.some.inj h)).symm⟩
      · cases h
    · cases h
  · cases h

/-- A poll's successor. -/
theorem poll_some {d d' : D} {e : Event} {s : Site} {l : Loc} {q : Nat} {ok : Bool}
    {sc : MbarScope} (hk : e.kind = .wait l q ok true sc) (h : poll d e s = some (some d')) :
    d' = if ok then { d with site := s } else d := by
  simp only [poll, hk, Option.some.injEq] at h
  exact h.symm

/-- A poll at a prologue site. -/
theorem pro_poll {d d' : D} {n : Cnt → Nat} {e : Event} {s : Site} {l : Loc} {q : Nat}
    {ok : Bool} {sc : MbarScope} (hpc : inRole e = true) (hk : e.kind = .wait l q ok true sc)
    (hd : ProSite d.site) (hs : ProSite s) (hJ : RefCore L g d n)
    (hn : poll d e s = some (some d'))
    (hc : ∀ c, plus (cntAt (objs L g) d.site.pro 0 0 false) (some (.acq l)) c =
      cntAt (objs L g) s.pro 0 0 false c) :
    RefCore L g d' (Code.bump cls n e) := by
  rw [poll_some hk hn]
  have hK := kindOf_wait hk
  cases ok
  · exact pro_next hpc hK hd hd hJ fun c => by simp [plus_none]
  · exact pro_next (d' := { d with site := s }) hpc hK hd hs hJ hc

/-- A poll at a loop site, to a loop site. -/
theorem loop_poll {d d' : D} {n : Cnt → Nat} {e : Event} {s : Site} {l : Loc} {q : Nat}
    {ok : Bool} {sc : MbarScope} (hpc : inRole e = true) (hk : e.kind = .wait l q ok true sc)
    (hd : d.site.inLoop = true) (hs : s.inLoop = true) (hJ : RefCore L g d n)
    (hn : poll d e s = some (some d'))
    (hc : ∀ c, plus (cntAt (objs L g) 31 d.cnt.toNat d.site.idx false) (some (.acq l)) c =
      cntAt (objs L g) 31 d.cnt.toNat s.idx false c) :
    RefCore L g d' (Code.bump cls n e) := by
  rw [poll_some hk hn]
  have hK := kindOf_wait hk
  cases ok
  · exact loop_next hpc hK hd hd id rfl hJ fun c => by simp [plus_none]
  · exact loop_next (d' := { d with site := s }) hpc hK hd hs id rfl hJ hc

/-- The value of `k + 1` in `Fin (n + 2)` below the last. -/
theorem fin_succ {n : Nat} (k : Fin (n + 2)) (h : k.val ≠ n + 1) : (k + 1).val = k.val + 1 := by
  have := k.isLt
  rw [Fin.val_add, Fin.val_one]
  exact Nat.mod_eq_of_lt (by omega)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
