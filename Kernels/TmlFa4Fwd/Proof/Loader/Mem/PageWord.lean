-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape

@[expose] public section

/-! # The loader's page word

The page word of a state is the word the last page-table load returned, or zero: a step keeps it,
sets it to zero, or is that load (`succ_pw`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (i32)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g w : Nat}

/-- A successor with the page word kept or zero. -/
def KeepP (d d' : D) : Prop := d'.v.pw = d.v.pw ∨ d'.v.pw = i32 0

theorem keepP_ite {c : Bool} {d a b : D} (ha : KeepP d a) (hb : KeepP d b) :
    KeepP d (D.ite c a b) := by
  cases c <;> assumption

theorem keepP_iteS {c : Bool} {d a b : D} (ha : KeepP d a) (hb : KeepP d b) :
    KeepP d (D.iteS c a b) := by
  cases c
  · exact hb
  · exact ha

theorem keepP_scanExit {d d0 : D} (h : KeepP d d0) (late : Bool) (gx cur : BitVec 64) :
    KeepP d (scanExit p late d0 gx cur) := by
  unfold scanExit
  apply keepP_ite <;> cases late <;> exact h

theorem keepP_loopHead {d d0 : D} (h : KeepP d d0) (late : Bool) (grp acc : BitVec 64) :
    KeepP d (loopHead p L g late d0 grp acc) := by
  unfold loopHead
  apply keepP_ite
  · exact keepP_scanExit h _ _ _
  · apply keepP_ite <;> exact h

theorem keepP_afterTotal (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    KeepP d (afterTotal p L g k d x) := by
  unfold afterTotal
  cases k <;> dsimp only <;> apply keepP_ite <;>
    first
      | (refine keepP_scanExit ?_ _ _ _; exact .inl rfl)
      | (refine keepP_loopHead ?_ _ _ _; exact .inl rfl)

theorem keepP_afterTiles {d d' : D} {x : BitVec 64} (h : afterTiles p L g d x = some d') :
    KeepP d d' := by
  simp only [afterTiles] at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq] at h
  subst h
  apply keepP_ite <;> exact .inl rfl

theorem keepP_passStart {d d0 : D} (h : KeepP d d0) (late : Bool) :
    KeepP d (passStart p L g late d0) := by
  unfold passStart; apply keepP_ite <;> exact h

theorem keepP_pgEnter {d d0 : D} (h : KeepP d d0) (per : Per) (it : Fin 2) :
    KeepP d (pgEnter p L g d0 per it) := by
  unfold pgEnter; apply keepP_iteS
  · exact .inr rfl
  · exact h

theorem keepP_afterTail {d d0 : D} (h : KeepP d d0) : KeepP d (afterTail p L g d0) := by
  unfold afterTail
  apply keepP_iteS
  · (refine keepP_passStart ?_ _; exact h)
  · (refine keepP_pgEnter ?_ _ _; exact h)

theorem keepP_afterWarm {d d0 : D} (h : KeepP d d0) : KeepP d (afterWarm p L g w d0) := by
  unfold afterWarm
  apply keepP_iteS
  · exact keepP_afterTail h
  · exact h

theorem keepP_afterPrime {d d0 : D} (h : KeepP d d0) : KeepP d (afterPrime p L g w d0) := by
  unfold afterPrime
  apply keepP_iteS
  · (refine keepP_afterWarm ?_; exact h)
  · (refine keepP_pgEnter ?_ _ _; exact h)

theorem keepP_warmEnd {d d0 : D} (h : KeepP d d0) : KeepP d (warmEnd p L g w d0) := by
  unfold warmEnd
  apply keepP_iteS
  · (refine keepP_pgEnter ?_ _ _; exact h)
  · (refine keepP_afterWarm ?_; exact h)

theorem keepP_steadyEnd {d d0 : D} (h : KeepP d d0) : KeepP d (steadyEnd p L g d0) := by
  unfold steadyEnd
  apply keepP_iteS
  · (refine keepP_pgEnter ?_ _ _; exact h)
  · (refine keepP_passStart ?_ _; exact h)

theorem keepP_afterArrive (d : D) (per : Per) (b : Bool) :
    KeepP d (afterArrive p L g w d per b) := by
  cases per <;> cases b <;> simp only [afterArrive]
  · apply keepP_ite <;> exact .inl rfl
  · (refine keepP_afterPrime ?_; exact .inl rfl)
  · apply keepP_ite <;> exact .inl rfl
  · (refine keepP_warmEnd ?_; exact .inl rfl)
  · exact .inl rfl
  · (refine keepP_steadyEnd ?_; exact .inl rfl)

theorem keepP_groupEnd {d d0 : D} (h : KeepP d d0) (t : Fin 7) :
    KeepP d (groupEnd p L g d0 t) := by
  fin_cases t <;> simp only [groupEnd] <;> first | exact h | exact keepP_afterTail h

theorem keepP_teNext (d : D) (t : Fin 7) (i : Fin 3) : KeepP d (teNext p L g d t i) := by
  fin_cases i <;> simp only [teNext]
  · exact .inl rfl
  · exact .inl rfl
  · split
    · (refine keepP_groupEnd ?_ _; exact .inl rfl)
    · (refine keepP_groupEnd ?_ _; exact .inl rfl)

theorem keepP_teElected (d : D) (t : Fin 7) (i : Fin 3) : KeepP d (teElected d t i) := by
  fin_cases i <;> simp only [teElected] <;> first | exact .inl rfl | (split <;> exact .inl rfl)

theorem keepP_dwNext (d : D) (k : Fin 3) : KeepP d (dwNext w d k) := by
  fin_cases k <;> simp only [dwNext] <;>
    first | exact .inl rfl | (apply keepP_ite <;> exact .inl rfl)

theorem keepP_pkStart (d : D) (per : Per) (b : Bool) : KeepP d (pkStart L g d per b) := by
  unfold pkStart; repeat' split
  all_goals exact .inl rfl

theorem keepP_word32 {v : Value} {f : BitVec 64 → D} {d d' : D} (hf : ∀ x, KeepP d (f x))
    (h : word32 v f = some (some d')) : KeepP d d' := by
  unfold word32 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hf _
  · simp at h

/-- A successor that keeps the page word: a state with the same words, or one of the
machine's composite successors. -/
syntax "kp_leaf" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| kp_leaf) => `(tactic| first
      | exact .inl rfl
      | (refine keepP_passStart ?_ _; exact .inl rfl)
      | exact keepP_afterArrive _ _ _
      | exact keepP_afterTotal _ _ _
      | (refine keepP_groupEnd ?_ _; exact .inl rfl)
      | exact keepP_pkStart _ _ _
      | (refine keepP_pgEnter ?_ _ _; exact .inl rfl)
      | exact keepP_teElected _ _ _
      | exact keepP_teNext _ _ _
      | exact keepP_dwNext _ _
      | (apply keepP_ite <;> kp_leaf)
      | (split <;> kp_leaf))

/-- The successor of an event that returns a value. -/
syntax "kp_kind" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| kp_kind) => `(tactic| first
      | (simp only [Option.some.injEq] at hn; subst hn; kp_leaf)
      | exact keepP_word32 (fun _ => by kp_leaf) hn
      | (obtain ⟨d1, hd1, h1⟩ := Option.map_eq_some_iff.mp hn
         simp only [Option.some.injEq] at h1
         subst h1
         exact keepP_afterTiles hd1)
      | (split at hn <;> kp_kind)
      | (simp at hn; done))

set_option maxHeartbeats 4000000 in
/-- **A step keeps the page word, zeroes it, or records a page-table load's word.** -/
theorem succ_pw {d d' : D} {e : Event} (hs : ∀ per it, d.site ≠ .pgLd per it)
    (hn : succ p L g w d e = some (some d')) : KeepP d d' := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case pgLd per it => exact (hs per it rfl).elim
  all_goals simp only [succ] at hn
  all_goals kp_kind

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
